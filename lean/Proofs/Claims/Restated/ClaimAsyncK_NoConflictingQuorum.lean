import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariantActiveSince
import Proofs.Claims.Restated.Claim13bK_FgJustified
import Proofs.Claims.Restated.Claim13bStepAnchor
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepSGMove
import Proofs.Claims.Restated.Claim13beRoute3_82
import Proofs.Claims.Restated.ClaimAsyncK_Defs
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_JustificationBound
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Model.Conditions.ClaimAsyncK_Defs
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_ClaimStableThroughAsyncPeriod
import Model.Conditions.Vocabulary_Internal_StoreFinality
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.ClaimAsyncK_NoConflictingQuorum

/-!
# No quorum conflicts with `P` after the hand-over

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M`: under
`VotesClassified` and the long-term condition, quorums of height votes, honest finalized and
justified blocks, and honest chain states all stay compatible with `P`, so `P` is in every honest
filtered tree or an ancestor of its fork-choice root.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If every member of a quorum `Q` has an attestation, included in a block `w`'s store holds after
    `k` steps, whose height pair is a vote for height `h` bound to `root`, then every block on the
    wire whose root is `root` is an ancestor or a descendant of `P`, or `h` is less than the
    justified height of every validator honest through `n₁ + 1`, in its store after that step. -/
theorem classified_of_quorum (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) {r : Nat} {P : Block V} {n₁ k : Nat}
    (hvc : Restated.VotesClassified M S Sched x r P n₁ k)
    (hlt : Restated.longTermConditionUpToW M S Sched r (x[k].time : Int))
    {w : V} {Q : Finset V} (hQ : S.E.electorate.IsQuorum Q) {h : Height} {root : BlockId}
    (hsign : ∀ signer ∈ Q, ∃ (carrier : NamedBlock V) (a : NamedAttestation V) (tmo : Bool),
      carrier ∈ (x[k][w].st).st.bodies ∧ a ∈ carrier.attestations ∧ a.val_index = signer ∧
      a.height_pair = NamedHeightPair.vote h root tmo) :
    (∀ C : NamedBlock V, Restated.blockInLog M S Sched x C → C.root = root → Block.Compatible P C.erase) ∨
      ∀ w' : V, Restated.HonestThrough M Sched x (n₁ + 1) w' → h < (x[n₁ + 1][w'].st).st.core.h_j := by
  obtain ⟨v', hv'Q, hv'out, hv'adv⟩ := Restated.exists_good_of_quorum facts S Sched r _ hlt
    ((isQuorum_iff_q_le S.E Q).mp hQ)
  have hv'k : Restated.HonestThrough M Sched x k v' := fun t ht hmem => hv'adv (hmono t _ ht hmem)
  obtain ⟨carrier, a, tmo, hc, ha, hval, hpair⟩ := hsign v' hv'Q
  have hsent : (⟨v', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[k].sent := by
    have hs := Restated.carried_vote_in_log facts S Sched x hexec hc ha (by rw [hval]; exact hv'k)
    rw [hval] at hs
    exact hs
  rcases hvc v' a h root tmo hv'k hval hsent hpair with h1 | h2 | h3
  · exact Or.inl h1
  · exact Or.inr h2
  · exact absurd h3 hv'out

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `VotesClassified S Sched x r P n₁ k` and `longTermConditionUpToW S Sched r (x[k].time)`,
    with `n₁ + 1 ≤ k`, every validator honest through `k` holds after `k` steps a finalized block
    and a justified block that are each an ancestor or a descendant of `P`. -/
theorem honest_roots_of_classified (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) {r : Nat} {P : Block V} {n₁ k : Nat}
    (hvc : Restated.VotesClassified M S Sched x r P n₁ k)
    (hlt : Restated.longTermConditionUpToW M S Sched r (x[k].time : Int))
    (hk : n₁ + 1 ≤ k) {w : V} (hw : Restated.HonestThrough M Sched x k w) :
    Block.Compatible P (x[k][w].st).st.core.F ∧ Block.Compatible P (x[k][w].st).st.core.J := by
  classical
  have hJ : Block.Compatible P (x[k][w].st).st.core.J := by
    rcases Restated.justified_certificate_sts facts S Sched x hexec hw with
      hgen | ⟨Jn, hJnmem, hJne, -, Q, hQ, hsign⟩
    · rw [hgen]
      exact compatible_genesis_right P
    · rcases Restated.classified_of_quorum facts S Sched x hexec hmono hvc hlt (w := w) hQ
          (h := (x[k][w].st).st.core.h_j) (root := Jn.root)
          (fun signer hs => by
            obtain ⟨carrier, a, hc, ha, hval, hpair⟩ := hsign signer hs
            exact ⟨carrier, a, false, hc, ha, hval, hpair⟩) with
        h1 | h2
      · rw [← hJne]
        exact h1 Jn (Restated.blockInLog_of_mem_bodies facts S Sched hw hJnmem) rfl
      · exfalso
        have hwn : Restated.HonestThrough M Sched x (n₁ + 1) w := fun t ht =>
          hw t (le_trans ht (Restated.time_mono_int facts S Sched x hk))
        have h3 := h2 w hwn
        have h4 := Restated.h_j_mono_sts facts S Sched x w hk
        exact lt_irrefl _ (lt_of_lt_of_le h3 h4)
  exact ⟨compatible_of_preceq_of_compatible (Restated.finalized_preceq_justified_sts facts S Sched x k w) hJ, hJ⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `VotesClassified S Sched x r P n₁ k` and `longTermConditionUpToW S Sched r (x[k].time)`,
    for every block `D` that a validator `w` honest through `k` holds after `k` steps and that is
    neither an ancestor nor a descendant of `P`, and every named block `Pn` on the wire erasing to
    `P`: the height of `D`'s chain state is at most that of `Pn`'s chain state plus one, or at most
    the justified height of every validator honest through `n₁ + 1`, after that step. -/
theorem conflicting_height_le (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) {r : Nat} {P : Block V} {n₁ k : Nat}
    (hvc : Restated.VotesClassified M S Sched x r P n₁ k)
    (hlt : Restated.longTermConditionUpToW M S Sched r (x[k].time : Int))
    {w : V} (hw : Restated.HonestThrough M Sched x k w)
    {D : NamedBlock V} (hD : D ∈ (x[k][w].st).st.bodies)
    {Pn : NamedBlock V} (hPn : Restated.blockInLog M S Sched x Pn) (hPe : Pn.erase = P)
    (hconf : ¬ Block.Compatible P D.erase) :
    (M.derive_named S.E S.cfg D).h ≤ (M.derive_named S.E S.cfg Pn).h + 1 ∨
      ∀ w' : V, Restated.HonestThrough M Sched x (n₁ + 1) w' →
        (M.derive_named S.E S.cfg D).h ≤ (x[n₁ + 1][w'].st).st.core.h_j := by
  classical
  by_cases hle : (M.derive_named S.E S.cfg D).h ≤ (M.derive_named S.E S.cfg Pn).h + 1
  · exact Or.inl hle
  right
  have hcl : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M (x[k][w].st).st :=
    (Restated.nodeInvariant_sts facts S Sched x k w).1.1.1.2.2.1
  have hpos : 1 ≤ (M.derive_named S.E S.cfg D).h - 1 := by unfold Height at *; omega
  have hlt' : (M.derive_named S.E S.cfg D).h - 1 < (M.derive_named S.E S.cfg D).h := by
    unfold Height at *
    omega
  obtain ⟨X, hXD, hXh, Q, hQ, hsign⟩ :=
    facts.cs.height_crossing S.E S.cfg D _ hpos hlt'
  have hXmem : X ∈ (x[k][w].st).st.bodies := Restated.mem_bodies_of_preceq hcl hD hXD
  have hXlog : Restated.blockInLog M S Sched x X := Restated.blockInLog_of_mem_bodies facts S Sched hw hXmem
  rcases Restated.classified_of_quorum facts S Sched x hexec hmono hvc hlt (w := w) hQ
      (h := (M.derive_named S.E S.cfg D).h - 1) (root := X.root)
      (fun signer hs => by
        obtain ⟨carrier, a, hcD, ha, hval, hm⟩ := hsign signer hs
        obtain ⟨tmo, htmo⟩ := vote_of_matchesEntry hm
        exact ⟨carrier, a, tmo, Restated.mem_bodies_of_preceq hcl hD hcD, ha, hval, htmo⟩) with
    h1 | h2
  · exfalso
    have hXc : Block.Compatible P X.erase := h1 X hXlog rfl
    have hXDe : Block.Preceq X.erase D.erase := Proofs.NamedWire.erase_preceq hXD
    rcases compatible_cases (compatible_iff_Compatible.mp hXc) with hPX | hXP
    · exact hconf (compatible_iff_Compatible.mpr
        (compatible_of_cases (Or.inl (preceq_trans_Preceq hPX hXDe))))
    · have hXPn : NamedBlock.Preceq X Pn :=
        Restated.namedPreceq_of_blockInLog facts S Sched x hexec.idealization hXlog hPn (by rw [hPe]; exact hXP)
      have hh := facts.cs.derive_height_mono S.E S.cfg hXPn
      unfold Height at *
      omega
  · intro w' hw'
    have hh := h2 w' hw'
    unfold Height at *
    omega

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every validator `v` and step `i`, the justified height of `v`'s store after `i` steps is
    less than its running maximum height `h_max`. -/
theorem h_j_lt_h_max_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (i : Nat) (v : V) : (x[i][v].st).st.core.h_j < (x[i][v].st).st.core.h_max := by
  obtain ⟨w, hw, hwv⟩ := Record.stateBeforeOf_runOfM M S Sched x facts.nd.wake_events_or_id v i
  have h := Restated.Vocabulary.Proofs.NamedJustificationBound.justificationBelowMax_stateBefore facts
    (Setup.alwaysAwake S) (Record.runOfM M S Sched x v i) (Record.veventsOf M S Sched x v i).length v
    w hw
  rw [hwv] at h
  exact h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every validator `v` and step `i`, `v`'s store after `i` steps holds a named block `D` whose
    chain-state height is the store's running maximum height `h_max`. -/
theorem h_max_carrier_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (i : Nat) (v : V) :
    ∃ D ∈ (x[i][v].st).st.bodies,
      (M.derive_named S.E S.cfg D).h = (x[i][v].st).st.core.h_max := by
  obtain ⟨w, hw, hwv⟩ := Record.stateBeforeOf_runOfM M S Sched x facts.nd.wake_events_or_id v i
  have h := Restated.Vocabulary.Proofs.NamedStoreBridge.maximum_carrier_stateBefore facts
    (Setup.alwaysAwake S) (Record.runOfM M S Sched x v i) (Record.veventsOf M S Sched x v i).length v
    w hw
  rw [hwv] at h
  exact h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `VotesClassified S Sched x r P n₁ k` and `longTermConditionUpToW S Sched r (x[k].time)`,
    with `n₁ + 1 ≤ k`, if a validator `w` honest through `k` holds after `k` steps a named block
    `Pn` erasing to `P`, then its store's tree has a block `W` that is `P` or a descendant of `P`,
    whose recorded chain-state height is at least the store's `h_max` minus one. -/
theorem viable_witness_of_classified (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) {r : Nat} {P : Block V} {n₁ k : Nat}
    (hvc : Restated.VotesClassified M S Sched x r P n₁ k)
    (hlt : Restated.longTermConditionUpToW M S Sched r (x[k].time : Int))
    (hk : n₁ + 1 ≤ k) {w : V} (hw : Restated.HonestThrough M Sched x k w)
    {Pn : NamedBlock V} (hPn : Pn ∈ (x[k][w].st).st.bodies) (hPe : Pn.erase = P) :
    ∃ W ∈ (x[k][w].st).st.core.T, Block.Preceq P W ∧
      (x[k][w].st).st.core.h_max - 1 ≤ ((x[k][w].st).st.core.σ W).h := by
  classical
  have hco := (Restated.nodeInvariant_sts facts S Sched x k w).1.1.1
  have hT : ∀ B ∈ (x[k][w].st).st.bodies, B.erase ∈ (x[k][w].st).st.core.T := by
    intro B hB
    rw [hco.1]
    exact Finset.mem_image_of_mem _ hB
  have hσ : ∀ B ∈ (x[k][w].st).st.bodies,
      (x[k][w].st).st.core.σ B.erase = M.derive_named S.E S.cfg B :=
    fun B hB => hco.2.2.2.2 B hB
  have hPlog : Restated.blockInLog M S Sched x Pn := Restated.blockInLog_of_mem_bodies facts S Sched hw hPn
  have hPwit : (x[k][w].st).st.core.h_max - 1 ≤ (M.derive_named S.E S.cfg Pn).h →
      ∃ W ∈ (x[k][w].st).st.core.T, Block.Preceq P W ∧
        (x[k][w].st).st.core.h_max - 1 ≤ ((x[k][w].st).st.core.σ W).h := by
    intro hh
    refine ⟨Pn.erase, hT Pn hPn, ?_, ?_⟩
    · rw [hPe]; exact preceq_eq_true_iff_Preceq.mp (Block.preceq_self P)
    · rw [hσ Pn hPn]; exact hh
  obtain ⟨D₀, hD₀, hD₀h⟩ := Restated.h_max_carrier_sts facts S Sched x k w
  by_cases hc : Block.Compatible P D₀.erase
  · rcases compatible_cases (compatible_iff_Compatible.mp hc) with hPD | hDP
    · refine ⟨D₀.erase, hT D₀ hD₀, hPD, ?_⟩
      rw [hσ D₀ hD₀, hD₀h]
      unfold Height at *
      omega
    · apply hPwit
      have hn : NamedBlock.Preceq D₀ Pn :=
        Restated.namedPreceq_of_blockInLog facts S Sched x hexec.idealization
          (Restated.blockInLog_of_mem_bodies facts S Sched hw hD₀) hPlog (by rw [hPe]; exact hDP)
      have hh := facts.cs.derive_height_mono S.E S.cfg hn
      unfold Height at *
      omega
  · rcases Restated.conflicting_height_le facts S Sched x hexec hmono hvc hlt hw hD₀ hPlog hPe hc with h1 | h2
    · apply hPwit
      unfold Height at *
      omega
    · exfalso
      have hwn : Restated.HonestThrough M Sched x (n₁ + 1) w := fun t ht =>
        hw t (le_trans ht (Restated.time_mono_int facts S Sched x hk))
      have h3 := h2 w hwn
      have h4 := Restated.h_j_mono_sts facts S Sched x w hk
      have h5 := Restated.h_j_lt_h_max_sts facts S Sched x k w
      rw [hD₀h] at h3
      exact lt_irrefl _ (lt_of_le_of_lt (le_trans h3 h4) h5)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `VotesClassified S Sched x r P n₁ k` and `longTermConditionUpToW S Sched r (x[k].time)`,
    with `n₁ + 1 ≤ k`, if a validator `w` honest through `k` holds after `k` steps a named block
    erasing to `P`, then `P` is in the filtered block tree of `w`'s store after `k` steps, or `P` is
    that store's fork-choice root or an ancestor of it. -/
theorem mem_filtered_or_root_of_classified (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) {r : Nat} {P : Block V} {n₁ k : Nat}
    (hvc : Restated.VotesClassified M S Sched x r P n₁ k)
    (hlt : Restated.longTermConditionUpToW M S Sched r (x[k].time : Int))
    (hk : n₁ + 1 ≤ k) {w : V} (hw : Restated.HonestThrough M Sched x k w)
    {Pn : NamedBlock V} (hPn : Pn ∈ (x[k][w].st).st.bodies) (hPe : Pn.erase = P) :
    P ∈ M.get_filtered_block_tree (M.toHealing (x[k][w].st).st.core).toFG ∨
      Block.Preceq P (M.get_fg_root (M.toHealing (x[k][w].st).st.core).toFG) := by
  classical
  obtain ⟨hF, hJ⟩ := Restated.honest_roots_of_classified facts S Sched x hexec hmono hvc hlt hk hw
  obtain ⟨W, hW, hPW, hh⟩ :=
    Restated.viable_witness_of_classified facts S Sched x hexec hmono hvc hlt hk hw hPn hPe
  have hparts : ∀ {C W : Block V}, C ∈ (x[k][w].st).st.core.T →
      Block.Preceq (x[k][w].st).st.core.F C → W ∈ (x[k][w].st).st.core.T → Block.Preceq C W →
      (x[k][w].st).st.core.h_max - 1 ≤ ((x[k][w].st).st.core.σ W).h →
      Block.Preceq (M.get_fg_root (M.toHealing (x[k][w].st).st.core).toFG) C →
      C ∈ M.get_filtered_block_tree (M.toHealing (x[k][w].st).st.core).toFG := by
    intro C W hC hFC hW hCW hh hroot
    refine facts.fc.mem_get_filtered_block_tree_of_parts (M.toHealing (x[k][w].st).st.core)
      ?_ ?_ ?_ hCW ?_ hroot
    · rw [facts.sto.toHealing_T]; exact hC
    · rw [facts.sto.ModelProperties_toHealing_F]; exact hFC
    · rw [facts.sto.toHealing_T]; exact hW
    · rw [facts.sto.ModelProperties_toHealing_h_max, facts.sto.ModelProperties_toHealing_σ]
      exact hh
  have hco := (Restated.nodeInvariant_sts facts S Sched x k w).1.1.1
  have hPT : P ∈ (x[k][w].st).st.core.T := by
    rw [hco.1, ← hPe]
    exact Finset.mem_image_of_mem _ hPn
  have hFJ := Restated.finalized_preceq_justified_sts facts S Sched x k w
  rcases facts.fc.get_fg_root_eq_J_or_F (x[k][w].st).st.core with hr | hr
  · rcases compatible_cases (compatible_iff_Compatible.mp hJ) with hPJ | hJP
    · right
      rw [hr]
      exact hPJ
    · left
      exact hparts hPT (preceq_trans_Preceq hFJ hJP) hW hPW hh
        (by rw [hr]; exact hJP)
  · rcases compatible_cases (compatible_iff_Compatible.mp hF) with hPF | hFP
    · right
      rw [hr]
      exact hPF
    · left
      exact hparts hPT hFP hW hPW hh (by rw [hr]; exact hFP)

end

end DecoupledConsensusModel.Sts.Restated
