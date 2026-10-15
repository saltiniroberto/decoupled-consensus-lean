import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bK_GradeLate
import Proofs.Claims.Restated.Claim13bPhaseSleepiness
import Proofs.Claims.Restated.Claim13bStepAssembly
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13bStepRoots
import Proofs.Claims.Restated.Claim13bStepSG
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Alignment
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bK_GradeOld
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_GradeOld
import Proofs.Claims.Restated.Claim13bK_GradeLateRecv
import Proofs.Claims.Restated.Claim13bW_ReceiptRule

/-!
# The grade-1 condition at the next round

The instant bounds and the hypotheses that the grade theorems at round `r + 1` take, each derived
for the members of `freshAttestersW` and `HonRound`, and `gradeOld_of_premises`, which assembles
them, stated over a model `M : Record.Model V`.
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

/-- A round's action instant is at or before the next round's: `S.a r ≤ S.a (r + 1)`. -/
theorem action_le_action_succ (facts : Record.Facts M) (S : Setup V) (r : Round) : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := by
  rw [facts.gr.action_succ_eq_add_rounds]
  have hd := S.E.Δ_pos
  have hR : (0 : Int) ≤ (S.hc.R : Int) := Int.natCast_nonneg _
  have : (0 : Int) ≤ 4 * (S.hc.R : Int) * S.E.Δ := by positivity
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `m` is the last step strictly before the domain instant of round `r + 1`'s phase `p`, the
    instant of step `m` is strictly before that domain instant. -/
theorem time_lt_domain_of_stepBefore (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x) {r : Round} {m : Nat}
    {p : Protocol.Phase}
    (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p)) :
    (x[m].time : Int) < M.domain S.E S.hc (r + 1) p := by
  have hpos : 0 < (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ := by
    linarith only [Restated.action_pos facts S r, S.E.Δ_pos]
  obtain ⟨k_1, hk_1⟩ := Restated.exists_tickStepAt facts x htd hpos
  obtain ⟨hk_1succ, -⟩ := Restated.tickStepAt_time facts x hk_1
  have hk_1m : k_1 < m := by
    by_contra hcon
    have h := hm.2 k_1 (Nat.le_of_not_lt hcon)
    rw [hk_1succ] at h
    exact absurd h (not_le_of_gt (Restated.action_delta_lt_domain_succ facts S r p))
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  exact hm.1 m' (Nat.lt_succ_self m')

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `m` is the last step strictly before the domain instant of round `r + 1`'s phase `p`, and
    that domain instant is at or before `S.a (r + 1)`, the instant of step `m` is at or before
    `S.a (r + 1)`. -/
theorem time_le_action_succ_of_stepBefore (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x) {r : Round} {m : Nat}
    {p : Protocol.Phase} (hdom : M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)))
    (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p)) :
    (x[m].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
  le_of_lt (lt_of_lt_of_le (Restated.time_lt_domain_of_stepBefore facts S Sched x htd hm) hdom)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- At the last step `m` before a round-`(r + 1)` phase instant, every member of
    `freshAttestersW S Sched x r m` is in `HonRound S Sched r`. -/
theorem hfreshH_of_stepBefore (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x) {r : Round} {m : Nat}
    {p : Protocol.Phase} (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p)) :
    Restated.freshAttestersW M S Sched x r m ⊆ Restated.HonRound M S Sched r :=
  Restated.freshAttestersW_subset_honRound facts S Sched x (Restated.action_le_time_of_stepBefore facts S Sched x htd hm)

end


section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If the adversary never releases a validator it holds, a member of `HonRound S Sched (r + 1)` is
    not held by the adversary at `S.a r`. -/
theorem hwh_of_honRound_succ (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (hmono : Sched.MonotoneCorruption) {r : Round} {v : V}
    (hv : v ∈ Restated.HonRound M S Sched (r + 1)) : v ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r)) := fun hmem =>
  (Finset.mem_sdiff.1 hv).2 (hmono _ _ (Restated.action_le_action_succ facts S r) hmem)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- An instant at or before `S.a (r + 1)` lies in a slot whose round is at most `r + η_SG`. -/
theorem hexp_of_domain (facts : Record.Facts M) (S : Setup V) {r : Round} {t : Int} (ht : t ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) :
    (M.round_of S.hc (S.E.slotOf t)) ≤ r + S.hc.η_SG := by
  have h := facts.gr.round_of_mono_sts S.hc (slotOf_mono_sts S ht)
  rw [Restated.round_of_slotOf_action facts] at h
  exact le_trans h (Nat.add_le_add_left S.hc.η_SG_ge_one r)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `a` is an attestation `v_1`'s round-`r` action can compute from its node state at step `n`,
    and `a` names the root `root`, then some body `v_1` holds after step `n + 1` has that root. -/
theorem hhead_mem_of_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (n : Nat) (r : Round) (v_1 : V)
    (a : NamedAttestation V)
    (ha : a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r)
    (root : BlockId) (hconf : a.confirmed = some root) :
    ∃ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies ∧ C.root = root := by
  obtain ⟨n_1, hn_1, ns, rec, hD⟩ := ha
  obtain ⟨g, hg⟩ := facts.gr.read_nonempty (M.gradeContract n_1.cache) S.E S.hc
    (M.toHealing n_1.st.core) r
  rw [facts.nd.gradeContract_read] at hg
  have hroot : root = (M.currentSGVote (M.toHealing n_1.st.core) g).root :=
    (Option.some_inj.mp ((Restated.attest_confirmed_eq_sgVote facts S (x[n][v_1].st) v_1 r n_1 hn_1
      (ns, rec, a) hD g hg).symm.trans hconf)).symm
  have hmem := Restated.actionSGVote_mem_tree facts S (x[n][v_1].st) r
    (Restated.nodeInvariant_sts facts S Sched x n v_1).1 n_1 hn_1 g hg
  have hT : (x[n][v_1].st).st.core.T = (x[n][v_1].st).st.bodies.image NamedBlock.erase :=
    (Restated.nodeInvariant_sts facts S Sched x n v_1).1.1.1.1
  rw [hT, Finset.mem_image] at hmem
  obtain ⟨D, hD, hDe⟩ := hmem
  have hDn1 : D ∈ (x[n + 1][v_1].st).st.bodies := by
    have h := Restated.processed_mono facts S Sched x v_1 (NamedObject.block D) (Nat.le_succ n)
      (by simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hD)
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using h
  refine ⟨D, hDn1, ?_⟩
  rw [hroot, ← hDe, Proofs.NamedWire.erase_root]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If step `n` is the tick step at `S.a r` and the adversary has held `v_1` at no instant up to
    step `k`, then for every attestation `a` that `v_1`'s round-`r` action can compute at step `n`,
    `v_0`'s store after `k` steps does not hold two round-`r` heads under `v_1`'s name. -/
theorem hroom_of_fresh (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {r : Round} {n : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r))) {k : Nat} {v_0 v_1 : V}
    (hv_1 : Restated.HonestThrough M Sched x k v_1) (a : NamedAttestation V)
    (ha : a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r) :
    (M.round_votes (x[k][v_0].st).st.core a.erase).card ≠ 2 := by
  have ha_round : a.erase.round = r := by
    rw [namedAttestation_erase_round]
    exact Restated.actionAttestationFrom_round facts (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r a ha
  have ha_idx : a.erase.val_index = v_1 := by
    rw [namedAttestation_erase_val_index]
    exact Restated.actionAttestationFrom_val_index facts (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r a ha
  have hsub : M.round_votes (x[k][v_0].st).st.core a.erase ⊆ {a.erase.confirmed} := by
    intro o ho
    obtain ⟨c, hcpool, hcidx, hco⟩ := (Restated.Vocabulary.Proofs.Optimistic.mem_round_votes facts).mp ho
    rw [ha_round] at hcpool
    rw [ha_idx] at hcidx
    have hu : M.sgVote c ∈ (M.gradeView (M.toHealing (x[k][v_0].st).st.core)).sg_votes r := by
      rw [facts.gr.gradeView_sg_votes]
      exact Finset.mem_image_of_mem M.sgVote hcpool
    have hur : (M.sgVote c).round = r :=
      Restated.sgVotesRoundIndexed_sts facts S Sched x k v_0 r _ hu
    have hu' : M.sgVote c
        ∈ (M.gradeView (M.toHealing (x[k][v_0].st).st.core)).sg_votes (M.sgVote c).round := by
      rw [hur]; exact hu
    have hcidx' : (M.sgVote c).val_index = v_1 := by
      rw [facts.sto.sgVote_val_index_eq_val_index]; exact hcidx
    obtain ⟨n', htick', -, hueq⟩ :=
      Restated.token_of_honest_sender facts S Sched x hexec hv_1 hu' hcidx'
    rw [hur] at htick' hueq
    have hnn : n' = n := Restated.tickStepAt_unique facts x htick' hn
    rw [hnn] at hueq
    have hc : c.confirmed = a.erase.confirmed := by
      have h := congrArg Protocol.SGVote.confirmed (hueq a ha)
      rw [facts.sto.sgVote_confirmed_eq, facts.sto.sgVote_confirmed_eq] at h
      exact h
    rw [← hco, hc]
    exact Finset.mem_singleton_self _
  intro h2
  have hle := Finset.card_le_card hsub
  rw [h2, Finset.card_singleton] at hle
  omega

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `roundSleepinessW` holds from an anchor at or before the opening of round `r + 1`, and `m` is
    the last step before a round-`(r + 1)` phase instant at or before `S.a (r + 1)`, then for every
    choice `raw` of one outcome of `v_0`'s round-`(r + 1)` late raw view per validator, the
    validators with a nonempty `raw`, other than the members of `freshAttestersW S Sched x r m`,
    weigh less than those members. -/
theorem hhalf_of_roundSleepinessW (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (htd : Restated.TimeDiverges M x) (hmono : Sched.MonotoneCorruption) {anchor : Int}
    (hrs : Restated.roundSleepinessW M S Sched anchor) {r : Round}
    (hanchor : anchor ≤ M.opening S.E S.hc (r + 1)) (hη : S.hc.η_SG ≤ r)
    {m : Nat} {v_0 : V} {p : Protocol.Phase}
    (hdom : M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)))
    (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p))
    (raw : V → Finset (Protocol.Token (Option BlockId)))
    (hraw : ∀ u, M.rawView (M.gradeView (M.toHealing (x[m][v_0].st).st.core)) S.hc.η_SG (r + 1)
      (M.late S.E S.hc (r + 1) p) u ⇢ raw u) :
    S.E.electorate.weightOf
        ((Finset.univ.filter (fun v_1 => (raw v_1).Nonempty))
          \ Restated.freshAttestersW M S Sched x r m)
      < S.E.electorate.weightOf (Restated.freshAttestersW M S Sched x r m) := by
  classical
  have hbound := hrs (r + 1) (Nat.succ_pos r) hanchor
  have hr1 : r + 1 - 1 = r := Nat.add_sub_cancel r 1
  rw [hr1] at hbound
  have hnext : Restated.Vocabulary.Execution.Setup.a M S (r + 1) ≤ M.opening S.E S.hc (r + 1 + 1) := by
    have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self (r + 1))
    have h2 := facts.gr.early_g2_le_opening S (r + 1 + 1)
    have hd := S.E.Δ_pos
    show M.a S.hc S.E.Δ _ ≤ _
    linarith
  have htm : (x[m].time : Int) ≤ M.opening S.E S.hc (r + 1 + 1) :=
    le_trans (Restated.time_le_action_succ_of_stepBefore facts S Sched x htd hdom hm) hnext
  have hhon : ∀ v : V, v ∉ Sched.adv (M.opening S.E S.hc (r + 1 + 1)) →
      Restated.HonestThrough M Sched x m v := fun v hv t ht hmem =>
    hv (hmono _ _ (le_trans ht htm) hmem)
  have hfresh' : Restated.activeRoundW M S Sched r \ Sched.adv (M.opening S.E S.hc (r + 1 + 1))
      ⊆ Restated.freshAttestersW M S Sched x r m := by
    intro v hv
    obtain ⟨hact, hadv⟩ := Finset.mem_sdiff.1 hv
    exact (Restated.mem_freshAttestersW facts).mpr
      ⟨Restated.activeRoundW_subset_attestersAt facts S Sched r hact, hhon v hadv⟩
  have hcover : (Finset.univ.filter (fun v_1 => (raw v_1).Nonempty))
          \ Restated.freshAttestersW M S Sched x r m
      ⊆ Sched.adv (M.opening S.E S.hc (r + 1 + 1)) ∪
          (Restated.attestersIn M S Sched (r + 1 - S.hc.η_SG) r \
            (Restated.activeRoundW M S Sched r \ Sched.adv (M.opening S.E S.hc (r + 1 + 1)))) := by
    intro v hv
    obtain ⟨hvhold, hvfresh⟩ := Finset.mem_sdiff.1 hv
    by_cases hadv : v ∈ Sched.adv (M.opening S.E S.hc (r + 1 + 1))
    · exact Finset.mem_union_left _ hadv
    refine Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨?_, fun h => hvfresh (hfresh' h)⟩)
    obtain ⟨tok, htok⟩ := (Finset.mem_filter.1 hvhold).2
    obtain ⟨Y, hY⟩ := facts.gr.rawInputs_nonempty
      (M.gradeView (M.toHealing (x[m][v_0].st).st.core)) S.hc.η_SG (r + 1)
      (M.late S.E S.hc (r + 1) p) v
    obtain ⟨u, hu, -⟩ := (facts.gr.mem_rawView_iff _ _ _ _ _ _ _ (hraw v) Y hY).mp htok
    obtain ⟨⟨k, hkw, huk⟩, huidx, -⟩ := facts.gr.rawInputs_mem_window _ _ _ _ _ Y hY hu
    have hukround : u.round = k :=
      Restated.sgVotesRoundIndexed_sts facts S Sched x m v_0 k u huk
    have hu' : u ∈ (M.gradeView (M.toHealing (x[m][v_0].st).st.core)).sg_votes u.round := by
      rw [hukround]; exact huk
    have hlo : r + 1 - S.hc.η_SG ≤ k := facts.fc.mem_latest_window_ge hkw
    have hk1 : 1 ≤ k :=
      le_trans (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact Nat.succ_le_succ hη)) hlo
    have hawk := Restated.sender_mem_attestersAt_of_sgVote facts S Sched x hexec (hhon v hadv) hu' huidx
      (by rw [hukround]; exact Restated.early_g2_sub_delta_nonneg_rr facts S hk1)
    rw [hukround] at hawk
    have hhi : k < r + 1 := facts.fc.mem_latest_window_lt hkw
    simp only [Restated.attestersIn, Finset.mem_biUnion, Finset.mem_Icc]
    exact ⟨k, ⟨hlo, Nat.le_of_lt_succ hhi⟩, hawk⟩
  have h_1 := S.E.electorate.weightOf_mono hcover
  have h_2 := S.E.electorate.weightOf_mono hfresh'
  omega

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `r` is at or after the switch round, the invariant holds at round `r` with tick step `n` and
    anchor `T`, `FreshSGHeadsAtLate` holds, the ticks at step `n` of the members of
    `HonRound S Sched r` have an outcome, and `NextRoundReceipts` holds at round `r` (every member
    of `HonRound S Sched (r + 1)` receives round `r`'s honest attestations before round `r + 1`'s
    grade-2 first cutoff), then every block a member
    of `HonRound S Sched (r + 1)` can grade at least 1 for round `r + 1`, at a phase whose domain
    instant is at or before `S.a (r + 1)`, is compatible with `T`. -/
theorem gradeOld_of_premises (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hheadsP : Restated.FreshSGHeadsAtLate M S Sched x r n)
    (hrecvR : Restated.NextRoundReceipts M S Sched x r)
    (hneAtt : ∀ v ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    ∀ v ∈ Restated.HonRound M S Sched (r + 1),
    ∀ p : Protocol.Phase, M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) →
    ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p) →
    ∀ B : Block V,
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
          (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
          (M.late S.E S.hc (r + 1) p) B ⇢ true →
      Block.compatible B T.erase = true := by
  intro v hv p hdom m hm B hgrade
  have hn := hinv.tick
  have hopen : M.opening S.E S.hc r ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
    show _ ≤ M.a S.hc S.E.Δ r
    rw [facts.gr.opening_eq_proposal_time, facts.sch.a_eq_confirmation_time]
    exact facts.sch.proposal_time_le_confirmation_time _ _
  have hgstr : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r) :=
    le_trans (Restated.gst_le_switchOpening facts S tGAT tE gap hgst hlen)
      (le_trans (Restated.switchOpening_le_opening facts S hr) hopen)
  have htm := Restated.time_le_action_succ_of_stepBefore facts S Sched x htd hdom hm
  have hrs := Restated.roundSleepinessW_switchOpening_of_phase facts S Sched tGAT tE gap hgst hlen hmono hthird
    hphase hrsW
  exact Restated.grade1_of_sg_prevLate_recv facts S Sched x hexec htd hn hgstr (Restated.HonRound M S Sched r) hinv.sg hm
    (Restated.hfreshH_of_stepBefore facts S Sched x htd hm)
    (hrecvR.at facts hv p)
    (fun t ht hin => (Finset.mem_sdiff.1 hv).2 (hmono t _ (le_trans ht htm) hin))
    (Restated.hexp_of_domain facts S htm)
    (fun k hk v_1 hv_1 a ha _ => Restated.hroom_of_fresh facts S Sched x hexec hn
      (fun t ht => Restated.honestThrough_of_mem_freshAttestersW facts hv_1 t
        (le_trans ht (Restated.time_mono_int facts S Sched x (le_of_lt hk)))) a ha)
    (fun v_1 hv_1 a ha C hC hconf => hheadsP v hv p hdom m hm v_1 hv_1 C hC a ha hconf)
    (fun v_1 _ a ha root hconf => Restated.hhead_mem_of_tick facts S Sched x n r v_1 a ha root hconf)
    (Restated.hhalf_of_roundSleepinessW facts S Sched x hexec htd hmono hrs
      (Restated.switchOpening_le_opening facts S (le_trans hr (Nat.le_succ r)))
      (Restated.eta_le_of_switchRound_le facts S tGAT tE gap hgst hlen hr) hdom hm)
    B hgrade (facts.ndRun.tick_outcome_sts S Sched x hexec.idealization.root_injective hexec.honestRootsNew)
    (fun v_1 hv_1 => hneAtt v_1 (Restated.hfreshH_of_stepBefore facts S Sched x htd hm hv_1))

end

end DecoupledConsensusModel.Sts.Restated
