import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActive
import Proofs.Claims.Restated.Claim13bInvariantActiveSince
import Proofs.Claims.Restated.Claim13bK_ConeAnchor
import Proofs.Claims.Restated.Claim13bK_ConeChain
import Proofs.Claims.Restated.Claim13bK_ConeSlots
import Proofs.Claims.Restated.Claim13bK_ConfirmedOld
import Proofs.Claims.Restated.Claim13bK_FgJustified
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bK_Frame
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bK_GradeDescendant
import Proofs.Claims.Restated.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.Claim13bK_HeadsNewAnchor
import Proofs.Claims.Restated.Claim13bK_HolderMargins
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStep
import Proofs.Claims.Restated.Claim13bPhaseSleepiness
import Proofs.Claims.Restated.Claim13bStepActionF
import Proofs.Claims.Restated.Claim13bStepAnchor
import Proofs.Claims.Restated.Claim13bStepAssembly
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepFin
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13bStepQuorum
import Proofs.Claims.Restated.Claim13bStepSGMove
import Proofs.Claims.Restated.Claim13bW_Schedule
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_ConeAnchor
import Model.Conditions.Claim13bK_ConeSlots
import Model.Conditions.Claim13bK_FgJustified
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bK_GradePairwise
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAnchor
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13bStepGrade
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13bStepSG
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Proofs.Claims.Spec2Claims.Claim13bStepSGMove
import Model.Conditions.Claim13beRoute3_5
import Model.Conditions.Claim13beRoute3_7
import Model.Conditions.CommonViewOfFinalizedDescendantsFacts
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring
import Proofs.Claims.Restated.Claim13bK_ConeAnchorRecv
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStepRecv

/-!
# Heads at the new anchor

Theorems showing that every member of `HonSlot` of round `(r + 1)`'s third slot votes for a
descendant of the round-`(r + 1)` anchor, from bounds on the honest finalized and justified blocks
up to `S.a (r + 2)` and from the heads at the second slot, stated over a model `M : Record.Model V`.
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

/-- From any node state `before`, validator `v`'s round-`r` action can compute some attestation. -/
private theorem actionAttestationFrom_nonempty_hj (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (v : V) (r : Round) :
    ∃ a, a ∈ Restated.actionAttestationFrom M S before v r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract (M.mkNode st before.record c).cache)
    S.E S.hc (S.node v) (M.mkNode st before.record c).st (M.mkNode st before.record c).record
  exact ⟨D.2.2, M.mkNode st before.record c, ⟨c, hc, st, hst, rfl⟩, D.1, D.2.1, hD⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If step `n` is the tick step at `S.a r`, no height vote signed up to step `n + 1` by a validator
    honest through it names a height greater than `T`'s, step `n'` is the tick step at
    `S.a (r + 1)`, and `roundSleepinessW` holds from an instant at or before round `r + 1`'s
    opening, then at every step up to `n'` every validator's `h_max` is at most one more than `T`'s
    chain-state height. -/
theorem hMax_le_anchor_succ_before_succ_tick_ofCeiling (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hceil : ∀ (v : V) (n₂ : Nat) (a : NamedAttestation V) (h' : Height)
      (entry : BlockId) (tmo : Bool),
      n₂ ≤ n + 1 → Restated.HonestThrough M Sched x n₂ v → a.val_index = v →
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n₂].sent →
      a.height_pair = NamedHeightPair.vote h' entry tmo →
      h' ≤ (M.derive_named S.E S.cfg T).h)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (htE : tE ≤ M.opening S.E S.hc (r + 1)) :
    ∀ (v : V) (n₁ : Nat), n₁ ≤ n' →
      (x[n₁][v].st).st.core.h_max ≤ (M.derive_named S.E S.cfg T).h + 1 := by
  classical
  intro v n₁ hn₁
  by_cases hsmall : (x[n₁][v].st).st.core.h_max ≤ 1
  · exact le_trans hsmall (Nat.succ_le_succ (Nat.zero_le _))
  obtain ⟨B, hBmem, hBh⟩ := Restated.hMax_attained_sts facts S Sched x n₁ v
  have hpos : 2 ≤ (M.derive_named S.E S.cfg B).h := by
    rw [hBh]; exact Nat.succ_le_of_lt (not_le.mp hsmall)
  obtain ⟨Q, hQ, hsign⟩ := Restated.carried_vote_of_tree_block facts S Sched x hBmem hpos
  obtain ⟨q, hqQ, hqadv⟩ := Restated.exists_nonAdv_of_quorum facts S Sched hrsW (r₀ := r + 1)
    (Nat.le_add_left 1 r) htE ((isQuorum_iff_q_le S.E Q).mp hQ)
  have htime : (x[n₁].time : Int) ≤ M.opening S.E S.hc (r + 1 + 1) := by
    refine le_trans (Restated.time_mono_int facts S Sched x (Nat.le_succ_of_le hn₁)) ?_
    rw [(Restated.tickStepAt_time facts x hn').1]
    have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self (r + 1))
    have h2 := facts.gr.early_g2_le_opening S (r + 1 + 1)
    have hd := S.E.Δ_pos
    show M.a S.hc S.E.Δ _ ≤ _
    linarith
  have hqhon : Restated.HonestThrough M Sched x n₁ q := by
    intro t ht hmem
    exact hqadv (hmono t (M.opening S.E S.hc (r + 1 + 1)) (le_trans ht htime) hmem)
  obtain ⟨carrier, a, entry, tmo, hcmem, hrow, hval, hpair⟩ := hsign q hqQ
  have hlog : (⟨a.val_index, NamedObject.attest a⟩ : SignedMsg V (NamedObject V))
      ∈ x[n₁].sent :=
    Restated.carried_vote_in_log facts S Sched x hexec hcmem hrow (by rw [hval]; exact hqhon)
  have hlog' : (⟨q, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n₁].sent := by
    rw [← hval]; exact hlog
  have hhonT : HonestThroughTime Sched ((x[n₁].time : Int)) q := fun t ht => hqhon t ht
  obtain ⟨-, k, hkn₁, htick, hawk, out, hout, hemit⟩ :=
    Restated.attest_round_of_sent facts S Sched x (tB := (x[n₁].time : Int)) hhonT
      hexec.toUnforgeability hval (le_refl _) hlog'
  have heq : ∀ a' ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[k][q].st) q a.round,
      a = a' := by
    have hA : Restated.actionAttestationFrom M (Setup.alwaysAwake S)
        (Record.wakeStage M Sched ((Restated.Vocabulary.Execution.Setup.a M S a.round)) x[k] q) q
          a.round =
        Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[k][q].st) q a.round := by
      simp only [Restated.actionAttestationFrom,
        Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom, Record.wakeStage_st facts,
        Record.wakeStage_record facts, Record.wakeStage_cache facts]
    rw [← hA]
    have _hr_s1 := Record.reachedNode_wakeStage facts S Sched x (k) q (Restated.Vocabulary.Execution.Setup.a M S a.round)
    have _hv_s2 := Record.runs_as_wakeStage facts S Sched x (k) q (Restated.Vocabulary.Execution.Setup.a M S a.round)
    exact Restated.attest_of_tick_eq facts S q _ a.round hout hemit
  obtain ⟨a₁, ha₁⟩ := actionAttestationFrom_nonempty_hj facts (Setup.alwaysAwake S)
    (x[k][q].st) q a.round
  have hsent : (⟨q, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent := by
    rw [heq a₁ ha₁]
    exact Restated.attest_emitted_at_tick_from facts S Sched x htick hawk ⟨out, hout⟩
      (facts.nd.tick_attestation_fields (Setup.alwaysAwake S) q _ _ (Record.runs_as_wakeStage facts S Sched x _ _ _) out hout a hemit).2.1 a₁ ha₁
  have hqk : Restated.HonestThrough M Sched x (k + 1) q := by
    intro t ht hmem
    exact hqhon t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.succ_le_of_lt hkn₁))) hmem
  have hround : a.round ≤ r :=
    Restated.round_le_of_tick_lt facts S Sched x htick hn' (Nat.lt_of_lt_of_le hkn₁ hn₁)
  have hkn : k ≤ n := Restated.tick_le_of_round_le facts S Sched x htick hn hround
  have hh := hceil q (k + 1) a _ entry tmo (Nat.succ_le_succ hkn) hqk hval hsent hpair
  have hone : 1 ≤ (M.derive_named S.E S.cfg B).h := le_trans (by decide) hpos
  calc (x[n₁][v].st).st.core.h_max
      = (M.derive_named S.E S.cfg B).h := hBh.symm
    _ = ((M.derive_named S.E S.cfg B).h - 1) + 1 := (Nat.sub_add_cancel hone).symm
    _ ≤ (M.derive_named S.E S.cfg T).h + 1 := Nat.succ_le_succ hh

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `n'` and `n''` are the tick steps at `S.a (r + 1)` and `S.a (r + 2)`, `n_W ≤ n'`, every
    finalized block of a validator honest through a step at or before `n'` is an ancestor of `T`,
    `T ⪯ D`, and every justified block of a validator honest through a step from `n_W` to `n'' + 1`
    is an ancestor of `D`, then every finalized block of a validator honest through a step whose
    instant is at most `S.a (r + 2) − 1` is an ancestor of `D`. -/
theorem fin_preceq_before_succ_succ_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {r : Round} {n' n'' n_W : Nat} {T D : Block V}
    (hn'' : Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)))) (hnWn' : n_W ≤ n')
    (hfin : ∀ (v : V) (n₁ : Nat), n₁ ≤ n' → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.F T)
    (hTD : Block.Preceq T D)
    (hJ : ∀ (v : V) (n₁ : Nat), n_W ≤ n₁ → n₁ ≤ n'' + 1 → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J D) :
    ∀ (v : V) (d : Nat), (x[d].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1 → Restated.HonestThrough M Sched x d v →
      Block.Preceq (x[d][v].st).st.core.F D := by
  intro v d hd hvd
  by_cases hdn : d ≤ n'
  · exact preceq_trans_Preceq (hfin v d hdn hvd) hTD
  · have hdn'' : d ≤ n'' := Restated.le_tick_of_time_lt_action facts S Sched x hn'' hd
    exact preceq_trans_Preceq (Restated.finalized_preceq_justified_sts facts S Sched x d v)
      (hJ v d (by omega) (by omega) hvd)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `n''` is the tick step at `S.a (r + 2)`, `n_W ≤ n'`, every block a validator honest through a
    step from `n + 1` to `n'` has justified with `h_max = h_j + 1` is an ancestor of `T`, `T ⪯ D`,
    and every justified block of a validator honest through a step from `n_W` to `n'' + 1` is an
    ancestor of `D`, then every block a validator honest through a step from `n + 1` on, at an
    instant at most `S.a (r + 2) − 1`, has justified with `h_max = h_j + 1` is an ancestor of `D`. -/
theorem just_preceq_before_succ_succ_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {r : Round} {n n' n'' n_W : Nat} {T D : Block V}
    (hn'' : Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)))) (hnWn' : n_W ≤ n')
    (hjust : ∀ (v : V) (n₁ : Nat), n + 1 ≤ n₁ → n₁ ≤ n' → Restated.HonestThrough M Sched x n₁ v →
      (x[n₁][v].st).st.core.h_max = (x[n₁][v].st).st.core.h_j + 1 →
      Block.Preceq (x[n₁][v].st).st.core.J T)
    (hTD : Block.Preceq T D)
    (hJ : ∀ (v : V) (n₁ : Nat), n_W ≤ n₁ → n₁ ≤ n'' + 1 → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J D) :
    ∀ (v : V) (d : Nat), n + 1 ≤ d → (x[d].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1 →
      Restated.HonestThrough M Sched x d v →
      (x[d][v].st).st.core.h_max = (x[d][v].st).st.core.h_j + 1 →
      Block.Preceq (x[d][v].st).st.core.J D := by
  intro v d hnd hd hvd hroot
  by_cases hdn : d ≤ n'
  · exact preceq_trans_Preceq (hjust v d hnd hdn hvd hroot) hTD
  · have hdn'' : d ≤ n'' := Restated.le_tick_of_time_lt_action facts S Sched x hn'' hd
    exact hJ v d (by omega) (by omega) hvd

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If every finalized block of a validator honest through a step whose instant is at most
    `S.a (r + 2) − 1` is an ancestor of `D`, then `DeliveredDescendantUnderFinalizedInPhase` holds
    at `D` from `tGAT` to `S.a (r + 2) − 1`. -/
theorem deliveredDescendant_before_succ_succ_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {r : Round} {D : Block V}
    (hF : ∀ (v : V) (d : Nat), (x[d].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1 →
      Restated.HonestThrough M Sched x d v → Block.Preceq (x[d][v].st).st.core.F D)
    (tGAT : Int) :
    Restated.DeliveredDescendantUnderFinalizedInPhase M S x tGAT ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1) D := by
  intro d v v' B _ hvh _ hhi hDB
  exact (preceq_eq_true_iff_Preceq.mpr (preceq_trans_Preceq (hF v d hhi hvh) hDB))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If every finalized block of a validator honest through a step whose instant is at most
    `S.a (r + 2) − 1` is an ancestor of `D`, then `FinalizedPreceqAtStepsInPhase` holds at `D` from
    `tGAT` to `S.a (r + 2) − 1`. -/
theorem finalizedPreceqAtSteps_before_succ_succ_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {r : Round} {D : Block V}
    (hF : ∀ (v : V) (d : Nat), (x[d].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1 →
      Restated.HonestThrough M Sched x d v → Block.Preceq (x[d][v].st).st.core.F D)
    (tGAT : Int) :
    Restated.FinalizedPreceqAtStepsInPhase M S x tGAT ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1) D :=
  fun d v hvh _ hhi => hF v d hhi hvh

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If step `n` is the tick step at `S.a r`, every finalized block of a validator honest through a
    step whose instant is at most `S.a (r + 2) − 1` is an ancestor of `D`, so is every block such a
    validator has justified with `h_max = h_j + 1` at a step from `n + 1` on, and slot `(s + 1)`'s
    vote instant lies strictly between `S.a r` and `S.a (r + 2)`, then `VoteFinJustCompatible` holds
    at `D` and `s`. -/
theorem voteFinJustCompatible_before_succ_succ_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (hmono : Sched.MonotoneCorruption)
    {r : Round} {n : Nat} {D : Block V} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hF : ∀ (v : V) (d : Nat), (x[d].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1 →
      Restated.HonestThrough M Sched x d v → Block.Preceq (x[d][v].st).st.core.F D)
    (hJ : ∀ (v : V) (d : Nat), n + 1 ≤ d → (x[d].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1 →
      Restated.HonestThrough M Sched x d v →
      (x[d][v].st).st.core.h_max = (x[d][v].st).st.core.h_j + 1 →
      Block.Preceq (x[d][v].st).st.core.J D)
    {s : Slot} (hlo : (Restated.Vocabulary.Execution.Setup.a M S r) < M.vote_time S.E (s + 1))
    (hhi : M.vote_time S.E (s + 1) < (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1))) :
    Restated.VoteFinJustCompatible M S x D s := by
  intro v mr hv hmr
  obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hn
  obtain ⟨-, hmr0⟩ := Restated.tickStepAt_time facts x hmr
  have hlow : n + 1 ≤ mr := by
    by_contra hcon
    have hle : mr ≤ n := by omega
    have h1 := Restated.time_mono_int facts S Sched x hle
    linarith
  have hct : (x[mr].time : Int) ≤ M.confirmation_time S.E (s + 1) := by
    have e : M.confirmation_time S.E (s + 1) = M.vote_time S.E (s + 1) + 5 * S.E.Δ := by
      have e6 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E (s + 1)
      have e1 := facts.sch.slotStart_add_delta_eq_vote_time S.E (s + 1)
      linarith
    have hd := S.E.Δ_pos
    linarith
  have hvh : Restated.HonestThrough M Sched x mr v := Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hv hct
  have hmrt : (x[mr].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1 := by linarith
  exact ⟨compatible_of_preceq_common_Preceq (hF v mr hmrt hvh)
      (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)),
    fun hroot => compatible_of_preceq_common_Preceq (hJ v mr hlow hmrt hvh hroot)
      (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `D` is an ancestor of `X`, and every block that a member of `HonRound S Sched r` names as
    confirmed in its round-`r` attestation, and holds right after the round-`r` tick, is compatible
    with `X`, then every block that a validator awake from `S.a r` to a round-`(r + 1)` phase's
    domain instant at or before `S.a (r + 1)`, and not held there, can grade at least 1 for round
    `r + 1` at the last step before that instant is compatible with `D`. -/
theorem graded_compatible_of_sgCompatible (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    {D X : Block V} (hDX : Block.Preceq D X)
    (hX : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
      a.round = r → a.val_index = v_1 →
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
      Block.compatible C.erase X = true)
    (hrecvR : Restated.NextRoundReceipts M S Sched x r) :
    ∀ v ∈ Restated.grade1PerformersW M S Sched (r + 1),
      ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) .g1) →
      ∀ B : Block V,
        M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
          (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g1)
          (M.late S.E S.hc (r + 1) .g1) B ⇢ true →
        Block.compatible B D = true := by
  intro v hv m hm B hB
  obtain ⟨hawT, hvS⟩ := Finset.mem_sdiff.1 hv
  obtain ⟨v_1, hv_1, a, har, hai, has, C, hC, hac, hBC⟩ :=
    Restated.graded_preceq_freshSG_at_awakeReader_recv facts S Sched x tE hexec hmono htd hsync
      hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross
      (facts.gr.domain_le_action S (r + 1) .g1) _ (Restated.early_g1_sub_delta_le_late_g1_sub_rr facts S (r + 1)) hawT
        (hrecvR.perf hv) hvS hm B hB
  exact compatible_of_preceq_of_preceq hBC hDX (hX v_1 hv_1 a har hai has C hC hac)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If step `n''` is the tick step at `S.a (r + 2)`, `v_1` holds `Dn` among its bodies after `m`
    steps and is honest through `m`, the instant of `m` is at or after `tGAT` and strictly before
    `S.a (r + 1)`, every honest finalized block up to the instant `S.a (r + 2) − 1` is an ancestor
    of `Dn`, and every store's `h_max` up to step `n''` is at most one more than `Dn`'s chain-state
    height, then `ConeAnchorChainInTree` holds at `Dn` for the voters of round `(r + 1)`'s third
    slot. -/
theorem coneAnchorChainInTree_thirdSlot_ofHolder (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} {n'' : Nat} (hn'' : Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1))))
    {Dn : NamedBlock V} {v_1 : V} {m : Nat} (hDv_1 : Dn ∈ (x[m][v_1].st).st.bodies)
    (hv_1 : Restated.HonestThrough M Sched x m v_1) (hm : tGAT ≤ (x[m].time : Int))
    (hmlt : (x[m].time : Int) < (Restated.Vocabulary.Execution.Setup.a M S (r + 1)))
    (hF : ∀ (v : V) (d : Nat), (x[d].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1 →
      Restated.HonestThrough M Sched x d v → Block.Preceq (x[d][v].st).st.core.F Dn.erase)
    (hhmax : ∀ (v : V) (n₁ : Nat), n₁ ≤ n'' →
      (x[n₁][v].st).st.core.h_max ≤ (M.derive_named S.E S.cfg Dn).h + 1)
    (hneTickW : ∀ w ∈ Restated.HonSlot M S Sched ((M.opening_slot S.hc (r + 1)) + 1 + 1),
      ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → w ∈ Sched.awake t' \ Sched.adv t' → t' < M.vote_time S.E ((M.opening_slot S.hc (r + 1)) + 1 + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t' x[n'] w) t' ⇢ out) :
    Restated.ConeAnchorChainInTree M S x Dn.erase ((M.opening_slot S.hc (r + 1)) + 1) := by
  have hd := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hRd : 12 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
  have hsucc := facts.gr.action_succ_eq_add_rounds S (r + 1)
  have hso : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) = slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) + 6 * S.E.Δ := by
    rw [← Restated.confirmation_time_opening_slot facts S (r + 1), facts.sch.slotStart_add_six_delta_eq_confirmation_time]
  have hss1 : slotStart S.E.Δ ((M.opening_slot S.hc (r + 1)) + 1)
      = slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) + 4 * S.E.Δ :=
    slotStart_succ S.E.Δ _
  have hvf : M.view_freeze S.E ((M.opening_slot S.hc (r + 1)) + 1)
      = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) + S.E.Δ :=
    (facts.sch.a_add_delta_eq_view_freeze S (r + 1)).symm
  have hvt : M.vote_time S.E ((M.opening_slot S.hc (r + 1)) + 1 + 1)
      = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 5 * S.E.Δ + 4 * S.E.Δ * ((2 : Nat) : Int) :=
    Restated.vote_time_opening_slot_add facts S (r + 1) 2
  push_cast at hvt
  exact Restated.coneAnchorChainInTree_of_holder_of_bounds facts S Sched x hexec hsync hmult htd hmono
    (tR := (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1) hgst hcv hphase hthird hcs (Restated.delta_le_of_healingLengthη facts S hlen)
    hDv_1 hv_1 hm hF
    (fun v d hd' => hhmax v d (Restated.le_tick_of_time_lt_action facts S Sched x hn'' hd'))
    (by rw [hvf]; linarith) (by rw [hvt]; linarith) hneTickW

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If round `r` is at or after the switch round, the invariant holds at round `r` with anchor `T`, and step `n'` is the tick step at `S.a (r + 1)`, then every
    member of `HonSlot` of the slot after round `(r + 1)`'s opening slot votes there for a
    descendant of `T`. -/
theorem headsBelow_secondSlot_at_anchor (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) :
    Restated.HeadsBelow M S Sched x T.erase ((M.opening_slot S.hc (r + 1)) + 1) := by
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  obtain ⟨t', ht'E, ht's, ht'len, hcs'⟩ :=
    Restated.exists_cone_cutoff facts S Sched tE hmono hcom tGAT gap hgst hlen hphase hcs hr
  have hcs2 := Restated.committeeSleepinessW_at_heads_slot facts S Sched tE hmono hcom tGAT gap hgst hlen hphase
    hcs hr
  have hfin := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts S Sched x tE
    hexec hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hcross hn'
  have hRs : (M.opening_slot S.hc r) + 2 ≤ (M.opening_slot S.hc (r + 1)) := by
    rw [facts.gr.opening_slot_succ]
    exact Nat.add_le_add_left (le_trans (by decide) S.hc.R_ge_three) _
  have hsR : M.support_cutoff S.E ((M.opening_slot S.hc (r + 1))) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1 := by
    have e1 := facts.sch.Sts_support_cutoff_lt_view_freeze S.E ((M.opening_slot S.hc (r + 1)))
    have e2 := facts.sch.view_freeze_lt_confirmation_time S.E ((M.opening_slot S.hc (r + 1)))
    rw [Restated.confirmation_time_opening_slot facts S (r + 1)] at e2
    have e1' := Int.add_one_le_of_lt e1
    have e2' := Int.add_one_le_of_lt e2
    linarith
  have hrange := Restated.headsBelow_range_afterPhase (hr1 := Restated.one_le_round_of_of_opening_slot_le facts S (r := r)
      (le_trans (Restated.one_le_switchRound facts S tGAT tE gap hgst hlen) hr) (Nat.le_add_right _ 2)) facts S Sched x hexec hsync hmult htd hmono hgst hcv
    (fun t h1 h2 => hphase t h1 (le_trans h2 ht'E))
    (fun t h => hthird t (le_trans h ht'E)) hcs' ht'len
    (Restated.deliveredDescendantUnderFinalized_anchor facts S Sched x hn' hfin tGAT)
    (Restated.finalizedPreceqAtSteps_anchor facts S Sched x hn' hfin tGAT)
    (s₀ := (M.opening_slot S.hc r) + 2) (s₁ := (M.opening_slot S.hc (r + 1)))
    (Nat.succ_pos _) ht's hsR
    (fun s h0 h1 => Restated.coneAnchorCompatible_range_at_anchor facts S
      Sched x tE hexec hmono htd hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr
      hinv hcross hjust (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hinv.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨Restated.awake_action_of_mem_honRound facts hv, (Finset.mem_sdiff.1 hv).2⟩)) s h0 h1)
    (fun s h0 h1 => Restated.coneAnchorChainInTree_at_anchor_of_committee facts S Sched x tE
      hexec hmono htd hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hcs2
      (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) s h0 h1)
    hinv.heads (by intro s _ _ m hm q hq; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hm (facts.sch.vote_time_emod_delta S _) (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_HonSlot facts S Sched _ hq, fun h => ((Restated.mem_HonSlot facts).mp hq).2.2 (hmono _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) h)⟩)) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
  exact hrange _ (Nat.le_succ_of_le hRs) le_rfl

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If round `r` is at or after the switch round, every honest finalized block up to the instant
    `S.a (r + 2) − 1` is an ancestor of `Dn`, so is every block an honest validator justifies with
    `h_max = h_j + 1` from the tick step at `S.a r` on up to that instant, every store's `h_max` up
    to the tick step at `S.a (r + 2)` is at most one more than `Dn`'s chain-state height, an honest
    validator holds `Dn` at an instant in `[tGAT, S.a (r + 1))`, every block a validator awake from
    `S.a r` to round `(r + 1)`'s grade-1 domain instant can grade at least 1 for round `r + 1` is
    compatible with `Dn`, and `HeadsBelow` holds for `Dn` at round `(r + 1)`'s second slot, then it
    holds for `Dn` at the third slot. -/
theorem headsBelow_thirdSlot_of_anchorFacts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} {n n'' : Nat} (hr : Restated.switchRound M S tE ≤ r)
    (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r))) (hn'' : Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1))))
    {Dn : NamedBlock V}
    (hF : ∀ (v : V) (d : Nat), (x[d].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1 →
      Restated.HonestThrough M Sched x d v → Block.Preceq (x[d][v].st).st.core.F Dn.erase)
    (hJ : ∀ (v : V) (d : Nat), n + 1 ≤ d → (x[d].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1 →
      Restated.HonestThrough M Sched x d v →
      (x[d][v].st).st.core.h_max = (x[d][v].st).st.core.h_j + 1 →
      Block.Preceq (x[d][v].st).st.core.J Dn.erase)
    (hhmax : ∀ (v : V) (n₁ : Nat), n₁ ≤ n'' →
      (x[n₁][v].st).st.core.h_max ≤ (M.derive_named S.E S.cfg Dn).h + 1)
    {v_1 : V} {m : Nat} (hDv_1 : Dn ∈ (x[m][v_1].st).st.bodies)
    (hv_1 : Restated.HonestThrough M Sched x m v_1) (hm : tGAT ≤ (x[m].time : Int))
    (hmlt : (x[m].time : Int) < (Restated.Vocabulary.Execution.Setup.a M S (r + 1)))
    (hgc : ∀ v ∈ Restated.grade1PerformersW M S Sched (r + 1),
      ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) .g1) →
      ∀ B : Block V,
        M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
          (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g1)
          (M.late S.E S.hc (r + 1) .g1) B ⇢ true →
        Block.compatible B Dn.erase = true)
    (hprev : Restated.HeadsBelow M S Sched x Dn.erase ((M.opening_slot S.hc (r + 1)) + 1)) :
    Restated.HeadsBelow M S Sched x Dn.erase ((M.opening_slot S.hc (r + 1)) + 2) := by
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hRd : 12 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
  have hsucc := facts.gr.action_succ_eq_add_rounds S r
  have hsucc1 := facts.gr.action_succ_eq_add_rounds S (r + 1)
  obtain ⟨t', ht'E, ht's, ht'len, hcs'⟩ :=
    Restated.exists_cone_cutoff facts S Sched tE hmono hcom tGAT gap hgst hlen hphase hcs hr
  have hRs : (M.opening_slot S.hc r) + 2 ≤ (M.opening_slot S.hc (r + 1)) + 1 := by
    rw [facts.gr.opening_slot_succ]
    exact Nat.le_succ_of_le (Nat.add_le_add_left (le_trans (by decide) S.hc.R_ge_three) _)
  have hso : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) = slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) + 6 * S.E.Δ := by
    rw [← Restated.confirmation_time_opening_slot facts S (r + 1)]; exact (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E _).symm
  have hss1 : slotStart S.E.Δ ((M.opening_slot S.hc (r + 1)) + 1)
      = slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) + 4 * S.E.Δ := by
    exact slotStart_succ S.E.Δ _
  have hsR : M.support_cutoff S.E ((M.opening_slot S.hc (r + 1)) + 1)
      ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1 := by
    have e1 : M.support_cutoff S.E ((M.opening_slot S.hc (r + 1)) + 1)
        = Restated.Vocabulary.Execution.Setup.a M S (r + 1) := by
      rw [← facts.sch.confirmation_time_eq_support_cutoff_succ,
        Restated.confirmation_time_opening_slot facts S (r + 1)]
    rw [e1]; linarith
  have hvt : M.vote_time S.E ((M.opening_slot S.hc (r + 1)) + 1 + 1)
      = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 5 * S.E.Δ + 4 * S.E.Δ * ((2 : Nat) : Int) :=
    Restated.vote_time_opening_slot_add facts S (r + 1) 2
  push_cast at hvt
  have hAB : Restated.ConeAnchorCompatible M S x Dn.erase ((M.opening_slot S.hc (r + 1)) + 1) :=
    Restated.coneAnchorCompatible_of_voteReads facts S x
      (Restated.voteGradeOneCompatible_of_gradedCompatible_rule facts S Sched x hmono hgc (j := 2)
        (by have := S.hc.R_ge_three; omega) rfl)
      (Restated.voteFinJustCompatible_before_succ_succ_tick facts S Sched x hmono hn hF hJ
        (by rw [hvt]; linarith) (by rw [hvt]; linarith))
  have hpath := Restated.coneAnchorChainInTree_thirdSlot_ofHolder facts S Sched x tE hexec hmono htd hsync hmult
    tGAT gap hgst hlen hcv hthird hphase hcs hn'' hDv_1 hv_1 hm hmlt hF hhmax
    (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
  have hrange := Restated.headsBelow_range_afterPhase (hr1 := Restated.one_le_round_of_of_opening_slot_le facts S (r := r + 1) (Nat.le_add_left 1 r) (Nat.le_succ _)) facts S Sched x hexec hsync hmult htd hmono hgst hcv
    (fun t h1 h2 => hphase t h1 (le_trans h2 ht'E))
    (fun t h => hthird t (le_trans h ht'E)) hcs' ht'len
    (Restated.deliveredDescendant_before_succ_succ_tick facts S Sched x hF tGAT)
    (Restated.finalizedPreceqAtSteps_before_succ_succ_tick facts S Sched x hF tGAT)
    (s₀ := (M.opening_slot S.hc (r + 1)) + 1) (s₁ := (M.opening_slot S.hc (r + 1)) + 1)
    (Nat.succ_pos _) (le_trans ht's (slotStart_mono S hRs)) hsR
    (fun s h0 h1 => by
      have hs : s = (M.opening_slot S.hc (r + 1)) + 1 := le_antisymm h1 h0
      rw [hs]; exact hAB)
    (fun s h0 h1 => by
      have hs : s = (M.opening_slot S.hc (r + 1)) + 1 := le_antisymm h1 h0
      rw [hs]; exact hpath)
    hprev (by intro s _ _ m hm q hq; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hm (facts.sch.vote_time_emod_delta S _) (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_HonSlot facts S Sched _ hq, fun h => ((Restated.mem_HonSlot facts).mp hq).2.2 (hmono _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) h)⟩)) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
  exact hrange _ (Nat.le_succ _) le_rfl

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Stamping a store's clock does not change the outcomes of the confirmation eligibility test for
    slot `s`. -/
private theorem confEligible_setClock_joint (facts : Record.Facts M) (E : Env V) (st : M.NS)
    (t : Int) (s : Slot) :
    Restated.Vocabulary.Protocol.confEligible M E (M.ns_setClock E st t).core s
      = Restated.Vocabulary.Protocol.confEligible M E st.core s := by
  have htau : (M.ns_setClock E st t).core.tau = st.core.tau :=
    facts.sto.tau_eq_of_fields (facts.hd.Sts_setClock_core_T E st t)
      (facts.hd.setClock_core_timestamp_block E st t) (facts.hd.setClock_core_timestamp_vote E st t)
  have hpool : (M.ns_setClock E st t).core.pool s = st.core.pool s :=
    facts.hd.Sts_setClock_core_pool E st t s
  unfold Restated.Vocabulary.Protocol.confEligible
    Restated.Vocabulary.Protocol.confCount Restated.Vocabulary.Protocol.confVotes
    Restated.Vocabulary.Protocol.confEarly Restated.Vocabulary.Protocol.confLate
  rw [htau, hpool, facts.hd.setClock_core_timestamp_vote, facts.hd.Sts_setClock_core_T]

open scoped DC in
/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim_joint {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

open scoped DC in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro_joint {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

open scoped DC in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff_joint {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
    (m >>= k) ⇢ b ↔ ∃ a, m ⇢ a ∧ k a ⇢ b := by
  unfold Record.Returns
  simp only [ExceptT.run_bind, Set.bind_def]
  constructor
  · intro h
    obtain ⟨e, he, hb⟩ := Set.mem_iUnion₂.mp h
    cases e with
    | ok a => exact ⟨a, he, hb⟩
    | error err => simp at hb
  · rintro ⟨a, ha, hb⟩
    exact Set.mem_iUnion₂.mpr ⟨_, ha, hb⟩

open scoped DC in
/-- The lift of the set `s` can return `a` exactly when `a ∈ s`. -/
private theorem returns_lift_iff_joint {α : Type} (s : Set α) (a : α) :
    (ExceptT.lift s : DC.NDRE α) ⇢ a ↔ a ∈ s := by
  unfold Record.Returns
  simp only [ExceptT.run_lift, Set.fmap_eq_image, Set.mem_image]
  constructor
  · rintro ⟨a', ha', he⟩
    cases he
    exact ha'
  · intro h
    exact ⟨a, h, rfl⟩

/-- At every node state `n`, `actionFGSource` can return some value. -/
private theorem actionFGSource_nonempty_joint (facts : Record.Facts M) (S : Setup V)
    (n : M.N) : ∃ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ o := by
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
  obtain ⟨o, ho⟩ := facts.dt.fg_source_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) A2
  exact ⟨o, (returns_bind_iff_joint _ _ _).2 ⟨A2, hA2, ho⟩⟩

/-- For every store `hs` the round-`r₁` action can give from `before`, `hs.live_confirmed` either
    passes some outcome of the confirmation eligibility test of `before`'s store for the slot before
    the action instant's, or is the `confRoot` of `before`'s store with its clock set to the action
    instant. -/
private theorem actionHealingStore_live_confirmed_cases_joint (facts : Record.Facts M)
    (S : Setup V) (before : M.N) (r₁ : Round) (hs : M.HS)
    (hhs : hs ∈ Restated.actionHealingStore M S before r₁) :
    (∃ el : Block V → Bool, Restated.Vocabulary.Protocol.confEligible M S.E before.st.core
        (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) ⇢ el ∧
        el hs.live_confirmed = true) ∨
      hs.live_confirmed
        = Restated.Vocabulary.Protocol.confRoot M
            (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core := by
  classical
  obtain ⟨c, hc, X, hX, st₀, hst₀, rfl⟩ := Restated.actionHealingStore_eq facts S before r₁ hs hhs
  obtain ⟨hF₀, hJ₀, hhj₀, hhm₀, hlc₀, hT₀, hs₀, hσ₀⟩ :=
    Restated.HS_fields_store_with_cache facts c hst₀
  simp only [hF₀, hJ₀, hhj₀, hhm₀, hlc₀, hT₀, hs₀, hσ₀] at *
  rw [Record.Model.HS.live_confirmed, facts.sto.toHealing_live_confirmed]
  by_cases hroot : X.live_confirmed = Restated.Vocabulary.Protocol.confRoot M
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
  · exact Or.inr hroot
  · left
    obtain ⟨tm, htm⟩ := facts.sto.tau_nonempty
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
    obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.toHealing
      (M.round_of S.hc
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.s)
    obtain ⟨score, hscore⟩ : ∃ score : Block V → ℕ, ∀ B, M.goldfish_score S.E
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.T
        ((beforeCutoff tm (M.support_cutoff S.E (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1))
          ((M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.pool
            (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1))).filter
          (fun u => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M S.E
            (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
            (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1)) u = true))
        ((beforeCutoff tm (M.support_cutoff S.E (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1))
          ((M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.pool
            (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1))).filter
          (fun u => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M S.E
            (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
            (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1)) u = true))
        (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) B ⇢ score B :=
      ⟨fun B => (facts.fc.goldfish_score_nonempty _ _ _ _ _ B).choose,
        fun B => (facts.fc.goldfish_score_nonempty _ _ _ _ _ B).choose_spec⟩
    obtain ⟨W, hW⟩ := facts.fc.ghost_nonempty R
      (M.get_filtered_block_tree
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.toHealing.toFG)
      score
      (fun B => decide (Restated.Vocabulary.Protocol.confCount M S.E
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
        (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) < 2 * score B))
    have hwalk := facts.hd.update_confirmation_with_live_confirmed_walk_or_fgRoot
      (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
      (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) tm htm R hR score hscore W hW X hX
    have hgen := facts.hd.update_confirmation_with_live_confirmed_genuine_or_fgRoot
      (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
      (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) tm htm R hR score hscore W hW X hX
    rcases hwalk with hwalk | hfg
    · rcases hgen with ⟨-, -, hel⟩ | hfg
      · refine ⟨fun B => decide (Restated.Vocabulary.Protocol.confCount M S.E
          (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
          (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) < 2 * score B), ?_, ?_⟩
        · rw [← confEligible_setClock_joint facts S.E before.st
            (Restated.Vocabulary.Execution.Setup.a M S r₁)]
          refine (returns_bind_iff_joint _ _ _).2 ⟨_, returns_map_intro_joint _ _ _
            (returns_map_intro_joint _ _ _ htm), ?_⟩
          refine (returns_bind_iff_joint _ _ _).2 ⟨score, (returns_lift_iff_joint _ _).2 hscore, ?_⟩
          exact (Record.returns_pure _ _).2 rfl
        · rw [hwalk]
          exact hel
      · exact absurd hfg hroot
    · exact absurd hfg hroot

/-- For every choice `att` of the round-`(r + 1)` action attestations, with `T'` the anchor
    `newAnchor` gives along `att`: if round `r` is at or after the switch round, the invariant holds
    at round `r` with tick step `n` and anchor `T`, `T ⪯ T'`, no honest height vote signed up to
    step `n' + 1` names a height greater than `T'`'s, every honest justified block from step `n_W`
    to `n'' + 1` is an ancestor of `T'`, and the round-`r` SG blocks of the members of
    `HonRound S Sched r` are ancestors of the heads at round `(r + 1)`'s opening slot and compatible
    with the confirmed blocks of the members of `HonRound S Sched (r + 1)`, then every member of
    `HonSlot` of round `(r + 1)`'s third slot votes there for a descendant of `T'`. -/
theorem headsAtNewAnchor_of_joint (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} {n n' n'' n_W : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n₀ : Nat, Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n₀ T)
    (hjust : ∀ n₀ : Nat, Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n₀ T)
    (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) (hn'' : Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1))))
    {att : V → NamedAttestation V} (hatt : Restated.ActionAttestationsOf M S Sched x r n' att)
    (hTT' : Block.Preceq T.erase (Restated.newAnchor M S Sched x r n' att T).erase)
    (hceil' : ∀ (v : V) (n₂ : Nat) (a : NamedAttestation V) (h' : Height)
      (entry : BlockId) (tmo : Bool),
      n₂ ≤ n' + 1 → Restated.HonestThrough M Sched x n₂ v → a.val_index = v →
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n₂].sent →
      a.height_pair = NamedHeightPair.vote h' entry tmo →
      h' ≤ (M.derive_named S.E S.cfg (Restated.newAnchor M S Sched x r n' att T)).h)
    (hJ' : ∀ (v : V) (n₁ : Nat), n_W ≤ n₁ → n₁ ≤ n'' + 1 → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J (Restated.newAnchor M S Sched x r n' att T).erase)
    (hP : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
      a.round = r → a.val_index = v_1 →
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
      Restated.HeadsBelow M S Sched x C.erase ((M.opening_slot S.hc (r + 1))))
    (hQ : Restated.ConfirmedCompatibleFreshSGOverHonRound M S Sched x r n n')
    (hrecvR : Restated.NextRoundReceipts M S Sched x r) :
    Restated.HeadsBelow M S Sched x (Restated.newAnchor M S Sched x r n' att T).erase ((M.opening_slot S.hc (r + 1)) + 2) := by
  classical
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hRd : 12 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
  have hsucc := facts.gr.action_succ_eq_add_rounds S r
  have hsucc1 := facts.gr.action_succ_eq_add_rounds S (r + 1)
  have hn := hinv.tick
  obtain ⟨hn1, -⟩ := Restated.tickStepAt_time facts x hn
  obtain ⟨hn'1, hn'0⟩ := Restated.tickStepAt_time facts x hn'
  have hnn' : n + 1 ≤ n' := Restated.tick_succ_le_tick_succ_round facts S Sched x hn hn'
  have hnWn : n_W ≤ n := Restated.tick_le_of_round_le facts S Sched x hnW hn hr
  have hnWn' : n_W ≤ n' := by omega
  have hopen : M.opening S.E S.hc r ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
    show _ ≤ M.a S.hc S.E.Δ r
    rw [facts.gr.opening_eq_proposal_time, facts.sch.a_eq_confirmation_time]
    exact facts.sch.proposal_time_le_confirmation_time _ _
  have htGAT : tGAT ≤ (Restated.Vocabulary.Execution.Setup.a M S r) :=
    le_trans (Restated.tGAT_le_switchOpening facts S tGAT tE gap hgst hlen)
      (le_trans (Restated.switchOpening_le_opening facts S hr) hopen)
  have hso : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) = slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) + 6 * S.E.Δ := by
    rw [← Restated.confirmation_time_opening_slot facts S (r + 1)]; exact (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E _).symm
  have hlo : tGAT ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) := by linarith
  have hRs : (M.opening_slot S.hc r) + 2 ≤ (M.opening_slot S.hc (r + 1)) := by
    rw [facts.gr.opening_slot_succ]
    exact Nat.add_le_add_left (le_trans (by decide) S.hc.R_ge_three) _
  obtain ⟨t', ht'E, ht's, ht'len, hcs'⟩ :=
    Restated.exists_cone_cutoff facts S Sched tE hmono hcom tGAT gap hgst hlen hphase hcs hr
  have hcs2 := Restated.committeeSleepinessW_at_heads_slot facts S Sched tE hmono hcom tGAT gap hgst hlen hphase
    hcs hr
  have hsE : t' ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) :=
    le_trans ht's (slotStart_mono S hRs)
  have hfinT := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts S Sched x tE
    hexec hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hcross hn'
  have hjustT := Restated.justified_old_anchor_before_succ_tick_of_hypotheses facts S Sched x tE
    hexec hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hjust hn'
  have hprevT := Restated.headsBelow_secondSlot_at_anchor facts S Sched x tE hexec hmono htd hsync hmult hcom
    tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hjust hn'
  obtain ⟨T', hT'⟩ : ∃ T' : NamedBlock V, T' = Restated.newAnchor M S Sched x r n' att T := ⟨_, rfl⟩
  rw [← hT'] at hTT' hceil' hJ' ⊢
  have hF' := Restated.fin_preceq_before_succ_succ_tick facts S Sched x hn'' hnWn' hfinT hTT' hJ'
  have hJ'' := Restated.just_preceq_before_succ_succ_tick facts S Sched x hn'' hnWn' hjustT hTT' hJ'
  have hhmax' := Restated.hMax_le_anchor_succ_before_succ_tick_ofCeiling facts S Sched x hexec hmono
    (tE := Restated.switchOpening M S tE)
    (Restated.roundSleepinessW_switchOpening_of_phase facts S Sched tGAT tE gap hgst hlen hmono hthird hphase
      hrsW)
    hn' hceil' hn''
    (Restated.switchOpening_le_opening facts S (le_trans hr (Nat.le_add_right r 2)))
  have hvt1 : M.vote_time S.E ((M.opening_slot S.hc (r + 1)) + 1)
      = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 5 * S.E.Δ + 4 * S.E.Δ * ((1 : Nat) : Int) :=
    Restated.vote_time_opening_slot_add facts S (r + 1) 1
  push_cast at hvt1
  have hFJ0 : Restated.VoteFinJustCompatible M S x T'.erase ((M.opening_slot S.hc (r + 1))) :=
    Restated.voteFinJustCompatible_before_succ_succ_tick facts S Sched x hmono hn hF' hJ''
      (by rw [hvt1]; linarith) (by rw [hvt1]; linarith)
  by_cases hex : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C
  · -- the anchor moved to a block `NewAnchorSpec` describes
    have hchoice : T' = hex.choose := by
      rw [hT']
      show (if h : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C then h.choose
        else T) = hex.choose
      rw [dif_pos hex]
    obtain ⟨q, hqW, hmem, h₀, tmo, hvote⟩ := hex.choose_spec.2.2.2
    rw [← hchoice] at hmem hvote
    have hq : q ∈ Restated.freshAttesters M S Sched x (r + 1) (n' + 1) :=
      Restated.freshAttestersW_subset_freshAttesters facts S Sched x (r + 1) (n' + 1) hqW
    obtain ⟨nr, hnr, ns, rec, hD⟩ := hatt q hqW
    obtain ⟨o, ho⟩ := actionFGSource_nonempty_joint facts (Setup.alwaysAwake S) nr
    obtain ⟨Cfg, rfl, hpre⟩ :=
      Restated.entry_preceq_source facts S Sched x hexec hn' hq hmem rfl nr hnr
        (ns, rec, att q) hD hvote o ho
    have hCfg := ho
    have hhsq : M.toHealing nr.st.core ∈ Restated.actionHealingStore M S (x[n'][q].st) (r + 1) :=
      ⟨nr, hnr, rfl⟩
    have qH : q ∈ Restated.HonRound M S Sched (r + 1) :=
      Restated.freshAttestersW_subset_honRound facts S Sched x (le_of_eq hn'1.symm) hqW
    have hqn' : Restated.HonestThrough M Sched x n' q := fun t ht =>
      Restated.honestThrough_of_mem_freshAttestersW facts hqW t
        (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.le_succ n')))
    have hqm : tGAT ≤ (x[n'].time : Int) := by linarith
    have hqlt : (x[n'].time : Int) < (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := by linarith
    have hfinish : ∀ X : Block V, Block.Preceq T'.erase X →
        (∀ v_1 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
          a.round = r → a.val_index = v_1 →
          (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
          ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
          Block.compatible C.erase X = true) →
        Restated.HeadsBelow M S Sched x T'.erase ((M.opening_slot S.hc (r + 1)) + 1) →
        Restated.HeadsBelow M S Sched x T'.erase ((M.opening_slot S.hc (r + 1)) + 2) := fun X hDX hX h1 =>
      Restated.headsBelow_thirdSlot_of_anchorFacts facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT gap
        hgst hlen hcv hthird hphase hcs hr hn hn'' hF' hJ'' hhmax' hmem hqn' hqm hqlt
        (Restated.graded_compatible_of_sgCompatible (hrecvR := hrecvR) facts S Sched x tE hexec hmono htd hsync
          hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hDX hX)
        h1
    have hAB0 : ∀ X : Block V, Block.Preceq T'.erase X →
        (∀ v_1 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
          a.round = r → a.val_index = v_1 →
          (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
          ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
          Block.compatible C.erase X = true) →
        Restated.ConeAnchorCompatible M S x T'.erase ((M.opening_slot S.hc (r + 1))) := fun X hDX hX =>
      Restated.coneAnchorCompatible_of_voteReads facts S x
        (Restated.voteGradeOneCompatible_of_gradedCompatible_rule facts S Sched x hmono
          (Restated.graded_compatible_of_sgCompatible (hrecvR := hrecvR) facts S Sched x tE hexec hmono htd
            hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hDX hX)
          (j := 1) (by have := S.hc.R_ge_three; omega) rfl)
        hFJ0
    rcases Restated.source_cases facts S (x[n'][q].st) (r + 1) nr hnr Cfg hCfg with hlc | hQ2
    · -- the confirmation branch
      have hDX : Block.Preceq T'.erase (M.toHealing nr.st.core).live_confirmed :=
        preceq_trans_Preceq hpre hlc
      have hX : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
          a.round = r → a.val_index = v_1 →
          (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
          ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
          Block.compatible C.erase (M.toHealing nr.st.core).live_confirmed = true :=
        fun v_1 hv_1 a har hai has C hC hac => hQ q qH v_1 hv_1 a har hai has C hC hac _ hhsq
      have hFq : Block.Preceq (M.toHealing nr.st.core).F T.erase := by
        rw [Restated.actionHealingStore_F facts S _ _ _ hhsq]; exact hfinT q n' le_rfl hqn'
      have hJq : (M.toHealing nr.st.core).h_max = (M.toHealing nr.st.core).h_j + 1 →
          Block.Preceq (M.toHealing nr.st.core).J T.erase := by
        intro hroot
        rw [Restated.actionHealingStore_h_max facts S _ _ _ hhsq,
          Restated.actionHealingStore_h_j facts S _ _ _ hhsq] at hroot
        rw [Restated.actionHealingStore_J facts S _ _ _ hhsq]
        exact hjustT q n' hnn' le_rfl hqn' hroot
      have hrootq := Restated.confRoot_setClock_preceq_ofAction facts S (x[n'][q].st) r _ hhsq hFq hJq
      have hct : M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))) = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
        Restated.confirmation_time_opening_slot facts S (r + 1)
      have hn'c : Restated.tickStepAt M x n'
          (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) := by
        rw [hct]; exact hn'
      have hqaw := Restated.honRound_awakeThroughout_confirmation facts S Sched (r + 1) qH
      have hqA : q ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) := (Finset.mem_sdiff.1 qH).2
      have hqh : HonestThroughTime Sched
          (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) q :=
        fun t'' ht'' hin => hqA (hmono _ _ (by rw [← hct]; exact ht'') hin)
      have hpath0 : Restated.ConeAnchorChainInTree M S x T'.erase ((M.opening_slot S.hc (r + 1))) := by
        rcases actionHealingStore_live_confirmed_cases_joint facts S (x[n'][q].st) (r + 1) _ hhsq with
          ⟨el, hel', hel⟩ | hlcR
        · rw [Restated.slotOf_a_sub_one facts S (r + 1)] at hel'
          exact Restated.coneAnchorChainInTree_of_eligibleConfirmation facts S Sched x tE hexec hmono htd hsync
            hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hqaw hqh el hel' hel hDX
            hTT' hlo le_rfl (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
        · have hlc2 : Block.Preceq T'.erase (Restated.Vocabulary.Protocol.confRoot M
              (M.ns_setClock S.E (x[n'][q].st).st
                (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))))).core) := by
            rw [hct, ← hlcR]; exact hDX
          have heq : T'.erase = T.erase := Block.preceq_antisymm (preceq_eq_true_iff_Preceq.mpr (preceq_trans_Preceq hlc2 hrootq))
            (preceq_eq_true_iff_Preceq.mpr hTT')
          rw [heq]
          exact Restated.coneAnchorChainInTree_at_anchor_of_committee facts S Sched x tE
            hexec hmono htd hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hcs2
            (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) _ hRs le_rfl
      have hvf : M.view_freeze S.E ((M.opening_slot S.hc (r + 1))) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1 := by
        have e1 := facts.sch.view_freeze_lt_confirmation_time S.E ((M.opening_slot S.hc (r + 1)))
        rw [hct] at e1
        have e1' := Int.add_one_le_of_lt e1
        linarith
      have h1 := Restated.headsBelow_secondSlot_of_confirmed_afterPhase facts S Sched x hexec hsync hmult htd
        hmono hgst hcv (fun t h1 h2 => hphase t h1 (le_trans h2 ht'E))
        (fun t h => hthird t (le_trans h ht'E)) hcs' ht'len
        (Restated.deliveredDescendantUnderFinalized_anchor facts S Sched x hn' hfinT tGAT)
        (Restated.finalizedPreceqAtSteps_anchor facts S Sched x hn' hfinT tGAT) hlo hvf hn' qH _ hhsq rfl
        hTT' hDX hrootq hprevT (hAB0 _ hDX hX) hpath0 (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
        (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
      exact hfinish _ hDX hX h1
    · -- the grade-2 branch
      obtain ⟨g, hg⟩ := facts.gr.read_nonempty (M.gradeContract nr.cache) S.E S.hc
        (M.toHealing nr.st.core) (r + 1)
      obtain ⟨o2, ho2⟩ := facts.gr.grade2Block_nonempty (M.toHealing nr.st.core)
        (M.readFrame nr.cache (M.toHealing nr.st.core) (r + 1))
      have hgo2 := facts.nd.ModelProperties_gradeContract_read_Q2 nr.cache S.E S.hc
        (M.toHealing nr.st.core) (r + 1) g hg o2 ho2
      have hgQ := hQ2 g ((facts.nd.gradeContract_read nr.cache S.E S.hc (M.toHealing nr.st.core)
        (r + 1) g).1 hg)
      obtain ⟨root, hroot, hQroot⟩ := facts.gr.grade2Block_preceq_root o2 ho2 (hgo2.symm.trans hgQ)
      obtain ⟨m₂, G, hm₂, hGall, hrootG⟩ := Restated.actionFrame_g2_provenance facts S Sched x hn' q
        root _ ⟨nr, hnr, rfl⟩ hroot
      obtain ⟨bG, hbG⟩ := facts.gr.gradeBool_nonempty S.E
        (M.gradeView (M.toHealing (x[m₂][q].st).st.core)) (x[m₂][q].st).st.core.F S.hc.η_SG (r + 1)
        (M.early S.E S.hc (r + 1) .g2) (M.late S.E S.hc (r + 1) .g2) G
      have hG : M.gradeBool S.E (M.gradeView (M.toHealing (x[m₂][q].st).st.core))
          (x[m₂][q].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g2)
          (M.late S.E S.hc (r + 1) .g2) G ⇢ true := by
        rw [← hGall bG hbG]; exact hbG
      obtain ⟨v_2, hv_2, a₂, har₂, hai₂, has₂, C₂, hC₂, hac₂, hGC₂⟩ :=
        Restated.graded_preceq_freshSG_of_premises (hrecvR := hrecvR) facts S Sched x tE hexec hmono htd hsync
          hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross qH
          (facts.gr.domain_le_action S (r + 1) .g2) hm₂ G hG (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
          (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hinv.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨Restated.awake_action_of_mem_honRound facts hv, (Finset.mem_sdiff.1 hv).2⟩))
      have hDX : Block.Preceq T'.erase C₂.erase :=
        preceq_trans_Preceq hpre (preceq_trans_Preceq hQroot (preceq_trans_Preceq hrootG hGC₂))
      have hX : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
          a.round = r → a.val_index = v_1 →
          (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
          ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
          Block.compatible C.erase C₂.erase = true :=
        fun v_1 hv_1 a har hai has C hC hac =>
          hinv.sgPairwise v_1 hv_1 v_2 hv_2 a a₂ har hai has har₂ hai₂ has₂ C C₂ hC hac hC₂ hac₂
      have hv2h : Restated.HonestThrough M Sched x (n + 1) v_2 := fun t ht hin =>
        (Finset.mem_sdiff.1 hv_2).2 (hmono _ _ (by rw [hn1] at ht; exact ht) hin)
      have hvf : (x[n + 1].time : Int) + S.E.Δ
          < M.view_freeze S.E ((M.opening_slot S.hc (r + 1))) := by
        have hR3 : (M.opening_slot S.hc r) + 1 + 1 + 1 ≤ (M.opening_slot S.hc (r + 1)) := by
          rw [facts.gr.opening_slot_succ]
          exact Nat.add_le_add_left S.hc.R_ge_three _
        have e1 : Restated.Vocabulary.Execution.Setup.a M S r + S.E.Δ
            = M.view_freeze S.E ((M.opening_slot S.hc r) + 1) :=
          facts.sch.a_add_delta_eq_view_freeze S r
        have e2 := facts.sch.view_freeze_lt_vote_time_succ S.E ((M.opening_slot S.hc r) + 1)
        have e3 := facts.sch.vote_time_add_delta_le_confirmation_time S ((M.opening_slot S.hc r) + 1 + 1)
        have e4 := facts.sch.confirmation_time_eq_support_cutoff_succ S.E
          ((M.opening_slot S.hc r) + 1 + 1)
        have e5 := facts.sch.support_cutoff_mono S.E hR3
        have e6 := facts.sch.Sts_support_cutoff_lt_view_freeze S.E ((M.opening_slot S.hc (r + 1)))
        rw [hn1]; linarith
      have hpath0 : Restated.ConeAnchorChainInTree M S x T'.erase ((M.opening_slot S.hc (r + 1))) :=
        Restated.coneAnchorChainInTree_of_heldDescendant facts S Sched x tE hexec hmono htd hsync hmult tGAT gap
          hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hC₂ hv2h (by rw [hn1]; exact htGAT)
          hDX hTT' hvf le_rfl (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
      have h0 : Restated.HeadsBelow M S Sched x T'.erase ((M.opening_slot S.hc (r + 1))) :=
        fun w mw hw' hmw G hG => preceq_trans_Preceq hDX (hP v_2 hv_2 a₂ har₂ hai₂ has₂ C₂ hC₂ hac₂ w mw
          hw' hmw G hG)
      have hsR : M.support_cutoff S.E ((M.opening_slot S.hc (r + 1)))
          ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1 := by
        have e1 := facts.sch.Sts_support_cutoff_lt_view_freeze S.E ((M.opening_slot S.hc (r + 1)))
        have e2 := facts.sch.view_freeze_lt_confirmation_time S.E ((M.opening_slot S.hc (r + 1)))
        rw [Restated.confirmation_time_opening_slot facts S (r + 1)] at e2
        linarith
      have hpos : 0 < (M.opening_slot S.hc (r + 1)) := facts.gr.opening_slot_pos S (Nat.succ_pos r)
      have hrange := Restated.headsBelow_range_afterPhase (hr1 := Restated.one_le_round_of_of_opening_slot_le facts S (r := r + 1) (Nat.le_add_left 1 r) le_rfl) facts S Sched x hexec hsync hmult htd hmono hgst hcv
        (fun t h1 h2 => hphase t h1 (le_trans h2 ht'E))
        (fun t h => hthird t (le_trans h ht'E)) hcs' ht'len
        (Restated.deliveredDescendant_before_succ_succ_tick facts S Sched x hF' tGAT)
        (Restated.finalizedPreceqAtSteps_before_succ_succ_tick facts S Sched x hF' tGAT)
        (s₀ := (M.opening_slot S.hc (r + 1))) (s₁ := (M.opening_slot S.hc (r + 1)))
        hpos hsE hsR
        (fun s h0' h1' => by
          have hs : s = (M.opening_slot S.hc (r + 1)) := le_antisymm h1' h0'
          rw [hs]; exact hAB0 _ hDX hX)
        (fun s h0' h1' => by
          have hs : s = (M.opening_slot S.hc (r + 1)) := le_antisymm h1' h0'
          rw [hs]; exact hpath0)
        h0 (by intro s _ _ m hm q hq; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hm (facts.sch.vote_time_emod_delta S _) (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_HonSlot facts S Sched _ hq, fun h => ((Restated.mem_HonSlot facts).mp hq).2.2 (hmono _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) h)⟩)) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
      exact hfinish _ hDX hX (hrange _ (Nat.le_succ _) le_rfl)
  · -- the anchor did not move: `T' = T`
    have hchoice : T' = T := by
      rw [hT']
      show (if h : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C then h.choose
        else T) = T
      rw [dif_neg hex]
    rw [hchoice] at hF' hJ'' hhmax' ⊢
    obtain ⟨v₀, m₀, hTbody, hv₀h, hm₀, hm₀t⟩ :=
      Restated.exists_anchor_holder_of_committee facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hr hinv
        hcs2
    exact Restated.headsBelow_thirdSlot_of_anchorFacts facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT
      gap hgst hlen hcv hthird hphase hcs hr hn hn'' hF' hJ'' hhmax' hTbody hv₀h hm₀
      (by linarith)
      (fun v hv m hm B hB => Restated.grade1_compatible_at_awakeReader_recv facts S Sched x
        tE hexec hmono htd hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross
        (facts.gr.domain_le_action S (r + 1) .g1) _ (Restated.early_g1_sub_delta_le_late_g1_sub_rr facts S (r + 1))
        (Finset.mem_sdiff.1 hv).1 (hrecvR.perf hv) (Finset.mem_sdiff.1 hv).2 hm B hB (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
        (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hinv.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨Restated.awake_action_of_mem_honRound facts hv, (Finset.mem_sdiff.1 hv).2⟩)))
      hprevT

end

end DecoupledConsensusModel.Sts.Restated
