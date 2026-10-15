import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActive
import Proofs.Claims.Restated.Claim13bK_AnchorMove
import Proofs.Claims.Restated.Claim13bK_ConfirmedOld
import Proofs.Claims.Restated.Claim13bK_FgJustified
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bK_Frame
import Proofs.Claims.Restated.Claim13bK_FrameNew
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bK_GradeOld
import Proofs.Claims.Restated.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.Claim13bPhaseSleepiness
import Proofs.Claims.Restated.Claim13bStepActionF
import Proofs.Claims.Restated.Claim13bStepActiveClauses
import Proofs.Claims.Restated.Claim13bStepAssembly
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRelay
import Proofs.Claims.Restated.Claim13bStepPairwise
import Proofs.Claims.Restated.Claim13bStepSGMove
import Proofs.Claims.Restated.Claim13bW_Ceiling
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_FgJustified
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepActiveAssembly
import Model.Conditions.Claim13bStepAnchor
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13bStepFieldsAt
import Model.Conditions.Claim13bStepGrade
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The clauses of the invariant at the next round

The clauses of the round invariant over the active sets at round `r + 1`, each derived from the step
hypotheses at round `r`; stated over a model `M : Record.Model V`.
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

/-- From any node state `before`, validator `v`'s round-`r` action read can compute some
    attestation. -/
private theorem actionAttestationFrom_nonempty_asm (facts : Record.Facts M) (S : Setup V)
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

/-- If `AfterPhaseStepHypothesesOverActiveSets` holds, then `StepFieldsAt S Sched x tE r n n' T`
    holds at every round `r` anchored at `T` with tick step `n`, where `n'` is the tick step at
    `S.a (r + 1)`. -/
theorem stepFieldsAt_of_hyp (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hmono : Sched.MonotoneCorruption)
    (hyp : Restated.AfterPhaseStepHypothesesOverActiveSets M S Sched x tE) :
    ∀ (r : Round) (n n' : Nat) (T : NamedBlock V),
      Restated.AnchoredRoundOverActiveSets M S Sched x tE r n T → Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFieldsAt M S Sched x tE r n n' T := by
  intro r n n' T hctx hn'
  exact ⟨fun att hatt v hv => hyp.confirmedNew r n n' T hctx hn' att hatt v
      (Restated.honRound_subset_honestThroughSet facts S Sched (r + 1) hmono hv),
    hyp.gradePairwise r n n' T hctx hn', hyp.gradeDescendant r n n' T hctx hn',
    hyp.headsAtNewAnchor r n n' T hctx hn'⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every choice `att` of the round-`(r + 1)` action attestations, the round-`r` anchor is an
    ancestor of the round-`(r + 1)` anchor read along `att`. -/
theorem anchor_preceq_new_of_hypotheses_overActiveSets (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hctx : Restated.AnchoredRoundOverActiveSets M S Sched x tE r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) :
    ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
      Block.Preceq T.erase (Restated.newAnchor M S Sched x r n' att T).erase := by
  intro att hatt
  have hinv := hctx.2
  refine Restated.old_preceq_new facts S Sched x hexec hn' hatt hinv.inPlay hinv.anchorEntry ?_
  refine Restated.newAnchor_compatible_old_ofSpec facts S Sched x hexec hn' hatt
    (fun q hq => ?_) (fun q hq => ?_)
  · exact Restated.confirmedOld_at_honRound facts S Sched x tE hexec hmono htd hsync hmult hcom
      tGAT gap hgst hlen hcv hthird hphase hrsW hcs hctx.1 hctx.2 hcross hjust hw hn'
      (Restated.freshAttestersW_subset_honRound facts S Sched x (le_of_eq (Restated.tickStepAt_time facts x hn').1.symm) hq)
      (by intro s _ _ m hm q hq; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hm (facts.sch.vote_time_emod_delta S _) (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_HonSlot facts S Sched _ hq, fun h => ((Restated.mem_HonSlot facts).mp hq).2.2 (hmono _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) h)⟩))
      (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
      (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
      (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hctx.2.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched (show v ∈ Sched.awakeThroughout (M.a S.hc S.E.Δ _ - wAttest S) (M.a S.hc S.E.Δ _) from (Finset.mem_sdiff.1 hv).1) (by linarith [twelve_delta_le_wAttest S, S.E.Δ_pos]) (le_refl _), (Finset.mem_sdiff.1 hv).2⟩))
  · exact Restated.frameG2Old_of_gradeOld facts S Sched x r n' T hn'
      (Restated.gradeOld_of_premisesOnly facts S Sched x tE hexec hmono htd hsync hmult tGAT gap
        hgst hlen hcv hthird hphase hrsW hcs hctx.1 hctx.2 hcross
        (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
        (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hctx.2.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched (show v ∈ Sched.awakeThroughout (M.a S.hc S.E.Δ _ - wAttest S) (M.a S.hc S.E.Δ _) from (Finset.mem_sdiff.1 hv).1) (by linarith [twelve_delta_le_wAttest S, S.E.Δ_pos]) (le_refl _), (Finset.mem_sdiff.1 hv).2⟩))) q
      (Restated.freshAttestersW_subset_honRound facts S Sched x (le_of_eq (Restated.tickStepAt_time facts x hn').1.symm) hq)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The `grade1` clause of the round invariant over the active sets at round `r + 1`, from `StepFieldsAt`
    at round `r`: for every choice `att` of the round-`(r + 1)` action attestations, every block the
    grade test of an honest active attester of round `r + 1` can pass for round `r + 1`, at any
    phase whose domain instant is at or before that action, lies on one chain with the
    round-`(r + 1)` anchor read along `att`. -/
theorem grade1_field_of_hypotheses_overActiveSets_ofFieldsAt (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hctx : Restated.AnchoredRoundOverActiveSets M S Sched x tE r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hf : Restated.StepFieldsAt M S Sched x tE r n n' T) :
    ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
    ∀ v ∈ Restated.HonRound M S Sched (r + 1),
      ∀ p : Protocol.Phase, M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) →
      ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p) →
      ∀ B : Block V,
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
          (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
          (M.late S.E S.hc (r + 1) p) B ⇢ true →
      Block.compatible B (Restated.newAnchor M S Sched x r n' att T).erase = true := fun att hatt =>
  Restated.grade1_field_at_new_anchor_overActiveSets facts S Sched x
    (Restated.anchor_preceq_new_of_hypotheses_overActiveSets facts S Sched x tE hexec hmono htd
        tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hctx hcross hjust hn'
        att hatt)
    (Restated.gradeOld_of_premises facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync
      hthird hphase hrsW hctx.1 hctx.2
      (Restated.freshSGHeadsAtLate_of_premises facts S Sched x tE hexec hmono htd hsync hmult
        tGAT gap hgst hlen hcv hthird hphase hrsW hcs hctx.1 hctx.2 hcross
        (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
        (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hctx.2.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched (show v ∈ Sched.awakeThroughout (M.a S.hc S.E.Δ _ - wAttest S) (M.a S.hc S.E.Δ _) from (Finset.mem_sdiff.1 hv).1) (by linarith [twelve_delta_le_wAttest S, S.E.Δ_pos]) (le_refl _), (Finset.mem_sdiff.1 hv).2⟩)))
      (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hctx.2.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched (Restated.hawT_of_honRound_succ facts S Sched hv (Restated.action_mono facts S (Nat.le_succ _))) (le_refl _) (le_refl _), Restated.hwh_of_honRound_succ facts S Sched hmono hv⟩))
      (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hctx.2.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched (show v ∈ Sched.awakeThroughout (M.a S.hc S.E.Δ _ - wAttest S) (M.a S.hc S.E.Δ _) from (Finset.mem_sdiff.1 hv).1) (by linarith [twelve_delta_le_wAttest S, S.E.Δ_pos]) (le_refl _), (Finset.mem_sdiff.1 hv).2⟩)))
    (hf.gradeDescendant att hatt)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every choice `att` of the round-`(r + 1)` action attestations, every grade-1 root any
    round-`(r + 1)` action frame of an honest active attester of round `r + 1` offers lies on one
    chain with the round-`(r + 1)` anchor read along `att`. -/
theorem frameG1New_of_hypotheses_overActiveSets (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hctx : Restated.AnchoredRoundOverActiveSets M S Sched x tE r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hf : Restated.StepFieldsAt M S Sched x tE r n n' T) :
    ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
    ∀ v ∈ Restated.HonRound M S Sched (r + 1),
      ∀ f ∈ Restated.actionFrame M S (x[n'][v].st) (r + 1), ∀ root : Block V,
      f.g1 = some (some root) →
      Block.compatible root (Restated.newAnchor M S Sched x r n' att T).erase = true := fun att hatt =>
  Restated.frameG1_compatible_of_grade1 facts S Sched x r n'
    (Restated.newAnchor M S Sched x r n' att T) hn'
    (Restated.grade1_field_of_hypotheses_overActiveSets_ofFieldsAt facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hctx hcross hjust hn' hf
      att hatt)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every choice `att` of the round-`(r + 1)` action attestations, every grade-2 root any
    round-`(r + 1)` action frame of an honest active attester of round `r + 1` offers lies on one
    chain with the round-`(r + 1)` anchor read along `att`. -/
theorem frameG2New_of_hypotheses_overActiveSets (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hctx : Restated.AnchoredRoundOverActiveSets M S Sched x tE r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hf : Restated.StepFieldsAt M S Sched x tE r n n' T) :
    ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
    ∀ v ∈ Restated.HonRound M S Sched (r + 1),
      ∀ f ∈ Restated.actionFrame M S (x[n'][v].st) (r + 1), ∀ root : Block V,
      f.g2 = some (some root) →
      Block.compatible root (Restated.newAnchor M S Sched x r n' att T).erase = true := fun att hatt =>
  Restated.frameG2Old_of_gradeOld facts S Sched x r n'
    (Restated.newAnchor M S Sched x r n' att T) hn'
    (Restated.grade1_field_of_hypotheses_overActiveSets_ofFieldsAt facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hctx hcross hjust hn' hf
      att hatt)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- GST is at or before the start of round `r + 1`'s opening slot. -/
theorem gst_le_opening_slot_of_hypotheses_overActiveSets (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hctx : Restated.AnchoredRoundOverActiveSets M S Sched x tE r n T) :
    S.E.t_GST ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) := by
  refine le_trans (Restated.gst_le_switchOpening facts S tGAT tE gap hgst hlen) ?_
  rw [facts.sch.Γ_0_eq_proposal_time, ← facts.gr.opening_eq_proposal_time]
  exact Restated.switchOpening_le_opening facts S (le_trans hctx.1 (Nat.le_succ r))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The `inPlay` clause of the round invariant over the active sets at round `r + 1`: for every choice
    `att` of the round-`(r + 1)` action attestations, the round-`(r + 1)` anchor read along `att` is
    one of the blocks the execution put in play. -/
theorem inPlay_field_of_hypotheses_overActiveSets (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hctx : Restated.AnchoredRoundOverActiveSets M S Sched x tE r n T) :
    ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
    Restated.blockInLog M S Sched x (Restated.newAnchor M S Sched x r n' att T) := fun _ _ =>
  Restated.inPlay_field_at_new_anchor facts S Sched x hctx.2.inPlay

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The `anchorEntry` clause of the round invariant over the active sets at round `r + 1`: for every
    choice `att` of the round-`(r + 1)` action attestations, the replay of the round-`(r + 1)`
    anchor read along `att` names it as its height's entry. -/
theorem anchorEntry_field_of_hypotheses_overActiveSets (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hctx : Restated.AnchoredRoundOverActiveSets M S Sched x tE r n T) :
    ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
    (M.derive_named S.E S.cfg (Restated.newAnchor M S Sched x r n' att T)).T_h
      = (Restated.newAnchor M S Sched x r n' att T).erase := fun _ _ =>
  Restated.newAnchor_entry facts S Sched x hctx.2.anchorEntry

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The `band` clause of the round invariant over the active sets at round `r + 1`: for every choice
    `att` of the round-`(r + 1)` action attestations, the largest `Σ.h_max` any honest active
    attester of round `r + 1` holds at that round's tick step, less one, is at most the chain-state
    height of the round-`(r + 1)` anchor read along `att`. -/
theorem band_field_of_hypotheses_overActiveSets (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hctx : Restated.AnchoredRoundOverActiveSets M S Sched x tE r n T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) :
    ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
    Restated.hmaxRoundAt M S Sched x (r + 1) n' - 1
      ≤ (M.derive_named S.E S.cfg (Restated.newAnchor M S Sched x r n' att T)).h := fun _ hatt =>
  Restated.band_field_at_succ_overActiveSets_ofHeightCeiling facts S Sched x (tE := Restated.switchOpening M S tE)
    hexec hmono
    (Restated.roundSleepinessW_switchOpening_of_phase facts S Sched tGAT tE gap hgst hlen hmono hthird hphase hrsW)
    hctx.2.tick hn' hatt (Restated.switchOpening_le_opening facts S hctx.1) T hctx.2.heightCeiling

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The `fin` clause of the round invariant over the active sets at round `r + 1`, from `StepFieldsAt` at
    round `r`: for every choice `att` of the round-`(r + 1)` action attestations, whatever a
    validator honest through its own read has finalized, at any step up to round `r + 1`'s tick, is
    an ancestor of the round-`(r + 1)` anchor read along `att`. -/
theorem fin_field_of_hypotheses_overActiveSets_ofFieldsAt (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hctx : Restated.AnchoredRoundOverActiveSets M S Sched x tE r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hf : Restated.StepFieldsAt M S Sched x tE r n n' T) :
    ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
    ∀ (v : V) (n₁ : Nat), n₁ ≤ n' + 1 → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.F (Restated.newAnchor M S Sched x r n' att T).erase := by
  intro att hatt
  refine Restated.fin_field_at_succ_top_ofRoundSleepinessW facts S Sched x hexec hmono (tE := Restated.switchOpening M S tE)
    (Restated.roundSleepinessW_switchOpening_of_phase facts S Sched tGAT tE gap hgst hlen hmono hthird hphase hrsW)
    hw hs hctx.2.tick hn' hatt
    (Restated.switchOpening_le_opening facts S (le_trans hctx.1 (Nat.le_succ r))) hctx.2.inPlay
    (Restated.anchor_preceq_new_of_hypotheses_overActiveSets facts S Sched x tE hexec hmono htd
        tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hctx hcross hjust hn'
        att hatt)
    (fun q hq => hf.confirmedNew att hatt q
      (Restated.mem_honRound_of_mem_freshAttesters_ofWakes facts S Sched x hw hn' hq))
    (fun q hq => Restated.frameG2New_of_hypotheses_overActiveSets facts S Sched x tE hexec hmono htd
        tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hctx hcross hjust hn' hf
        att hatt q
      (Restated.mem_honRound_of_mem_freshAttesters_ofWakes facts S Sched x hw hn' hq))
    (P := fun w m => Restated.HonestThrough M Sched x m w)
    (fun _ _ h => h)
    (fun _ _ _ hm h t ht => h t (le_trans ht (Restated.time_mono_int facts S Sched x hm)))
    (fun _ _ hm h t ht => h t (le_trans ht hm))
    hctx.2.heightCeiling hctx.2.fin hctx.2.targetsTop (hcross n' hn')

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every choice `att` of the round-`(r + 1)` action attestations, the finalized block of every
    healing store of the round-`(r + 1)` action read of a validator honest through round `r + 1`'s
    action instant is an ancestor of the round-`(r + 1)` anchor read along `att`. -/
theorem fgFinalized_of_hypotheses_overActiveSets (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hctx : Restated.AnchoredRoundOverActiveSets M S Sched x tE r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hf : Restated.StepFieldsAt M S Sched x tE r n n' T) :
    ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
    ∀ v ∈ honestThroughSet Sched ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1),
      Block.Preceq hs.F (Restated.newAnchor M S Sched x r n' att T).erase := fun att hatt =>
  Restated.actionHealingStore_F_preceq_of_fin facts S Sched x hn'
    (Restated.fin_field_of_hypotheses_overActiveSets_ofFieldsAt facts S Sched x tE hexec hmono htd
        tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hs hctx hcross hjust hn' hf
        att hatt)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every healing store `hs` of the round-`(r + 1)` action read of a validator honest through
    round `r + 1`'s action instant, if `hs.h_max = hs.h_j + 1` then `hs`'s justified block is an
    ancestor of the round-`r` anchor. -/
theorem fgJustified_of_hypotheses_overActiveSets (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hctx : Restated.AnchoredRoundOverActiveSets M S Sched x tE r n T)
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) :
    ∀ v ∈ honestThroughSet Sched ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1),
      (hs : M.HS).h_max = hs.h_j + 1 → Block.Preceq hs.J T.erase :=
  Restated.actionJ_preceq_old_anchor facts S Sched x hn'
    (Restated.tick_succ_le_tick_succ_round facts S Sched x hctx.2.tick hn')
    (Restated.justified_old_anchor_before_succ_tick_of_hypotheses facts S Sched x tE hexec hmono
      tGAT gap hgst hlen hthird hphase hrsW hctx.1 hctx.2 hjust hn')

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The `sg` clause of the round invariant over the active sets at round `r + 1`, from `StepFieldsAt` at
    round `r`: for every choice `att` of the round-`(r + 1)` action attestations, every SG block an
    honest active attester of round `r + 1` attested to at that round lies on one chain with the
    round-`(r + 1)` anchor read along `att`. -/
theorem sg_field_of_hypotheses_overActiveSets_ofFieldsAt (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hctx : Restated.AnchoredRoundOverActiveSets M S Sched x tE r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hf : Restated.StepFieldsAt M S Sched x tE r n n' T) :
    ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
    ∀ v ∈ Restated.HonRound M S Sched (r + 1), ∀ a : NamedAttestation V,
      a.round = r + 1 → a.val_index = v →
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n' + 1].sent →
      ∀ C : NamedBlock V, C ∈ (x[n' + 1][v].st).st.bodies → a.confirmed = some C.root →
      Block.compatible C.erase (Restated.newAnchor M S Sched x r n' att T).erase = true :=
  fun att hatt =>
  Restated.sg_field_at_new_anchor_overActiveSets_ofFrameOverHonRound facts S Sched x hexec hmono hn' hatt
    (Restated.anchor_preceq_new_of_hypotheses_overActiveSets facts S Sched x tE hexec hmono htd
        tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hctx hcross hjust hn'
        att hatt)
    (hf.confirmedNew att hatt)
    (Restated.frameG1New_of_hypotheses_overActiveSets facts S Sched x tE hexec hmono htd
        tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hctx hcross hjust hn' hf
        att hatt)
    (Restated.frameG2New_of_hypotheses_overActiveSets facts S Sched x tE hexec hmono htd
        tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hctx hcross hjust hn' hf
        att hatt)
    (Restated.fgFinalized_of_hypotheses_overActiveSets facts S Sched x tE hexec hmono htd
        tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hs hctx hcross hjust hn' hf
        att hatt)
    (Restated.fgJustified_of_hypotheses_overActiveSets facts S Sched x tE hexec hmono tGAT gap hgst
        hlen hthird hphase hrsW hctx hjust hn')

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The `sgPairwise` clause of the round invariant over the active sets at round `r + 1`, from
    `StepFieldsAt` at round `r`: any two SG blocks two honest active attesters of round `r + 1`
    attested to at that round lie on one chain. -/
theorem sgPairwise_field_of_hypotheses_overActiveSets_ofFieldsAt (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hctx : Restated.AnchoredRoundOverActiveSets M S Sched x tE r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hf : Restated.StepFieldsAt M S Sched x tE r n n' T) :
    ∀ v₁ ∈ Restated.HonRound M S Sched (r + 1), ∀ v₂ ∈ Restated.HonRound M S Sched (r + 1),
      ∀ a₁ a₂ : NamedAttestation V,
      a₁.round = r + 1 → a₁.val_index = v₁ →
      (⟨v₁, NamedObject.attest a₁⟩ : SignedMsg V (NamedObject V)) ∈ x[n' + 1].sent →
      a₂.round = r + 1 → a₂.val_index = v₂ →
      (⟨v₂, NamedObject.attest a₂⟩ : SignedMsg V (NamedObject V)) ∈ x[n' + 1].sent →
      ∀ C₁ C₂ : NamedBlock V,
      C₁ ∈ (x[n' + 1][v₁].st).st.bodies → a₁.confirmed = some C₁.root →
      C₂ ∈ (x[n' + 1][v₂].st).st.bodies → a₂.confirmed = some C₂.root →
      Block.compatible C₁.erase C₂.erase = true := by
  have htH : (x[n' + 1].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := le_of_eq (Restated.tickStepAt_time facts x hn').1
  have hsub : Restated.HonRound M S Sched (r + 1) ⊆ honestThroughSet Sched ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) :=
    Restated.honRound_subset_honestThroughSet facts S Sched (r + 1) hmono
  -- one choice of the round-`(r + 1)` action attestations: every action read can compute one
  let att : V → NamedAttestation V := fun q => Classical.choose
    (actionAttestationFrom_nonempty_asm facts (Setup.alwaysAwake S) (x[n'][q].st) q (r + 1))
  have hatt : Restated.ActionAttestationsOf M S Sched x r n' att := fun q _ =>
    Classical.choose_spec
      (actionAttestationFrom_nonempty_asm facts (Setup.alwaysAwake S) (x[n'][q].st) q (r + 1))
  have hold := Restated.anchor_preceq_new_of_hypotheses_overActiveSets facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hctx hcross hjust hn'
      att hatt
  have hF := Restated.fgFinalized_of_hypotheses_overActiveSets facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hs hctx hcross hjust hn' hf
      att hatt
  have fgJ := Restated.fgJustified_of_hypotheses_overActiveSets facts S Sched x tE hexec hmono
      tGAT gap hgst hlen hthird hphase hrsW hctx hjust hn'
  have hfg0 := Restated.fgRoot_preceq_at_reads_ofNewAnchorF facts S Sched x
    (tH' := (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) hold
  have hfg : ∀ v ∈ Restated.HonRound M S Sched (r + 1),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1),
      Block.Preceq (M.get_fg_root hs.toFG) (Restated.newAnchor M S Sched x r n' att T).erase :=
    fun v hv hs' hhs => hfg0 v (hsub hv) hs' hhs (hF v (hsub hv) hs' hhs)
      (fgJ v (hsub hv) hs' hhs)
  have hg1 := Restated.frameG1New_of_hypotheses_overActiveSets facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hctx hcross hjust hn' hf
      att hatt
  have hg2 := Restated.frameG2New_of_hypotheses_overActiveSets facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hctx hcross hjust hn' hf
      att hatt
  have hwalk : ∀ v ∈ Restated.HonRound M S Sched (r + 1),
      ∀ m ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (x[n'][v].st) (r + 1),
      ∀ g, M.frameGradeRead m.cache S.E S.hc (M.toHealing m.st.core) (r + 1) ⇢ g →
      Block.compatible (M.currentSGVote (M.toHealing m.st.core) g)
        (Restated.newAnchor M S Sched x r n' att T).erase = true :=
    fun v hv m hm g hg => Restated.sgVote_compatible_at_read facts S (x[n'][v].st) (r + 1) m hm g hg
      (hf.confirmedNew att hatt v hv _ ⟨m, hm, rfl⟩) (hg1 v hv _ ⟨m, hm, rfl⟩) (hg2 v hv _ ⟨m, hm, rfl⟩)
      (compatible_of_preceq_common_Preceq (hfg v hv _ ⟨m, hm, rfl⟩)
        (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)))
  have honest : ∀ v ∈ honestThroughSet Sched ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))), Restated.HonestThrough M Sched x n' v := by
    intro v hv t ht
    exact (mem_honestThroughSet.1 hv) t
      (le_trans ht (le_trans (Restated.time_mono_int facts S Sched x (Nat.le_succ n')) htH))
  have hlc : ∀ v₁ ∈ Restated.HonRound M S Sched (r + 1), ∀ v₂ ∈ Restated.HonRound M S Sched (r + 1),
      ∀ hs₁ ∈ Restated.actionHealingStore M S (x[n'][v₁].st) (r + 1),
      ∀ hs₂ ∈ Restated.actionHealingStore M S (x[n'][v₂].st) (r + 1),
      Block.compatible hs₁.live_confirmed hs₂.live_confirmed = true := by
    intro v₁ hv₁ v₂ hv₂ hs₁ hhs₁ hs₂ hhs₂
    exact Restated.live_confirmed_pairwise facts S Sched x hexec
      (T := Restated.newAnchor M S Sched x r n' att T)
      (Restated.gfVoteRelayAtAccept_of_sync facts S Sched x hsync) htd hn'
      (Restated.gst_le_opening_slot_of_hypotheses_overActiveSets facts S Sched x tE tGAT gap hgst hlen hctx)
      (honest v₁ (hsub hv₁)) (honest v₂ (hsub hv₂))
      (mem_honestThroughSet.1 (hsub hv₁) _ (le_refl _))
      (mem_honestThroughSet.1 (hsub hv₂) _ (le_refl _))
      (Restated.honRound_awakeThroughout_confirmation facts S Sched (r + 1) hv₁)
      (Restated.honRound_awakeThroughout_confirmation facts S Sched (r + 1) hv₂)
      hs₁ hhs₁ hs₂ hhs₂
      (hf.confirmedNew att hatt v₁ hv₁ hs₁ hhs₁)
      (hf.confirmedNew att hatt v₂ hv₂ hs₂ hhs₂)
      (hF v₁ (hsub hv₁) hs₁ hhs₁) (hF v₂ (hsub hv₂) hs₂ hhs₂)
      (fun hroot => preceq_trans_Preceq (fgJ v₁ (hsub hv₁) hs₁ hhs₁ hroot) hold)
      (fun hroot => preceq_trans_Preceq (fgJ v₂ (hsub hv₂) hs₂ hhs₂ hroot) hold)
      (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
  exact Restated.sgPairwise_field_at_succ_overActiveSets_overHonRound facts S Sched x hexec hmono hn'
    (att := att) hfg hwalk hlc
    (fun v₁ hv₁ v₂ hv₂ m₁ hm₁ g₁ hg₁ m₂ hm₂ g₂ hg₂ =>
      hf.gradePairwise v₁ hv₁ v₂ hv₂ m₁ hm₁ m₂ hm₂ g₁ hg₁ g₂ hg₂)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The `heads` clause of the round invariant over the active sets at round `r + 1`, from `StepFieldsAt`
    at round `r`: for every choice `att` of the round-`(r + 1)` action attestations, every honest
    active member of round `(r + 1)`'s third slot's committee votes there for a descendant of the
    round-`(r + 1)` anchor read along `att`. -/
theorem heads_field_of_hypotheses_overActiveSets_ofFieldsAt (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hf : Restated.StepFieldsAt M S Sched x tE r n n' T) :
    ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
    Restated.HeadsBelow M S Sched x (Restated.newAnchor M S Sched x r n' att T).erase
      ((M.opening_slot S.hc (r + 1)) + 2) :=
  hf.headsAtNewAnchor

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The `heightCeiling` clause of the round invariant over the active sets at round `r + 1`: for every
    choice `att` of the round-`(r + 1)` action attestations, no non-empty height vote authored and
    signed at a step up to the round-`(r + 1)` tick's successor by a validator honest through that
    step names a height greater than the chain-state height of the round-`(r + 1)` anchor read along
    `att`. -/
theorem heightCeiling_field_of_hypotheses_overActiveSets (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hctx : Restated.AnchoredRoundOverActiveSets M S Sched x tE r n T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) :
    ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
    ∀ (v : V) (n₁ : Nat) (a : NamedAttestation V) (h' : Height)
      (entry : BlockId) (tmo : Bool),
      n₁ ≤ n' + 1 → Restated.HonestThrough M Sched x n₁ v → a.val_index = v →
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n₁].sent →
      a.height_pair = NamedHeightPair.vote h' entry tmo →
      h' ≤ (M.derive_named S.E S.cfg (Restated.newAnchor M S Sched x r n' att T)).h := fun _ hatt =>
  Restated.heightCeiling_field_at_succ_of_fresh facts S Sched x hexec hw hs hctx.2.tick hn' hatt T
    hctx.2.heightCeiling

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The `targets` clause of the round invariant over the active sets at round `r + 1`, from
    `StepFieldsAt` at round `r`: for every choice `att` of the round-`(r + 1)` action attestations
    and every validator honest through round `r + 1`'s tick, every non-empty height-vote target at
    the chain-state height of the round-`(r + 1)` anchor read along `att`, authored and signed by a
    validator honest through its send at a step up to that tick, is an ancestor of that anchor. -/
theorem targetsTop_field_of_hypotheses_overActiveSets_ofFieldsAt (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hctx : Restated.AnchoredRoundOverActiveSets M S Sched x tE r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hf : Restated.StepFieldsAt M S Sched x tE r n n' T) :
    ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
    ∀ (w : V) (n₁ : Nat) (a : NamedAttestation V) (entry : BlockId) (tmo : Bool),
      n₁ ≤ n' + 1 → Restated.HonestThrough M Sched x n₁ w → a.val_index = w →
      (⟨w, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n₁].sent →
      a.height_pair = NamedHeightPair.vote
        (M.derive_named S.E S.cfg (Restated.newAnchor M S Sched x r n' att T)).h entry tmo →
      ∀ C : NamedBlock V, Restated.blockInLog M S Sched x C → C.root = entry →
      Block.Preceq C.erase (Restated.newAnchor M S Sched x r n' att T).erase := by
  intro att hatt
  refine Restated.targetsTop_field_at_succ_ofWakes facts S Sched x hexec hw hs hctx.2.tick hn' hatt
    hctx.2.inPlay
    (Restated.anchor_preceq_new_of_hypotheses_overActiveSets facts S Sched x tE hexec hmono htd
        tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hctx hcross hjust hn'
        att hatt)
    (fun q hq => hf.confirmedNew att hatt q
      (Restated.mem_honRound_of_mem_freshAttesters_ofWakes facts S Sched x hw hn' hq))
    (fun q hq => Restated.frameG2New_of_hypotheses_overActiveSets facts S Sched x tE hexec hmono htd
        tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hctx hcross hjust hn' hf
        att hatt q
      (Restated.mem_honRound_of_mem_freshAttesters_ofWakes facts S Sched x hw hn' hq))
    (P := fun w m => Restated.HonestThrough M Sched x m w)
    (fun _ _ h => h)
    (fun _ _ _ hm h t ht => h t (le_trans ht (Restated.time_mono_int facts S Sched x hm)))
    hctx.2.heightCeiling hctx.2.targetsTop

end

end DecoupledConsensusModel.Sts.Restated
