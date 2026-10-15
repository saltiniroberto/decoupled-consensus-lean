import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13bK_FinalityDeadlineArith
import Proofs.Claims.Restated.Claim13bK_JointBase
import Proofs.Claims.Restated.Claim13bSGCompatible
import Proofs.Claims.Restated.Claim13beRoute3_76
import Proofs.Claims.Restated.Claim13beRoute3_85d
import Proofs.Claims.Restated.Claim13beRoute3_85f
import Proofs.Claims.Restated.Claim13beRoute3_88
import Proofs.Claims.Restated.Claim13beRoute3_91
import Proofs.Claims.Restated.Claim13beRoute3_97
import Proofs.Claims.Restated.Constants
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.Claim13beRoute3_97
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_ClaimFinalityLiveAfterHealing
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Honest proposals are finalized

That a slot proposed at or after the phase end comes after the switch round's third slot, and that,
under the phase premises, every honest proposal in the window is an ancestor of the finalized block
of every late honest reader. Stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- On the phase's premises, if the proposal time of `s` is at or after `tE`, then `s` is at least
    the opening slot of the switch round of `tE` plus `2`. -/
theorem switchOpening_add_two_le_of_le_proposal_f3 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    {tGAT tE : Int} {gap : Nat}
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    {s : Slot} (hsE : tE ≤ M.proposal_time S.E s) :
    (M.opening_slot S.hc (Restated.switchRound M S tE)) + 2 ≤ s := by
  let rho₀ : Record.Run V := { honest := ∅, horizon := 0, events := [] }
  have hrDrW : Restated.deadlineRoundW M S tGAT gap + 2 ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_add_two_le_rebased_l88 facts S Sched rho₀ hgst hlen hrec).trans
      (Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap rho₀ hgst hlen)
  have hne : Restated.switchRound M S tE ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (Nat.succ_pos _) hrDrW)
  have hspec := Restated.switchRound_spec facts S tE hne
  by_contra hlt
  have hle : s ≤ (M.opening_slot S.hc (Restated.switchRound M S tE)) + 2 := le_of_lt (not_le.mp hlt)
  have hp := facts.sch.proposal_time_mono S.E hle
  have h6 := (facts.sch.slot_instants_l55 S.E
    ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2)).2.2.2.2.2
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  linarith

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- On the phase premises with the phase length `hlen` and `tE ≤ tL`, for every slot `s` with
    `tE ≤ proposal_time s` and `proposal_time s + finalityPremisesContinueDirect S gap ≤ tL`, whose
    proposer is not held at any time up to `s`'s vote time, every block `B` that proposer put in the
    sent log `x[i].sent` at a step `i` at or before that vote time is an ancestor of the finalized
    block of every validator honest through any read at or after
    `proposal_time s + finalityDeadlineDirect S gap`. -/
theorem finalizedAfterDeadline_of_premises_f3 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE tL : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE) (hEL : tE ≤ tL)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched) (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tL →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tL →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tL gap)
    (hsl : sleepinessW S Sched tE) (hrs : Restated.roundSleepinessW M S Sched tE)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    {s : Slot} (hsE : tE ≤ M.proposal_time S.E s)
    (hcont : M.proposal_time S.E s + Restated.finalityPremisesContinueDirect M S gap ≤ tL)
    (hprop : HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s))
    {i : Nat} {B : Block V} (hB : Restated.proposedBlockAtStep M S x i s B)
    (hi : (x[i].time : Int) ≤ M.vote_time S.E s) :
    ∀ (v : V) (j : Nat), Restated.HonestThrough M Sched x j v →
      M.proposal_time S.E s + Restated.finalityDeadlineDirect M S gap ≤ (x[j].time : Int) →
      Block.Preceq B (x[j][v].st).st.core.F := by
  intro v j hv hj
  -- the phase's premises at `tE`, read off the continued ones
  have hthirdE : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight :=
    fun t ht => hthird t (ht.trans hEL)
  have hphaseE : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t :=
    fun t h1 h2 => hawake t h1 (h2.trans hEL)
  have hrecE : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap :=
    fun t h1 h2 => hrec t h1 (h2.trans hEL)
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  -- the internal hypotheses
  have hlow := Restated.hlow_of_premises_l85f facts S Sched x tGAT tE gap hgap hlen hgst hmono hexec hsync hmult
    hwakes hsleeps hcv htd hcom hthirdE hphaseE hrecE hsl hrs hcs
  have hprev := Restated.basePreviousRoundSGCompatibleWithAnchor_atRound facts S Sched x tGAT tE gap hlen hgst
    hmono hexec hsync hmult hcv hcom hthirdE hphaseE hrecE
  have hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T :=
    fun r hrD' hrW => Restated.baseClearFGSource_atRound_of_premises facts S Sched x tGAT tE gap hgst hmono
      hexec hsync hmult hcv hcom hthirdE hphaseE r
      ((Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrD') hrW
  have hB' := Restated.baseJustifiedHighAtSwitchRoundW_of_phase facts S Sched x tGAT tE gap hgap hlen hgst hmono
    hexec hsync hmult hwakes hsleeps hcv htd hcom hthirdE hphaseE hrecE hsl hrs hcs
  obtain ⟨n_W, T_W, hnW, hAW, hJ⟩ := Restated.afterPhaseInvariantOverActiveSetsJoint_at_switchRound facts S
    Sched x tGAT tE gap hgap hlen hgst hmono hexec hsync hmult hwakes hsleeps hcv htd hcom hthirdE
    hphaseE hrecE hsl hrs hcs hprev hclear hB'
  have hJswitch := Restated.justifiedAncestor_before_switchTick_of_justifiedHigh facts S Sched x tE hexec hmono
    htd tGAT gap hgst hlen' hsync hthirdE hphaseE hrs hmult hcv hcom hrecE hprev hclear hnW hAW
    (hlow n_W hnW)
  have hs0 := Restated.switchOpening_add_two_le_of_le_proposal_f3 facts S Sched hgst hlen' hrecE hsE
  have hdead : M.proposal_time S.E s + Restated.finalityDeadlineSharpLanded_f7 M S gap ≤ tL :=
    le_trans (by linarith [Restated.finalityDeadlineSharpLanded_le_continue_f4 facts S gap]) hcont
  exact Restated.honestProposal_finalizedAfterDeadline_f7 facts S Sched x v tGAT tE tL gap hgap hlen hEL hgst
    hmono hexec hsync hmult hcv htd hcom hthird hawake hrec hrs hcs hwakes hsleeps hprev hclear hB'
    hnW hAW hJswitch le_rfl (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) hJ hs0 hprop hB hi hdead
    v j hv hj

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- On the phase premises with `gap + 2 ≤ K`, `tGAT + (healingLengthη S gap + period) ≤ tE` and
    `tE ≤ tL`, every honest proposal made at or after the start and at least
    `finalityPremisesContinueDirect S gap` before `tL` is an ancestor of the finalized block of
    every validator honest through any read at or after its proposal time plus
    `finalityDeadlineDirect S gap`. -/
theorem finalityIncluded_of_premises_f3 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE tL : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE) (hEL : tE ≤ tL)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched) (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tL →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tL →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tL gap)
    (hsl : sleepinessW S Sched tE) (hrs : Restated.roundSleepinessW M S Sched tE)
    (hcs : Restated.committeeSleepinessW M S Sched tE) :
    Restated.FinalityIncludedAfterHealing M S Sched x tE tL gap := by
  intro s hstart hcont hprop i B hB hi
  have hstartup : (0 : Int) ≤ Restated.finalityStartupDirect M S gap :=
    mul_nonneg (Int.natCast_nonneg _) (Restated.constants_holds facts S).period_pos.le
  have hsE : tE ≤ M.proposal_time S.E s := by
    have h : Restated.finalityLiveStart M S tE gap = tE + Restated.finalityStartupDirect M S gap := rfl
    rw [h] at hstart
    linarith
  exact Restated.finalizedAfterDeadline_of_premises_f3 facts S Sched x tGAT tE tL gap hgap hlen hEL hgst hmono
    hexec hsync hmult hwakes hsleeps hcv htd hcom hthird hawake hrec hsl hrs hcs hsE hcont hprop
    hB hi

end

end DecoupledConsensusModel.Sts.Restated
