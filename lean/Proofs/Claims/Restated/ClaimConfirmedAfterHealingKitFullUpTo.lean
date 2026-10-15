import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13bK_ConfirmedWakeUpTo
import Proofs.Claims.Restated.Claim13beRoute3_76
import Proofs.Claims.Restated.Claim13beRoute3_85fUpTo
import Proofs.Claims.Restated.Claim13beRoute3_88UpTo
import Proofs.Claims.Restated.Claim13beRoute3_91UpTo
import Proofs.Claims.Restated.ClaimConfirmedAfterHealingKit
import Proofs.Claims.Restated.ClaimConfirmedAfterHealingKitUpTo
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ConfirmedRecordUpTo
import Model.Conditions.Claim13bK_ConfirmedWakeUpTo
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Records settled at the action ticks, up to a slot

A theorem over a model `M : Record.Model V` with facts `facts : Record.Facts M`: from the healing
premises and the records settled up to a slot `sEnd`, the records settled at the action ticks, with
synchrony assumed only up to a bound (`recordsSettledAtActionTicks_of_joint_upTo`).
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
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- From the healing premises, with synchrony only up to
    `max tE (S.a (S.hc.round_of (sEnd - 2) + 1))`, and the records settled at the settle tick up to
    slot `sEnd`: at the action instant of every round after the switch round, every honest active
    attester of that round that is at the round after the switch round, or that woke at the round's
    previous action instant, holds right after the tick two records that are ancestors of every
    honest head from slot `o_r + 3` to `sEnd`. -/
theorem recordsSettledAtActionTicks_of_joint_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {sEnd : Slot}
    (hsync : Restated.SynchronyFromWakeBefore M S x (max tE ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (sEnd - 2)) + 1)))))
    (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched) (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hsl : sleepinessW S Sched tE) (hrs : Restated.roundSleepinessW M S Sched tE)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hsettle : Restated.RecordsSettledAtSettleTickTo M S Sched x tE sEnd) :
    Restated.RecordsSettledAtActionTicksTo M S Sched x tE sEnd := by
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  have hsE : Restated.SynchronyFromWakeBefore M S x tE := Restated.SynchronyFromWakeBefore.mono (le_max_left _ _) hsync
  have hlow := Restated.hlow_of_premises_l85f_upTo facts S Sched x tGAT tE gap hgap hlen hgst hmono hexec hsE hmult
    hwakes hsleeps hcv htd hcom hthird hawake hrec hsl hrs hcs
  have hprev := Restated.basePreviousRoundSGCompatibleWithAnchor_atRound_upTo facts S Sched x tGAT tE gap hlen hgst
    hmono hexec hsE hmult hcv hcom hthird hawake hrec
  have hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T :=
    fun r hrD' hrW => Restated.baseClearFGSource_atRound_of_premises_upTo facts S Sched x tGAT tE gap hgst hmono
      hexec hsE hmult hcv hcom hthird hawake r
      ((Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrD') hrW
  have hB' := Restated.baseJustifiedHighAtSwitchRoundW_of_hlow facts S Sched x tGAT tE gap hlow
  obtain ⟨n_W, T_W, hnW, hAW, hJswitch, hbase⟩ :=
    Restated.afterPhaseJointSwitchRound_of_premises_upTo facts S Sched x tGAT tE gap hgap hlen hgst hmono hexec hsE
      hmult hwakes hsleeps hcv htd hcom hthird
      hawake hrec hsl hrs hcs hlow
  exact Restated.recordsSettledAtActionTicks_of_settleTick_upTo facts S Sched x tE hexec hmono htd tGAT gap
    hgst hlen' hsync hthird hawake hrs hmult hcv hcs hcom hwakes hsleeps hrec hprev hclear hB' hnW
    hAW hJswitch (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) hbase hsettle le_rfl

end

end DecoupledConsensusModel.Sts.Restated
