import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_Claim13bf
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Agreement of confirmed outputs after healing

The settle instant, the agreement and monotonicity of honest confirmed outputs from it on, and the
statement that they hold after a long enough phase, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The settle instant: the action instant of the round after the switch round of `tE`. -/
noncomputable def confirmedSettleTime (M : Record.Model V) (S : Setup V) (tE : Int) : Int := (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE + 1))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- From the settle instant on, any two validators honest through their reads, each awake throughout
    the vote window of its read's slot, hold confirmed outputs on one chain. -/
def ConfirmedAgreeAfterHealing (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) : Prop :=
  ∀ (v₁ v₂ : V) (i j : Nat),
    Restated.HonestThrough M Sched x i v₁ → Restated.HonestThrough M Sched x j v₂ →
    Restated.confirmedSettleTime M S tE ≤ (x[i].time : Int) →
    Restated.confirmedSettleTime M S tE ≤ (x[j].time : Int) →
    v₁ ∈ activeAtW S Sched (S.E.slotOf (x[i].time : Int)) →
    v₂ ∈ activeAtW S Sched (S.E.slotOf (x[j].time : Int)) →
    Block.Compatible (Restated.Read.confirmed M x[i][v₁].st)
      (Restated.Read.confirmed M x[j][v₂].st)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- From the settle instant on, a validator honest through the later of two reads and awake
    throughout the vote window at both holds, at the later read, a confirmed output that is a
    descendant of the one it held at the earlier read. -/
def ConfirmedMonotoneAfterHealing (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) : Prop :=
  ∀ (v : V) (i j : Nat), i ≤ j →
    Restated.HonestThrough M Sched x j v →
    Restated.confirmedSettleTime M S tE ≤ (x[i].time : Int) →
    v ∈ activeAtW S Sched (S.E.slotOf (x[i].time : Int)) →
    v ∈ activeAtW S Sched (S.E.slotOf (x[j].time : Int)) →
    Block.Preceq (Restated.Read.confirmed M x[i][v].st)
      (Restated.Read.confirmed M x[j][v].st)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every `gap` with `gap + 2 ≤ S.cfg.K` there is a `tHeal ≥ 0` such that every execution
    meeting the premises listed over a phase `[tGAT, tAwakeEnd]` of length at least `tHeal`
    satisfies `ConfirmedAgreeAfterHealing` and `ConfirmedMonotoneAfterHealing` at `tAwakeEnd`. -/
def claimConfirmedAfterHealingStatement (M : Record.Model V) (S : Setup V) (Sched : Schedule V) : Prop :=
  ∀ gap : Nat, gap + 2 ≤ S.cfg.K →
  ∃ tHeal : Int, 0 ≤ tHeal ∧
  ∀ (x : AtomicExec (Record.protocolOf M S) Sched) (tGAT tAwakeEnd : Int),
    tGAT + tHeal ≤ tAwakeEnd →
    S.E.t_GST ≤ tGAT →
    Sched.MonotoneCorruption →
    Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x →
    Restated.SynchronyFromWake M S x →
    AwakeAtMultiples S Sched →
    Restated.WakesAtActionInstants M S Sched →
    Restated.SleepsAfterActionInstants M S Sched →
    Restated.CatchUpOnWake M S x →
    Restated.TimeDiverges M x →
    Restated.HonestCommittees M S Sched (Restated.interface M S Sched) →
    (∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) →
    (∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) →
    Restated.strongOpeningsRecurFrom M S Sched tGAT tAwakeEnd gap →
    sleepinessW S Sched tAwakeEnd →
    Restated.roundSleepinessW M S Sched tAwakeEnd →
    Restated.committeeSleepinessW M S Sched tAwakeEnd →
    Restated.ConfirmedAgreeAfterHealing M S Sched x tAwakeEnd ∧
      Restated.ConfirmedMonotoneAfterHealing M S Sched x tAwakeEnd

end

end DecoupledConsensusModel.Sts.Restated
