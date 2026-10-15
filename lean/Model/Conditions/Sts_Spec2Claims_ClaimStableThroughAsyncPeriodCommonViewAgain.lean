import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_ClaimConfirmedAfterHealing
import Model.Conditions.Sts_Spec2Claims_ClaimStableThroughAsyncPeriod
import Model.Record.Wiring

/-!
# The stable output through one asynchronous period, with the common view again

The statement that the stable output persists through one asynchronous period when the common view
is asked again after it, stated over a model `M : Record.Model V`.
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

/-- For every `gap` with `gap + 2 ≤ S.cfg.K` there is a `tHeal ≥ 0` such that, in every execution
    meeting the premises listed, with synchrony and catch-up suspended on an asynchronous period
    `[b₀, b₁)`, the phase's premises asked again on `[tAgain, tSafe]`, and the common view
    `CommonViewAtGAT` at `tAgain`, the stable output persists from `b₀` on
    (`StablePersistsFromRound`). -/
def claimStableThroughOneAsyncPeriodCommonViewAgainStatement (M : Record.Model V) (S : Setup V) (Sched : Schedule V) :
    Prop :=
  ∀ gap : Nat, gap + 2 ≤ S.cfg.K →
  ∃ tHeal : Int, 0 ≤ tHeal ∧
  ∀ (x : AtomicExec (Record.protocolOf M S) Sched) (tGAT tAwakeEnd b₀ b₁ tAgain tSafe : Int) (r : Nat),
    tGAT + tHeal ≤ tAwakeEnd →
    S.E.t_GST ≤ tGAT →
    Sched.MonotoneCorruption →
    Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x →
    Restated.SynchronyFromWakeOutside M S x b₀ b₁ →
    AwakeAtMultiples S Sched →
    Restated.WakesAtActionInstants M S Sched →
    Restated.SleepsAfterActionInstants M S Sched →
    Restated.CatchUpOnWakeOutside M S x b₀ b₁ →
    Restated.CommonViewAtGAT M S Sched x tGAT →
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
    Restated.confirmedSettleTime M S tAwakeEnd ≤ (M.a S.hc S.E.Δ r) →
    -- the asynchronous period `[b₀, b₁)`, placed after rounds `r + 1` and `r + 2`
    Restated.periodAfterRound M S (r + 1) b₀ →
    b₀ ≤ b₁ →
    Restated.periodBeforeExpiry M S (r + 1) b₁ →
    Restated.fixedRoundSleepinessCountedW M S Sched (r + 1) →
    -- the outside attesters, then the phase's premises again on `[tAgain, tSafe]`
    Restated.outsideAttestersUnderThird M S Sched (r + 1) →
    b₁ + S.E.Δ ≤ tAgain →
    tAgain + (tHeal + Restated.liveAgainAfterHealing M S gap) ≤ tSafe →
    (∀ t : Int, t ≤ tSafe →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) →
    (∀ t : Int, tAgain ≤ t → t ≤ tSafe →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) →
    Restated.strongOpeningsRecurFrom M S Sched tAgain tSafe gap →
    Restated.CommonViewAtGAT M S Sched x tAgain →
    Restated.StablePersistsFromRound M S Sched x tAwakeEnd r b₀

end

end DecoupledConsensusModel.Sts.Restated
