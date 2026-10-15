import Model.Sts.Spec2Claims.ClaimStableThroughAsyncPeriod
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_ClaimConfirmedAfterHealing
import Model.Conditions.Sts_Spec2Claims_ClaimFinalityLiveAfterHealing
import Model.Record.Wiring

/-!
# The stable output through one asynchronous period

Synchrony and catch-up suspended on an asynchronous period, the validators awake through two rounds
and the sleepiness premise over them, the placement of the period, and the statement that the stable
output persists through it, stated over a model `M : Record.Model V`.
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

/-- Whatever an honest validator puts on the wire at step `k` is delivered, at a step after `k` and
    strictly before `deadline` of the send's instant, to every validator awake at every instant from
    the one the message is on the wire through that deadline. -/
def SynchronyFromWakeBy (M : Record.Model V) (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) (deadline : Int → Int) : Prop :=
  ∀ (k : Nat) (w : V) (sm : SignedMsg V (NamedObject V)),
    Restated.HonestSendAt M S x k sm →
    w ∈ Sched.awakeThroughout (x[k + 1].time : Int) (deadline (x[k].time : Int)) →
    ∃ d : Nat, k < d ∧ x.lbl d = AtomicAction.deliver w sm ∧
      (x[k].time : Int) ≤ (x[d].time : Int) ∧
      (x[d].time : Int) < deadline (x[k].time : Int)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A message an honest validator sent before `w`'s wake instant `t_w` is delivered to `w` at or
    after the wake and strictly before `deadline t_w`, provided `w` stays awake through that
    deadline. -/
def CatchUpOnWakeBy (M : Record.Model V) (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) (deadline : Int → Int) : Prop :=
  ∀ (k : Nat) (w : V) (sm : SignedMsg V (NamedObject V)) (t_w : Int),
    Restated.HonestSendAt M S x k sm →
    (x[k].time : Int) < t_w →
    w ∈ Sched.awake t_w → w ∉ Sched.awake (t_w - 1) →
    w ∈ Sched.awakeThroughout t_w (deadline t_w) →
    ∃ d : Nat, k < d ∧ x.lbl d = AtomicAction.deliver w sm ∧
      t_w ≤ (x[d].time : Int) ∧ (x[d].time : Int) < deadline t_w

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Synchrony suspended on the asynchronous period `[b₀, b₁)`: `SynchronyFromWakeBy` with the
    deadline `deadlineOutside S b₀ b₁`. -/
def SynchronyFromWakeOutside (M : Record.Model V) (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) (b₀ b₁ : Int) : Prop :=
  Restated.SynchronyFromWakeBy M S x (deadlineOutside S b₀ b₁)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Catch-up on wake suspended on the asynchronous period `[b₀, b₁)`: `CatchUpOnWakeBy` with the
    deadline `deadlineOutside S b₀ b₁`. -/
def CatchUpOnWakeOutside (M : Record.Model V) (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) (b₀ b₁ : Int) : Prop :=
  Restated.CatchUpOnWakeBy M S x (deadlineOutside S b₀ b₁)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The validators awake at every instant from `S.a r − wAttest S` through one delay after round
    `r + 1`'s action instant. -/
def activeRoundWThroughNext (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (r : Nat) : Finset V :=
  Sched.awakeThroughout ((M.a S.hc S.E.Δ r) - wAttest S) ((M.a S.hc S.E.Δ (r + 1)) + S.E.Δ)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The validators that, at some round `ρ` from `lo` to `hi`, are awake at `ρ`'s action instant
    without having been awake at every instant from one delay before the first cutoff that round
    `ρ`'s grade computation reads. -/
def attestersNotAwakeSinceFirstCutoffIn (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (lo hi : Nat) :
    Finset V :=
  (Finset.Icc lo hi).biUnion fun ρ =>
    Sched.awake ((M.a S.hc S.E.Δ ρ)) \
      Sched.awakeThroughout (M.early S.E S.hc ρ .g2 - S.E.Δ) ((M.a S.hc S.E.Δ ρ))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The validators of `activeRoundWThroughNext S Sched r` that, at no round `ρ` from `r + 2` to
    `r₀ − 1`, were awake at `ρ`'s action instant without having been awake at every instant from one
    delay before `ρ`'s first cutoff to it. -/
def activeRoundWThroughNextCountedAt (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (r r₀ : Nat) :
    Finset V :=
  Restated.activeRoundWThroughNext M S Sched r \
    Restated.attestersNotAwakeSinceFirstCutoffIn M S Sched (r + 2) (r₀ - 1)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- At every round `r₀` from `r + 1` to `r + η_SG + 1`, the validators of
    `activeRoundWThroughNextCountedAt S Sched r r₀` not held by the adversary at the opening of
    round `r₀ + 1` outweigh the adversary at that opening together with everyone else who attested
    in the `η_SG` rounds before `r₀`. -/
def fixedRoundSleepinessCountedW (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (r : Nat) : Prop :=
  ∀ r₀ : Nat, r + 1 ≤ r₀ → r₀ ≤ r + S.hc.η_SG + 1 →
    S.E.electorate.weightOf
        (Sched.adv (M.opening S.E S.hc (r₀ + 1)) ∪
          (Restated.attestersIn M S Sched (r₀ - S.hc.η_SG) (r₀ - 1) \
            (Restated.activeRoundWThroughNextCountedAt M S Sched r r₀ \
              Sched.adv (M.opening S.E S.hc (r₀ + 1)))))
      < S.E.electorate.weightOf
          (Restated.activeRoundWThroughNextCountedAt M S Sched r r₀ \
            Sched.adv (M.opening S.E S.hc (r₀ + 1)))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- One delay after round `r + 1`'s action instant is at or before `b₀`. -/
def periodAfterRound (M : Record.Model V) (S : Setup V) (r : Nat) (b₀ : Int) : Prop :=
  (M.a S.hc S.E.Δ (r + 1)) + S.E.Δ ≤ b₀

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `b₁ + Δ` is at or before the first cutoff that round `r + η_SG + 1`'s grade computation reads. -/
def periodBeforeExpiry (M : Record.Model V) (S : Setup V) (r : Nat) (b₁ : Int) : Prop :=
  b₁ + S.E.Δ ≤ M.early S.E S.hc (r + S.hc.η_SG + 1) .g2

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The validators awake throughout the attester window of some round from `r + 2` to `r + η_SG` and
    not in `activeRoundWThroughNext S Sched r`. -/
def activeOutsideFixedIn (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (r : Nat) : Finset V :=
  (Finset.Icc (r + 2) (r + S.hc.η_SG)).biUnion (Restated.activeRoundW M S Sched) \
    Restated.activeRoundWThroughNext M S Sched r

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Three times the weight of `activeOutsideFixedIn S Sched r` is at most the total weight. -/
def outsideAttestersUnderThird (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (r : Nat) : Prop :=
  3 * S.E.electorate.weightOf (Restated.activeOutsideFixedIn M S Sched r) ≤ S.E.electorate.totalWeight

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- How long the phase's premises are asked again after one healing length:
    `finalityStartupDirect S gap`, plus `3 · gap + timeoutDelay / R` periods, plus
    `finalityPremisesContinueDirect S gap`. -/
noncomputable def liveAgainAfterHealing (M : Record.Model V) (S : Setup V) (gap : Nat) : Int :=
  Restated.finalityStartupDirect M S gap +
    ((3 * gap + S.cfg.timeoutDelay / S.hc.R : Nat) : Int) * (Restated.constants M S).period +
    Restated.finalityPremisesContinueDirect M S gap

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every block that is an ancestor of the stable output of a validator honest through a step `T`
    between `confirmedSettleTime S tE` and round `r`'s action instant, and awake throughout the vote
    window of that step's slot, is an ancestor of the stable output of every validator honest
    through any step at or after `b₀` and awake since the start of round `r + 1`'s attester window. -/
def StablePersistsFromRound (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (r : Nat) (b₀ : Int) : Prop :=
  ∀ (v : V) (T : Nat) (P : Block V),
    Restated.HonestThrough M Sched x T v →
    Restated.confirmedSettleTime M S tE ≤ (x[T].time : Int) →
    (x[T].time : Int) ≤ (M.a S.hc S.E.Δ r) →
    v ∈ activeAtW S Sched (S.E.slotOf (x[T].time : Int)) →
    Block.Preceq P (Restated.Read.stable M x[T][v].st) →
    ∀ (w : V) (j : Nat), Restated.HonestThrough M Sched x j w →
      b₀ ≤ (x[j].time : Int) →
      w ∈ Sched.awakeThroughout ((M.a S.hc S.E.Δ (r + 1)) - wAttest S) (x[j].time : Int) →
      Block.Preceq P (Restated.Read.stable M x[j][w].st)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every `gap` with `gap + 2 ≤ S.cfg.K` there is a `tHeal ≥ 0` such that, in every execution
    meeting the premises listed, with synchrony and catch-up suspended on an asynchronous period
    `[b₀, b₁)` placed by `periodAfterRound` and `periodBeforeExpiry`, and the phase's premises asked
    again on `[tAgain, tSafe]`, the stable output persists from `b₀` on (`StablePersistsFromRound`). -/
def claimStableThroughOneAsyncPeriodStatement (M : Record.Model V) (S : Setup V) (Sched : Schedule V) : Prop :=
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
    Restated.StablePersistsFromRound M S Sched x tAwakeEnd r b₀

end

end DecoupledConsensusModel.Sts.Restated
