import Proofs.Instance.Facts.Assembly
import Proofs.Claims.Restated.ClaimConfirmedAfterHealingHolds
import Proofs.Claims.Restated.ClaimStableLiveAfterHealingHolds
import Proofs.Claims.Restated.ClaimConfirmedIncludedAfterHealingHolds
import Proofs.Claims.Restated.ClaimStableThroughOneAsyncPeriodHolds
import Proofs.Claims.Restated.Claim13bfKitTop
import Proofs.Claims.Restated.ClaimConfirmedGrowsAfterHealingHolds
import Proofs.Claims.Restated.ClaimFinalityLiveAfterHealingKit
import Proofs.Claims.Restated.ClaimStableThroughAsyncPeriodCommonViewAgainHolds
import Model.Conditions.ExecutionHypotheses

/-!
# The end results at the spec's model, in their existential forms

The theorems `…_holds`, the claims' top-level theorems applied to `Model.spec_facts`, and their
per-execution forms `…_holds_perExecution`, both of which state that there is a healing length
`tHeal`. `lean/EndResults.lean` holds `constants_holds` and the explicit forms `…_holds_explicit`,
and its module docstring says how the statements are written.
-/

set_option autoImplicit false
-- The hypotheses under each `∃ tHeal` are named for the reader; the statement never refers to
-- them by name, which the unused-variables linter would report on every one.
set_option linter.unusedVariables false

namespace EndResults

open DecoupledConsensusModel
open DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Restated
open DecoupledConsensusModel.Sts.Record
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- For every `gap` with `gap + 2 ≤ S.cfg.K` there is a `tHeal ≥ 0` such that, at `Model.spec`,
    every execution meeting the premises over a phase `[tGAT, tAwakeEnd]` of length at least
    `tHeal` satisfies `ConfirmedAgreeAfterHealing` and `ConfirmedMonotoneAfterHealing` at
    `tAwakeEnd`. -/
theorem claimConfirmedAfterHealing_holds
    -- ## The objects
    (S : Setup V)
    (Sched : Schedule V)
    -- A number of periods.
    (gap : Nat)
    -- ## The parameter
    -- `gap + 2` is at most `S.cfg.K`, the period of the nonjustifiable heights.
    (hgap : gap + 2 ≤ S.cfg.K)
    -- ## The adversary and the committees
    -- A validator the adversary holds at time `t` it holds at every later time.
    (hmonotone : Sched.MonotoneCorruption)
    -- Every committee is more than half honest through its slot's confirmation time.
    (hhonestComm : HonestCommittees (Model.spec (V := V)) S Sched
      (interface (Model.spec (V := V)) S Sched))
    -- ## The schedule
    -- A validator awake at `t` and not at `t - 1` has `t` a multiple of `S.E.Δ`.
    (hawakeMultiples : AwakeAtMultiples S Sched) :
    -- There is a healing length `tHeal`, not negative, such that:
    ∃ tHeal : Int, 0 ≤ tHeal ∧ ∀
    -- ## The objects
    (x : AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    -- The execution is admitted (`admittedExecution`):
    -- - `SignaturesUnforgeable`: an honest author's sent payload is in the sent log signed by them.
    -- - `IncludedSignaturesUnforgeable`: honest authors' included objects are sent signed by them.
    -- - `DeliveredMessagesWellFormed`: delivered blocks and votes have votes of committee members.
    -- - `DeliveredBlocksHaveParent`: a delivered block's parent is in the receiver's store.
    -- - `BlockRootsCollisionFree`: two ancestors of `blockInLog` blocks sharing a root are equal.
    -- - `HonestRootsNew`: at its proposal time, an honest proposer has no block of its `new_root`.
    -- - `TimeDiverges`: every natural number is at most some `x[i].time`.
    (hadmitted : admittedExecution (Model.spec (V := V)) S Sched x)
    -- The start and the end of the window `[tGAT, tAwakeEnd]`.
    (tGAT tAwakeEnd : Int)
    -- ## The window
    -- The window lasts at least `tHeal`.
    (hlen : tGAT + tHeal ≤ tAwakeEnd)
    -- The window starts at or after `S.E.t_GST`.
    (hGST : S.E.t_GST ≤ tGAT)
    -- ## The adversary and the committees
    -- Up to `tAwakeEnd`, the adversary holds less than one third of the total weight.
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- ## The schedule
    -- From `tGAT` to `tAwakeEnd`, every validator the adversary does not hold is awake.
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    -- From `tAwakeEnd`, voters awake for `wVote S`, not held, outnumber the held and the other
    -- validators the awake rule lets vote.
    (hsleepiness : sleepinessW S Sched tAwakeEnd)
    -- From `tAwakeEnd`, attesters awake for `wAttest S`, not held, outweigh the held and the other
    -- validators the awake rule lets attest.
    (hroundSleepiness : roundSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- From `tAwakeEnd`, committee members awake for `wVote S`, not held, outnumber the other
    -- members the awake rule lets vote or the adversary holds.
    (hcommitteeSleepiness : committeeSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- ## The network
    -- An honest message sent at `t` reaches before `max t S.E.t_GST + S.E.Δ` all awake until then.
    (hsync : SynchronyFromWake (Model.spec (V := V)) S x)
    -- Woken at `t_w`, awake to `max t_w S.E.t_GST + S.E.Δ`, `w` gets prior honest messages by then.
    (hcatchUp : CatchUpOnWake (Model.spec (V := V)) S x)
    -- ## The proposals
    -- Every `gap` periods in the window a round opens with honest first proposers, and recent ones.
    (hopenings : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tGAT tAwakeEnd gap),
    -- ## The conclusion
    -- From `confirmedSettleTime`, honest validators awake for `wVote S` confirm compatible blocks.
    ConfirmedAgreeAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd ∧
    -- From `confirmedSettleTime`, an honest `v` awake for `wVote S` later confirms descendants.
    ConfirmedMonotoneAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd := by
  obtain ⟨tHeal, h0, hall⟩ :=
    DecoupledConsensusModel.Sts.Restated.claimConfirmedAfterHealing_holds Model.spec_facts S Sched
      gap hgap
  refine ⟨tHeal, h0, fun x hadmitted tGAT tAwakeEnd hlen hGST hthird hawake hsleepiness
      hroundSleepiness hcommitteeSleepiness hsync hcatchUp hopenings => ?_⟩
  obtain ⟨hunforgeable, hcarried, hwire, hdeps, hrootInjective, hhonestRootsNew, htime⟩ :=
    hadmitted
  exact hall x tGAT tAwakeEnd hlen hGST hmonotone
      ⟨⟨hunforgeable, hcarried⟩, ⟨hwire, hdeps⟩, ⟨hrootInjective⟩, hhonestRootsNew⟩ hsync
      hawakeMultiples hcatchUp htime hhonestComm hthird hawake hopenings hsleepiness
      hroundSleepiness hcommitteeSleepiness

/-- The theorem `claimConfirmedAfterHealing_holds` with `tHeal` chosen for each execution `x`: `x`
    and each hypothesis naming only `x` and the binders before it come before the colon, ahead of
    the `∃ tHeal`. It follows from `claimConfirmedAfterHealing_holds`, whose `tHeal` serves every
    execution. -/
theorem claimConfirmedAfterHealing_holds_perExecution
    -- ## The objects
    (S : Setup V)
    (Sched : Schedule V)
    -- A number of periods.
    (gap : Nat)
    (x : AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    -- The execution is admitted (`admittedExecution`):
    -- - `SignaturesUnforgeable`: an honest author's sent payload is in the sent log signed by them.
    -- - `IncludedSignaturesUnforgeable`: honest authors' included objects are sent signed by them.
    -- - `DeliveredMessagesWellFormed`: delivered blocks and votes have votes of committee members.
    -- - `DeliveredBlocksHaveParent`: a delivered block's parent is in the receiver's store.
    -- - `BlockRootsCollisionFree`: two ancestors of `blockInLog` blocks sharing a root are equal.
    -- - `HonestRootsNew`: at its proposal time, an honest proposer has no block of its `new_root`.
    -- - `TimeDiverges`: every natural number is at most some `x[i].time`.
    (hadmitted : admittedExecution (Model.spec (V := V)) S Sched x)
    -- ## The parameter
    -- `gap + 2` is at most `S.cfg.K`, the period of the nonjustifiable heights.
    (hgap : gap + 2 ≤ S.cfg.K)
    -- ## The adversary and the committees
    -- A validator the adversary holds at time `t` it holds at every later time.
    (hmonotone : Sched.MonotoneCorruption)
    -- Every committee is more than half honest through its slot's confirmation time.
    (hhonestComm : HonestCommittees (Model.spec (V := V)) S Sched
      (interface (Model.spec (V := V)) S Sched))
    -- ## The schedule
    -- A validator awake at `t` and not at `t - 1` has `t` a multiple of `S.E.Δ`.
    (hawakeMultiples : AwakeAtMultiples S Sched)
    -- ## The network
    -- An honest message sent at `t` reaches before `max t S.E.t_GST + S.E.Δ` all awake until then.
    (hsync : SynchronyFromWake (Model.spec (V := V)) S x)
    -- Woken at `t_w`, awake to `max t_w S.E.t_GST + S.E.Δ`, `w` gets prior honest messages by then.
    (hcatchUp : CatchUpOnWake (Model.spec (V := V)) S x) :
    -- There is a healing length `tHeal`, not negative, such that:
    ∃ tHeal : Int, 0 ≤ tHeal ∧ ∀
    -- ## The objects
    -- The start and the end of the window `[tGAT, tAwakeEnd]`.
    (tGAT tAwakeEnd : Int)
    -- ## The window
    -- The window lasts at least `tHeal`.
    (hlen : tGAT + tHeal ≤ tAwakeEnd)
    -- The window starts at or after `S.E.t_GST`.
    (hGST : S.E.t_GST ≤ tGAT)
    -- ## The adversary and the committees
    -- Up to `tAwakeEnd`, the adversary holds less than one third of the total weight.
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- ## The schedule
    -- From `tGAT` to `tAwakeEnd`, every validator the adversary does not hold is awake.
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    -- From `tAwakeEnd`, voters awake for `wVote S`, not held, outnumber the held and the other
    -- validators the awake rule lets vote.
    (hsleepiness : sleepinessW S Sched tAwakeEnd)
    -- From `tAwakeEnd`, attesters awake for `wAttest S`, not held, outweigh the held and the other
    -- validators the awake rule lets attest.
    (hroundSleepiness : roundSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- From `tAwakeEnd`, committee members awake for `wVote S`, not held, outnumber the other
    -- members the awake rule lets vote or the adversary holds.
    (hcommitteeSleepiness : committeeSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- ## The proposals
    -- Every `gap` periods in the window a round opens with honest first proposers, and recent ones.
    (hopenings : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tGAT tAwakeEnd gap),
    -- ## The conclusion
    -- From `confirmedSettleTime`, honest validators awake for `wVote S` confirm compatible blocks.
    ConfirmedAgreeAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd ∧
    -- From `confirmedSettleTime`, an honest `v` awake for `wVote S` later confirms descendants.
    ConfirmedMonotoneAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd := by
  obtain ⟨tHeal, h0, hall⟩ :=
    EndResults.claimConfirmedAfterHealing_holds S Sched gap hgap hmonotone hhonestComm
      hawakeMultiples
  exact ⟨tHeal, h0, fun tGAT tAwakeEnd hlen hGST hthird hawake hsleepiness hroundSleepiness
    hcommitteeSleepiness hopenings =>
      hall x hadmitted tGAT tAwakeEnd hlen hGST hthird hawake hsleepiness hroundSleepiness
        hcommitteeSleepiness hsync hcatchUp hopenings⟩

/-- For every `gap` with `gap + 2 ≤ S.cfg.K` there is a `tHeal ≥ 0` such that, at `Model.spec`,
    every execution meeting the premises over a phase `[tGAT, tAwakeEnd]` of length at least
    `tHeal` satisfies `StableIncludedAfterHealing` and `StableOnlyExtendsAfterHealing` at
    `tAwakeEnd`, and `StableGrowsAfterHealing` for every `gapP` with which honest awake proposers
    recur from `tAwakeEnd` on. -/
theorem claimStableLiveAfterHealing_holds
    -- ## The objects
    (S : Setup V)
    (Sched : Schedule V)
    -- A number of periods.
    (gap : Nat)
    -- ## The parameter
    -- `gap + 2` is at most `S.cfg.K`, the period of the nonjustifiable heights.
    (hgap : gap + 2 ≤ S.cfg.K)
    -- ## The adversary and the committees
    -- A validator the adversary holds at time `t` it holds at every later time.
    (hmonotone : Sched.MonotoneCorruption)
    -- Every committee is more than half honest through its slot's confirmation time.
    (hhonestComm : HonestCommittees (Model.spec (V := V)) S Sched
      (interface (Model.spec (V := V)) S Sched))
    -- ## The schedule
    -- A validator awake at `t` and not at `t - 1` has `t` a multiple of `S.E.Δ`.
    (hawakeMultiples : AwakeAtMultiples S Sched) :
    -- There is a healing length `tHeal`, not negative, such that:
    ∃ tHeal : Int, 0 ≤ tHeal ∧ ∀
    -- ## The objects
    (x : AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    -- The execution is admitted (`admittedExecution`):
    -- - `SignaturesUnforgeable`: an honest author's sent payload is in the sent log signed by them.
    -- - `IncludedSignaturesUnforgeable`: honest authors' included objects are sent signed by them.
    -- - `DeliveredMessagesWellFormed`: delivered blocks and votes have votes of committee members.
    -- - `DeliveredBlocksHaveParent`: a delivered block's parent is in the receiver's store.
    -- - `BlockRootsCollisionFree`: two ancestors of `blockInLog` blocks sharing a root are equal.
    -- - `HonestRootsNew`: at its proposal time, an honest proposer has no block of its `new_root`.
    -- - `TimeDiverges`: every natural number is at most some `x[i].time`.
    (hadmitted : admittedExecution (Model.spec (V := V)) S Sched x)
    -- The start and the end of the window `[tGAT, tAwakeEnd]`.
    (tGAT tAwakeEnd : Int)
    -- ## The window
    -- The window lasts at least `tHeal`.
    (hlen : tGAT + tHeal ≤ tAwakeEnd)
    -- The window starts at or after `S.E.t_GST`.
    (hGST : S.E.t_GST ≤ tGAT)
    -- ## The adversary and the committees
    -- Up to `tAwakeEnd`, the adversary holds less than one third of the total weight.
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- ## The schedule
    -- From `tGAT` to `tAwakeEnd`, every validator the adversary does not hold is awake.
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    -- From `tAwakeEnd`, voters awake for `wVote S`, not held, outnumber the held and the other
    -- validators the awake rule lets vote.
    (hsleepiness : sleepinessW S Sched tAwakeEnd)
    -- From `tAwakeEnd`, attesters awake for `wAttest S`, not held, outweigh the held and the other
    -- validators the awake rule lets attest.
    (hroundSleepiness : roundSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- From `tAwakeEnd`, committee members awake for `wVote S`, not held, outnumber the other
    -- members the awake rule lets vote or the adversary holds.
    (hcommitteeSleepiness : committeeSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- ## The network
    -- An honest message sent at `t` reaches before `max t S.E.t_GST + S.E.Δ` all awake until then.
    (hsync : SynchronyFromWake (Model.spec (V := V)) S x)
    -- Woken at `t_w`, awake to `max t_w S.E.t_GST + S.E.Δ`, `w` gets prior honest messages by then.
    (hcatchUp : CatchUpOnWake (Model.spec (V := V)) S x)
    -- ## The proposals
    -- Every `gap` periods in the window a round opens with honest first proposers, and recent ones.
    (hopenings : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tGAT tAwakeEnd gap),
    -- ## The conclusion
    -- From `tAwakeEnd`, honest proposals enter the stable outputs of the honest that ran a
    -- confirmation after them.
    StableIncludedAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd ∧
    -- From `tAwakeEnd`, an honest validator's stable output is a descendant of its earlier ones.
    StableOnlyExtendsAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd ∧
    -- If honest awake proposers recur every `gapP` periods from `tAwakeEnd`, stable outputs grow.
    ∀ gapP : Nat, honestAwakeProposersRecurFrom (Model.spec (V := V)) S Sched tAwakeEnd gapP →
      StableGrowsAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd gapP := by
  obtain ⟨tHeal, h0, hall⟩ :=
    DecoupledConsensusModel.Sts.Restated.claimStableLiveAfterHealing_holds Model.spec_facts S Sched
      gap hgap
  refine ⟨tHeal, h0, fun x hadmitted tGAT tAwakeEnd hlen hGST hthird hawake hsleepiness
      hroundSleepiness hcommitteeSleepiness hsync hcatchUp hopenings => ?_⟩
  obtain ⟨hunforgeable, hcarried, hwire, hdeps, hrootInjective, hhonestRootsNew, htime⟩ :=
    hadmitted
  exact hall x tGAT tAwakeEnd hlen hGST hmonotone
      ⟨⟨hunforgeable, hcarried⟩, ⟨hwire, hdeps⟩, ⟨hrootInjective⟩, hhonestRootsNew⟩ hsync
      hawakeMultiples hcatchUp htime hhonestComm hthird hawake hopenings hsleepiness
      hroundSleepiness hcommitteeSleepiness

/-- The theorem `claimStableLiveAfterHealing_holds` with `tHeal` chosen for each execution `x`: `x`
    and each hypothesis naming only `x` and the binders before it come before the colon, ahead of
    the `∃ tHeal`. It follows from `claimStableLiveAfterHealing_holds`, whose `tHeal` serves every
    execution. -/
theorem claimStableLiveAfterHealing_holds_perExecution
    -- ## The objects
    (S : Setup V)
    (Sched : Schedule V)
    -- A number of periods.
    (gap : Nat)
    (x : AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    -- The execution is admitted (`admittedExecution`):
    -- - `SignaturesUnforgeable`: an honest author's sent payload is in the sent log signed by them.
    -- - `IncludedSignaturesUnforgeable`: honest authors' included objects are sent signed by them.
    -- - `DeliveredMessagesWellFormed`: delivered blocks and votes have votes of committee members.
    -- - `DeliveredBlocksHaveParent`: a delivered block's parent is in the receiver's store.
    -- - `BlockRootsCollisionFree`: two ancestors of `blockInLog` blocks sharing a root are equal.
    -- - `HonestRootsNew`: at its proposal time, an honest proposer has no block of its `new_root`.
    -- - `TimeDiverges`: every natural number is at most some `x[i].time`.
    (hadmitted : admittedExecution (Model.spec (V := V)) S Sched x)
    -- ## The parameter
    -- `gap + 2` is at most `S.cfg.K`, the period of the nonjustifiable heights.
    (hgap : gap + 2 ≤ S.cfg.K)
    -- ## The adversary and the committees
    -- A validator the adversary holds at time `t` it holds at every later time.
    (hmonotone : Sched.MonotoneCorruption)
    -- Every committee is more than half honest through its slot's confirmation time.
    (hhonestComm : HonestCommittees (Model.spec (V := V)) S Sched
      (interface (Model.spec (V := V)) S Sched))
    -- ## The schedule
    -- A validator awake at `t` and not at `t - 1` has `t` a multiple of `S.E.Δ`.
    (hawakeMultiples : AwakeAtMultiples S Sched)
    -- ## The network
    -- An honest message sent at `t` reaches before `max t S.E.t_GST + S.E.Δ` all awake until then.
    (hsync : SynchronyFromWake (Model.spec (V := V)) S x)
    -- Woken at `t_w`, awake to `max t_w S.E.t_GST + S.E.Δ`, `w` gets prior honest messages by then.
    (hcatchUp : CatchUpOnWake (Model.spec (V := V)) S x) :
    -- There is a healing length `tHeal`, not negative, such that:
    ∃ tHeal : Int, 0 ≤ tHeal ∧ ∀
    -- ## The objects
    -- The start and the end of the window `[tGAT, tAwakeEnd]`.
    (tGAT tAwakeEnd : Int)
    -- ## The window
    -- The window lasts at least `tHeal`.
    (hlen : tGAT + tHeal ≤ tAwakeEnd)
    -- The window starts at or after `S.E.t_GST`.
    (hGST : S.E.t_GST ≤ tGAT)
    -- ## The adversary and the committees
    -- Up to `tAwakeEnd`, the adversary holds less than one third of the total weight.
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- ## The schedule
    -- From `tGAT` to `tAwakeEnd`, every validator the adversary does not hold is awake.
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    -- From `tAwakeEnd`, voters awake for `wVote S`, not held, outnumber the held and the other
    -- validators the awake rule lets vote.
    (hsleepiness : sleepinessW S Sched tAwakeEnd)
    -- From `tAwakeEnd`, attesters awake for `wAttest S`, not held, outweigh the held and the other
    -- validators the awake rule lets attest.
    (hroundSleepiness : roundSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- From `tAwakeEnd`, committee members awake for `wVote S`, not held, outnumber the other
    -- members the awake rule lets vote or the adversary holds.
    (hcommitteeSleepiness : committeeSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- ## The proposals
    -- Every `gap` periods in the window a round opens with honest first proposers, and recent ones.
    (hopenings : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tGAT tAwakeEnd gap),
    -- ## The conclusion
    -- From `tAwakeEnd`, honest proposals enter the stable outputs of the honest that ran a
    -- confirmation after them.
    StableIncludedAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd ∧
    -- From `tAwakeEnd`, an honest validator's stable output is a descendant of its earlier ones.
    StableOnlyExtendsAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd ∧
    -- If honest awake proposers recur every `gapP` periods from `tAwakeEnd`, stable outputs grow.
    ∀ gapP : Nat, honestAwakeProposersRecurFrom (Model.spec (V := V)) S Sched tAwakeEnd gapP →
      StableGrowsAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd gapP := by
  obtain ⟨tHeal, h0, hall⟩ :=
    EndResults.claimStableLiveAfterHealing_holds S Sched gap hgap hmonotone hhonestComm
      hawakeMultiples
  exact ⟨tHeal, h0, fun tGAT tAwakeEnd hlen hGST hthird hawake hsleepiness hroundSleepiness
    hcommitteeSleepiness hopenings =>
      hall x hadmitted tGAT tAwakeEnd hlen hGST hthird hawake hsleepiness hroundSleepiness
        hcommitteeSleepiness hsync hcatchUp hopenings⟩

/-- For every `gap` with `gap + 2 ≤ S.cfg.K` there is a `tHeal ≥ 0` such that, at `Model.spec`,
    every execution meeting the premises over a phase `[tGAT, tAwakeEnd]` of length at least
    `tHeal` satisfies `ConfirmedIncludedAfterHealing` and `ConfirmedOnlyExtendsAfterHealing` at
    `tAwakeEnd`. -/
theorem claimConfirmedIncludedAfterHealing_holds
    -- ## The objects
    (S : Setup V)
    (Sched : Schedule V)
    -- A number of periods.
    (gap : Nat)
    -- ## The parameter
    -- `gap + 2` is at most `S.cfg.K`, the period of the nonjustifiable heights.
    (hgap : gap + 2 ≤ S.cfg.K)
    -- ## The adversary and the committees
    -- A validator the adversary holds at time `t` it holds at every later time.
    (hmonotone : Sched.MonotoneCorruption)
    -- Every committee is more than half honest through its slot's confirmation time.
    (hhonestComm : HonestCommittees (Model.spec (V := V)) S Sched
      (interface (Model.spec (V := V)) S Sched))
    -- ## The schedule
    -- A validator awake at `t` and not at `t - 1` has `t` a multiple of `S.E.Δ`.
    (hawakeMultiples : AwakeAtMultiples S Sched) :
    -- There is a healing length `tHeal`, not negative, such that:
    ∃ tHeal : Int, 0 ≤ tHeal ∧ ∀
    -- ## The objects
    (x : AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    -- The execution is admitted (`admittedExecution`):
    -- - `SignaturesUnforgeable`: an honest author's sent payload is in the sent log signed by them.
    -- - `IncludedSignaturesUnforgeable`: honest authors' included objects are sent signed by them.
    -- - `DeliveredMessagesWellFormed`: delivered blocks and votes have votes of committee members.
    -- - `DeliveredBlocksHaveParent`: a delivered block's parent is in the receiver's store.
    -- - `BlockRootsCollisionFree`: two ancestors of `blockInLog` blocks sharing a root are equal.
    -- - `HonestRootsNew`: at its proposal time, an honest proposer has no block of its `new_root`.
    -- - `TimeDiverges`: every natural number is at most some `x[i].time`.
    (hadmitted : admittedExecution (Model.spec (V := V)) S Sched x)
    -- The start and the end of the window `[tGAT, tAwakeEnd]`.
    (tGAT tAwakeEnd : Int)
    -- ## The window
    -- The window lasts at least `tHeal`.
    (hlen : tGAT + tHeal ≤ tAwakeEnd)
    -- The window starts at or after `S.E.t_GST`.
    (hGST : S.E.t_GST ≤ tGAT)
    -- ## The adversary and the committees
    -- Up to `tAwakeEnd`, the adversary holds less than one third of the total weight.
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- ## The schedule
    -- From `tGAT` to `tAwakeEnd`, every validator the adversary does not hold is awake.
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    -- From `tAwakeEnd`, voters awake for `wVote S`, not held, outnumber the held and the other
    -- validators the awake rule lets vote.
    (hsleepiness : sleepinessW S Sched tAwakeEnd)
    -- From `tAwakeEnd`, attesters awake for `wAttest S`, not held, outweigh the held and the other
    -- validators the awake rule lets attest.
    (hroundSleepiness : roundSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- From `tAwakeEnd`, committee members awake for `wVote S`, not held, outnumber the other
    -- members the awake rule lets vote or the adversary holds.
    (hcommitteeSleepiness : committeeSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- ## The network
    -- An honest message sent at `t` reaches before `max t S.E.t_GST + S.E.Δ` all awake until then.
    (hsync : SynchronyFromWake (Model.spec (V := V)) S x)
    -- Woken at `t_w`, awake to `max t_w S.E.t_GST + S.E.Δ`, `w` gets prior honest messages by then.
    (hcatchUp : CatchUpOnWake (Model.spec (V := V)) S x)
    -- ## The proposals
    -- Every `gap` periods in the window a round opens with honest first proposers, and recent ones.
    (hopenings : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tGAT tAwakeEnd gap),
    -- ## The conclusion
    -- From `tAwakeEnd`, honest proposals enter the confirmed outputs of the honest that ran a
    -- confirmation after them.
    ConfirmedIncludedAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd ∧
    -- From `tAwakeEnd`, an honest validator's confirmed output is a descendant of its earlier ones.
    ConfirmedOnlyExtendsAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd := by
  obtain ⟨tHeal, h0, hall⟩ :=
    DecoupledConsensusModel.Sts.Restated.claimConfirmedIncludedAfterHealing_holds Model.spec_facts S
      Sched gap hgap
  refine ⟨tHeal, h0, fun x hadmitted tGAT tAwakeEnd hlen hGST hthird hawake hsleepiness
      hroundSleepiness hcommitteeSleepiness hsync hcatchUp hopenings => ?_⟩
  obtain ⟨hunforgeable, hcarried, hwire, hdeps, hrootInjective, hhonestRootsNew, htime⟩ :=
    hadmitted
  exact hall x tGAT tAwakeEnd hlen hGST hmonotone
      ⟨⟨hunforgeable, hcarried⟩, ⟨hwire, hdeps⟩, ⟨hrootInjective⟩, hhonestRootsNew⟩ hsync
      hawakeMultiples hcatchUp htime hhonestComm hthird hawake hopenings hsleepiness
      hroundSleepiness hcommitteeSleepiness

/-- The theorem `claimConfirmedIncludedAfterHealing_holds` with `tHeal` chosen for each execution
    `x`: `x` and each hypothesis naming only `x` and the binders before it come before the colon,
    ahead of the `∃ tHeal`. It follows from `claimConfirmedIncludedAfterHealing_holds`, whose
    `tHeal` serves every execution. -/
theorem claimConfirmedIncludedAfterHealing_holds_perExecution
    -- ## The objects
    (S : Setup V)
    (Sched : Schedule V)
    -- A number of periods.
    (gap : Nat)
    (x : AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    -- The execution is admitted (`admittedExecution`):
    -- - `SignaturesUnforgeable`: an honest author's sent payload is in the sent log signed by them.
    -- - `IncludedSignaturesUnforgeable`: honest authors' included objects are sent signed by them.
    -- - `DeliveredMessagesWellFormed`: delivered blocks and votes have votes of committee members.
    -- - `DeliveredBlocksHaveParent`: a delivered block's parent is in the receiver's store.
    -- - `BlockRootsCollisionFree`: two ancestors of `blockInLog` blocks sharing a root are equal.
    -- - `HonestRootsNew`: at its proposal time, an honest proposer has no block of its `new_root`.
    -- - `TimeDiverges`: every natural number is at most some `x[i].time`.
    (hadmitted : admittedExecution (Model.spec (V := V)) S Sched x)
    -- ## The parameter
    -- `gap + 2` is at most `S.cfg.K`, the period of the nonjustifiable heights.
    (hgap : gap + 2 ≤ S.cfg.K)
    -- ## The adversary and the committees
    -- A validator the adversary holds at time `t` it holds at every later time.
    (hmonotone : Sched.MonotoneCorruption)
    -- Every committee is more than half honest through its slot's confirmation time.
    (hhonestComm : HonestCommittees (Model.spec (V := V)) S Sched
      (interface (Model.spec (V := V)) S Sched))
    -- ## The schedule
    -- A validator awake at `t` and not at `t - 1` has `t` a multiple of `S.E.Δ`.
    (hawakeMultiples : AwakeAtMultiples S Sched)
    -- ## The network
    -- An honest message sent at `t` reaches before `max t S.E.t_GST + S.E.Δ` all awake until then.
    (hsync : SynchronyFromWake (Model.spec (V := V)) S x)
    -- Woken at `t_w`, awake to `max t_w S.E.t_GST + S.E.Δ`, `w` gets prior honest messages by then.
    (hcatchUp : CatchUpOnWake (Model.spec (V := V)) S x) :
    -- There is a healing length `tHeal`, not negative, such that:
    ∃ tHeal : Int, 0 ≤ tHeal ∧ ∀
    -- ## The objects
    -- The start and the end of the window `[tGAT, tAwakeEnd]`.
    (tGAT tAwakeEnd : Int)
    -- ## The window
    -- The window lasts at least `tHeal`.
    (hlen : tGAT + tHeal ≤ tAwakeEnd)
    -- The window starts at or after `S.E.t_GST`.
    (hGST : S.E.t_GST ≤ tGAT)
    -- ## The adversary and the committees
    -- Up to `tAwakeEnd`, the adversary holds less than one third of the total weight.
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- ## The schedule
    -- From `tGAT` to `tAwakeEnd`, every validator the adversary does not hold is awake.
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    -- From `tAwakeEnd`, voters awake for `wVote S`, not held, outnumber the held and the other
    -- validators the awake rule lets vote.
    (hsleepiness : sleepinessW S Sched tAwakeEnd)
    -- From `tAwakeEnd`, attesters awake for `wAttest S`, not held, outweigh the held and the other
    -- validators the awake rule lets attest.
    (hroundSleepiness : roundSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- From `tAwakeEnd`, committee members awake for `wVote S`, not held, outnumber the other
    -- members the awake rule lets vote or the adversary holds.
    (hcommitteeSleepiness : committeeSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- ## The proposals
    -- Every `gap` periods in the window a round opens with honest first proposers, and recent ones.
    (hopenings : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tGAT tAwakeEnd gap),
    -- ## The conclusion
    -- From `tAwakeEnd`, honest proposals enter the confirmed outputs of the honest that ran a
    -- confirmation after them.
    ConfirmedIncludedAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd ∧
    -- From `tAwakeEnd`, an honest validator's confirmed output is a descendant of its earlier ones.
    ConfirmedOnlyExtendsAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd := by
  obtain ⟨tHeal, h0, hall⟩ :=
    EndResults.claimConfirmedIncludedAfterHealing_holds S Sched gap hgap hmonotone hhonestComm
      hawakeMultiples
  exact ⟨tHeal, h0, fun tGAT tAwakeEnd hlen hGST hthird hawake hsleepiness hroundSleepiness
    hcommitteeSleepiness hopenings =>
      hall x hadmitted tGAT tAwakeEnd hlen hGST hthird hawake hsleepiness hroundSleepiness
        hcommitteeSleepiness hsync hcatchUp hopenings⟩

/-- For every `gap` with `gap + 2 ≤ S.cfg.K` there is a `tHeal ≥ 0` such that, at `Model.spec`,
    in every execution meeting the premises, with synchrony and catch-up suspended on an
    asynchronous period `[b₀, b₁)` and the phase's premises asked again on `[tAgain, tSafe]`, the
    stable output persists from `b₀` on. -/
theorem claimStableThroughOneAsyncPeriod_holds
    -- ## The objects
    (S : Setup V)
    (Sched : Schedule V)
    -- A number of periods.
    (gap : Nat)
    -- ## The parameter
    -- `gap + 2` is at most `S.cfg.K`, the period of the nonjustifiable heights.
    (hgap : gap + 2 ≤ S.cfg.K)
    -- ## The adversary and the committees
    -- A validator the adversary holds at time `t` it holds at every later time.
    (hmonotone : Sched.MonotoneCorruption)
    -- Every committee is more than half honest through its slot's confirmation time.
    (hhonestComm : HonestCommittees (Model.spec (V := V)) S Sched
      (interface (Model.spec (V := V)) S Sched))
    -- ## The schedule
    -- A validator awake at `t` and not at `t - 1` has `t` a multiple of `S.E.Δ`.
    (hawakeMultiples : AwakeAtMultiples S Sched) :
    -- There is a healing length `tHeal`, not negative, such that:
    ∃ tHeal : Int, 0 ≤ tHeal ∧ ∀
    -- ## The objects
    (x : AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    -- The execution is admitted (`admittedExecution`):
    -- - `SignaturesUnforgeable`: an honest author's sent payload is in the sent log signed by them.
    -- - `IncludedSignaturesUnforgeable`: honest authors' included objects are sent signed by them.
    -- - `DeliveredMessagesWellFormed`: delivered blocks and votes have votes of committee members.
    -- - `DeliveredBlocksHaveParent`: a delivered block's parent is in the receiver's store.
    -- - `BlockRootsCollisionFree`: two ancestors of `blockInLog` blocks sharing a root are equal.
    -- - `HonestRootsNew`: at its proposal time, an honest proposer has no block of its `new_root`.
    -- - `TimeDiverges`: every natural number is at most some `x[i].time`.
    (hadmitted : admittedExecution (Model.spec (V := V)) S Sched x)
    -- The start and the end of the window `[tGAT, tAwakeEnd]`.
    (tGAT tAwakeEnd : Int)
    -- The start and the end of the asynchronous period `[b₀, b₁)`.
    (b₀ b₁ : Int)
    -- The start and the end of the window `[tAgain, tSafe]`, after the asynchronous period.
    (tAgain tSafe : Int)
    -- The round by whose action time the stable output is taken.
    (r : Nat)
    -- ## The window
    -- The window lasts at least `tHeal`.
    (hlen : tGAT + tHeal ≤ tAwakeEnd)
    -- The window starts at or after `S.E.t_GST`.
    (hGST : S.E.t_GST ≤ tGAT)
    -- ## The adversary and the committees
    -- Up to `tAwakeEnd`, the adversary holds less than one third of the total weight.
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- ## The schedule
    -- From `tGAT` to `tAwakeEnd`, every validator the adversary does not hold is awake.
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    -- From `tAwakeEnd`, voters awake for `wVote S`, not held, outnumber the held and the other
    -- validators the awake rule lets vote.
    (hsleepiness : sleepinessW S Sched tAwakeEnd)
    -- From `tAwakeEnd`, attesters awake for `wAttest S`, not held, outweigh the held and the other
    -- validators the awake rule lets attest.
    (hroundSleepiness : roundSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- From `tAwakeEnd`, committee members awake for `wVote S`, not held, outnumber the other
    -- members the awake rule lets vote or the adversary holds.
    (hcommitteeSleepiness : committeeSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- ## The network
    -- An honest message sent at `t` reaches all awake until `deadlineOutside S b₀ b₁ t` before it.
    (hsync : SynchronyFromWakeOutside (Model.spec (V := V)) S x b₀ b₁)
    -- Woken at `t_w`, awake to `deadlineOutside S b₀ b₁ t_w`, `w` gets prior honest sends by then.
    (hcatchUp : CatchUpOnWakeOutside (Model.spec (V := V)) S x b₀ b₁)
    -- ## The proposals
    -- Every `gap` periods in the window a round opens with honest first proposers, and recent ones.
    (hopenings : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tGAT tAwakeEnd gap)
    -- ## The round `r` and the asynchronous period
    -- Round `r`'s action time is at or after `confirmedSettleTime` of `tAwakeEnd`.
    (hsettle : confirmedSettleTime (Model.spec (V := V)) S tAwakeEnd ≤
      ((Model.spec (V := V)).a S.hc S.E.Δ r))
    -- Round `r + 2`'s action time plus `S.E.Δ` is at most `b₀`.
    (hafterRound : periodAfterRound (Model.spec (V := V)) S (r + 1) b₀)
    -- `b₀` is at most `b₁`.
    (hb₀b₁ : b₀ ≤ b₁)
    -- `b₁ + S.E.Δ` is at most the first cutoff round `r + S.hc.η_SG + 2`'s grade computation reads.
    (hbeforeExpiry : periodBeforeExpiry (Model.spec (V := V)) S (r + 1) b₁)
    -- Those awake from `wAttest S` before round `r + 1`'s action instant to `Δ` after round
    -- `r + 2`'s, not held, outweigh the held and the other validators the awake rule lets attest.
    (hfixedSleepiness : fixedRoundSleepinessCountedW (Model.spec (V := V)) S Sched (r + 1))
    -- The other validators the awake rule lets attest at rounds `r + 3` to `r + S.hc.η_SG + 1`
    -- weigh at most a third of the total.
    (houtsideThird : outsideAttestersUnderThird (Model.spec (V := V)) S Sched (r + 1))
    -- ## The window `[tAgain, tSafe]`
    -- `b₁ + S.E.Δ` is at most `tAgain`.
    (hagain : b₁ + S.E.Δ ≤ tAgain)
    -- `[tAgain, tSafe]` lasts at least `tHeal` plus `liveAgainAfterHealing` of `gap`.
    (hlenAgain : tAgain + (tHeal + liveAgainAfterHealing (Model.spec (V := V)) S gap) ≤ tSafe)
    -- Up to `tSafe`, the adversary holds less than one third of the total weight.
    (hthirdAgain : ∀ t : Int, t ≤ tSafe →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- From `tAgain` to `tSafe`, every validator the adversary does not hold is awake.
    (hawakeAgain : ∀ t : Int, tAgain ≤ t → t ≤ tSafe →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    -- Every `gap` periods in `[tAgain, tSafe]` a round opens with honest proposers and recent ones.
    (hopeningsAgain : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tAgain tSafe gap),
    -- ## The conclusion
    -- Ancestors of an honest stable output by round `r` stay in honest stable outputs from `b₀` on.
    StablePersistsFromRound (Model.spec (V := V)) S Sched x tAwakeEnd r b₀ := by
  obtain ⟨tHeal, h0, hall⟩ :=
    DecoupledConsensusModel.Sts.Restated.claimStableThroughOneAsyncPeriod_holds Model.spec_facts S
      Sched gap hgap
  refine ⟨tHeal, h0, fun x hadmitted tGAT tAwakeEnd b₀ b₁ tAgain tSafe r hlen hGST hthird hawake
      hsleepiness hroundSleepiness hcommitteeSleepiness hsync hcatchUp hopenings hsettle hafterRound
      hb₀b₁ hbeforeExpiry hfixedSleepiness houtsideThird hagain hlenAgain hthirdAgain hawakeAgain
      hopeningsAgain => ?_⟩
  obtain ⟨hunforgeable, hcarried, hwire, hdeps, hrootInjective, hhonestRootsNew, htime⟩ :=
    hadmitted
  exact hall x tGAT tAwakeEnd b₀ b₁ tAgain tSafe r hlen hGST hmonotone
      ⟨⟨hunforgeable, hcarried⟩, ⟨hwire, hdeps⟩, ⟨hrootInjective⟩, hhonestRootsNew⟩ hsync
      hawakeMultiples hcatchUp htime hhonestComm hthird hawake hopenings hsleepiness
      hroundSleepiness hcommitteeSleepiness hsettle hafterRound hb₀b₁ hbeforeExpiry hfixedSleepiness
      houtsideThird hagain hlenAgain hthirdAgain hawakeAgain hopeningsAgain

/-- The theorem `claimStableThroughOneAsyncPeriod_holds` with `tHeal` chosen for each execution `x`:
    `x` and each hypothesis naming only `x` and the binders before it come before the colon, ahead
    of the `∃ tHeal`. It follows from `claimStableThroughOneAsyncPeriod_holds`, whose `tHeal` serves
    every execution. -/
theorem claimStableThroughOneAsyncPeriod_holds_perExecution
    -- ## The objects
    (S : Setup V)
    (Sched : Schedule V)
    -- A number of periods.
    (gap : Nat)
    (x : AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    -- The execution is admitted (`admittedExecution`):
    -- - `SignaturesUnforgeable`: an honest author's sent payload is in the sent log signed by them.
    -- - `IncludedSignaturesUnforgeable`: honest authors' included objects are sent signed by them.
    -- - `DeliveredMessagesWellFormed`: delivered blocks and votes have votes of committee members.
    -- - `DeliveredBlocksHaveParent`: a delivered block's parent is in the receiver's store.
    -- - `BlockRootsCollisionFree`: two ancestors of `blockInLog` blocks sharing a root are equal.
    -- - `HonestRootsNew`: at its proposal time, an honest proposer has no block of its `new_root`.
    -- - `TimeDiverges`: every natural number is at most some `x[i].time`.
    (hadmitted : admittedExecution (Model.spec (V := V)) S Sched x)
    -- ## The parameter
    -- `gap + 2` is at most `S.cfg.K`, the period of the nonjustifiable heights.
    (hgap : gap + 2 ≤ S.cfg.K)
    -- ## The adversary and the committees
    -- A validator the adversary holds at time `t` it holds at every later time.
    (hmonotone : Sched.MonotoneCorruption)
    -- Every committee is more than half honest through its slot's confirmation time.
    (hhonestComm : HonestCommittees (Model.spec (V := V)) S Sched
      (interface (Model.spec (V := V)) S Sched))
    -- ## The schedule
    -- A validator awake at `t` and not at `t - 1` has `t` a multiple of `S.E.Δ`.
    (hawakeMultiples : AwakeAtMultiples S Sched) :
    -- There is a healing length `tHeal`, not negative, such that:
    ∃ tHeal : Int, 0 ≤ tHeal ∧ ∀
    -- ## The objects
    -- The start and the end of the window `[tGAT, tAwakeEnd]`.
    (tGAT tAwakeEnd : Int)
    -- The start and the end of the asynchronous period `[b₀, b₁)`.
    (b₀ b₁ : Int)
    -- The start and the end of the window `[tAgain, tSafe]`, after the asynchronous period.
    (tAgain tSafe : Int)
    -- The round by whose action time the stable output is taken.
    (r : Nat)
    -- ## The window
    -- The window lasts at least `tHeal`.
    (hlen : tGAT + tHeal ≤ tAwakeEnd)
    -- The window starts at or after `S.E.t_GST`.
    (hGST : S.E.t_GST ≤ tGAT)
    -- ## The adversary and the committees
    -- Up to `tAwakeEnd`, the adversary holds less than one third of the total weight.
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- ## The schedule
    -- From `tGAT` to `tAwakeEnd`, every validator the adversary does not hold is awake.
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    -- From `tAwakeEnd`, voters awake for `wVote S`, not held, outnumber the held and the other
    -- validators the awake rule lets vote.
    (hsleepiness : sleepinessW S Sched tAwakeEnd)
    -- From `tAwakeEnd`, attesters awake for `wAttest S`, not held, outweigh the held and the other
    -- validators the awake rule lets attest.
    (hroundSleepiness : roundSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- From `tAwakeEnd`, committee members awake for `wVote S`, not held, outnumber the other
    -- members the awake rule lets vote or the adversary holds.
    (hcommitteeSleepiness : committeeSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- ## The network
    -- An honest message sent at `t` reaches all awake until `deadlineOutside S b₀ b₁ t` before it.
    (hsync : SynchronyFromWakeOutside (Model.spec (V := V)) S x b₀ b₁)
    -- Woken at `t_w`, awake to `deadlineOutside S b₀ b₁ t_w`, `w` gets prior honest sends by then.
    (hcatchUp : CatchUpOnWakeOutside (Model.spec (V := V)) S x b₀ b₁)
    -- ## The proposals
    -- Every `gap` periods in the window a round opens with honest first proposers, and recent ones.
    (hopenings : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tGAT tAwakeEnd gap)
    -- ## The round `r` and the asynchronous period
    -- Round `r`'s action time is at or after `confirmedSettleTime` of `tAwakeEnd`.
    (hsettle : confirmedSettleTime (Model.spec (V := V)) S tAwakeEnd ≤
      ((Model.spec (V := V)).a S.hc S.E.Δ r))
    -- Round `r + 2`'s action time plus `S.E.Δ` is at most `b₀`.
    (hafterRound : periodAfterRound (Model.spec (V := V)) S (r + 1) b₀)
    -- `b₀` is at most `b₁`.
    (hb₀b₁ : b₀ ≤ b₁)
    -- `b₁ + S.E.Δ` is at most the first cutoff round `r + S.hc.η_SG + 2`'s grade computation reads.
    (hbeforeExpiry : periodBeforeExpiry (Model.spec (V := V)) S (r + 1) b₁)
    -- Those awake from `wAttest S` before round `r + 1`'s action instant to `Δ` after round
    -- `r + 2`'s, not held, outweigh the held and the other validators the awake rule lets attest.
    (hfixedSleepiness : fixedRoundSleepinessCountedW (Model.spec (V := V)) S Sched (r + 1))
    -- The other validators the awake rule lets attest at rounds `r + 3` to `r + S.hc.η_SG + 1`
    -- weigh at most a third of the total.
    (houtsideThird : outsideAttestersUnderThird (Model.spec (V := V)) S Sched (r + 1))
    -- ## The window `[tAgain, tSafe]`
    -- `b₁ + S.E.Δ` is at most `tAgain`.
    (hagain : b₁ + S.E.Δ ≤ tAgain)
    -- `[tAgain, tSafe]` lasts at least `tHeal` plus `liveAgainAfterHealing` of `gap`.
    (hlenAgain : tAgain + (tHeal + liveAgainAfterHealing (Model.spec (V := V)) S gap) ≤ tSafe)
    -- Up to `tSafe`, the adversary holds less than one third of the total weight.
    (hthirdAgain : ∀ t : Int, t ≤ tSafe →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- From `tAgain` to `tSafe`, every validator the adversary does not hold is awake.
    (hawakeAgain : ∀ t : Int, tAgain ≤ t → t ≤ tSafe →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    -- Every `gap` periods in `[tAgain, tSafe]` a round opens with honest proposers and recent ones.
    (hopeningsAgain : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tAgain tSafe gap),
    -- ## The conclusion
    -- Ancestors of an honest stable output by round `r` stay in honest stable outputs from `b₀` on.
    StablePersistsFromRound (Model.spec (V := V)) S Sched x tAwakeEnd r b₀ := by
  obtain ⟨tHeal, h0, hall⟩ :=
    EndResults.claimStableThroughOneAsyncPeriod_holds S Sched gap hgap hmonotone hhonestComm
      hawakeMultiples
  exact ⟨tHeal, h0, fun tGAT tAwakeEnd b₀ b₁ tAgain tSafe r hlen hGST hthird hawake hsleepiness
    hroundSleepiness hcommitteeSleepiness hsync hcatchUp hopenings hsettle hafterRound hb₀b₁
    hbeforeExpiry hfixedSleepiness houtsideThird hagain hlenAgain hthirdAgain hawakeAgain
    hopeningsAgain =>
      hall x hadmitted tGAT tAwakeEnd b₀ b₁ tAgain tSafe r hlen hGST hthird hawake hsleepiness
        hroundSleepiness hcommitteeSleepiness hsync hcatchUp hopenings hsettle hafterRound hb₀b₁
        hbeforeExpiry hfixedSleepiness houtsideThird hagain hlenAgain hthirdAgain hawakeAgain
        hopeningsAgain⟩

/-- For every `gap` with `gap + 2 ≤ S.cfg.K` there is a `tHeal ≥ 0` such that, at `Model.spec`,
    in every execution meeting the premises over a phase `[tGAT, tAwakeEnd]` of length at least
    `tHeal`, any two validators honest through any two steps have compatible finalized blocks. -/
theorem claim13bf_holds
    -- ## The objects
    (S : Setup V)
    (Sched : Schedule V)
    -- A number of periods.
    (gap : Nat)
    -- ## The parameter
    -- `gap + 2` is at most `S.cfg.K`, the period of the nonjustifiable heights.
    (hgap : gap + 2 ≤ S.cfg.K)
    -- ## The adversary and the committees
    -- A validator the adversary holds at time `t` it holds at every later time.
    (hmonotone : Sched.MonotoneCorruption)
    -- Every committee is more than half honest through its slot's confirmation time.
    (hhonestComm : HonestCommittees (Model.spec (V := V)) S Sched
      (interface (Model.spec (V := V)) S Sched))
    -- ## The schedule
    -- A validator awake at `t` and not at `t - 1` has `t` a multiple of `S.E.Δ`.
    (hawakeMultiples : AwakeAtMultiples S Sched) :
    -- There is a healing length `tHeal`, not negative, such that:
    ∃ tHeal : Int, 0 ≤ tHeal ∧ ∀
    -- ## The objects
    (x : AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    -- The execution is admitted (`admittedExecution`):
    -- - `SignaturesUnforgeable`: an honest author's sent payload is in the sent log signed by them.
    -- - `IncludedSignaturesUnforgeable`: honest authors' included objects are sent signed by them.
    -- - `DeliveredMessagesWellFormed`: delivered blocks and votes have votes of committee members.
    -- - `DeliveredBlocksHaveParent`: a delivered block's parent is in the receiver's store.
    -- - `BlockRootsCollisionFree`: two ancestors of `blockInLog` blocks sharing a root are equal.
    -- - `HonestRootsNew`: at its proposal time, an honest proposer has no block of its `new_root`.
    -- - `TimeDiverges`: every natural number is at most some `x[i].time`.
    (hadmitted : admittedExecution (Model.spec (V := V)) S Sched x)
    -- The start and the end of the window `[tGAT, tAwakeEnd]`.
    (tGAT tAwakeEnd : Int)
    -- Two validators.
    (v₁ v₂ : V)
    -- Two steps of `x`.
    (i j : Nat)
    -- ## The window
    -- The window lasts at least `tHeal`.
    (hlen : tGAT + tHeal ≤ tAwakeEnd)
    -- The window starts at or after `S.E.t_GST`.
    (hGST : S.E.t_GST ≤ tGAT)
    -- ## The adversary and the committees
    -- Up to `tAwakeEnd`, the adversary holds less than one third of the total weight.
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- ## The schedule
    -- From `tGAT` to `tAwakeEnd`, every validator the adversary does not hold is awake.
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    -- From `tAwakeEnd`, voters awake for `wVote S`, not held, outnumber the held and the other
    -- validators the awake rule lets vote.
    (hsleepiness : sleepinessW S Sched tAwakeEnd)
    -- From `tAwakeEnd`, attesters awake for `wAttest S`, not held, outweigh the held and the other
    -- validators the awake rule lets attest.
    (hroundSleepiness : roundSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- From `tAwakeEnd`, committee members awake for `wVote S`, not held, outnumber the other
    -- members the awake rule lets vote or the adversary holds.
    (hcommitteeSleepiness : committeeSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- ## The network
    -- An honest message sent at `t` reaches before `max t S.E.t_GST + S.E.Δ` all awake until then.
    (hsync : SynchronyFromWake (Model.spec (V := V)) S x)
    -- Woken at `t_w`, awake to `max t_w S.E.t_GST + S.E.Δ`, `w` gets prior honest messages by then.
    (hcatchUp : CatchUpOnWake (Model.spec (V := V)) S x)
    -- ## The proposals
    -- Every `gap` periods in the window a round opens with honest first proposers, and recent ones.
    (hopenings : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tGAT tAwakeEnd gap)
    -- ## The two validators
    -- `v₁` is honest through step `i`: the adversary holds it at no time up to `x[i].time`.
    (hhonest₁ : HonestThrough (Model.spec (V := V)) Sched x i v₁)
    -- `v₂` is honest through step `j`: the adversary holds it at no time up to `x[j].time`.
    (hhonest₂ : HonestThrough (Model.spec (V := V)) Sched x j v₂),
    -- ## The conclusion
    -- The finalized blocks of `v₁` at step `i` and of `v₂` at step `j` are compatible.
    Block.Compatible (Read.finalized (Model.spec (V := V)) x[i][v₁].st)
      (Read.finalized (Model.spec (V := V)) x[j][v₂].st) := by
  obtain ⟨tHeal, h0, hall⟩ :=
    DecoupledConsensusModel.Sts.Restated.claim13bf_holds Model.spec_facts S Sched gap hgap
  refine ⟨tHeal, h0, fun x hadmitted tGAT tAwakeEnd v₁ v₂ i j hlen hGST hthird hawake hsleepiness
      hroundSleepiness hcommitteeSleepiness hsync hcatchUp hopenings hhonest₁ hhonest₂ => ?_⟩
  obtain ⟨hunforgeable, hcarried, hwire, hdeps, hrootInjective, hhonestRootsNew, htime⟩ :=
    hadmitted
  exact hall x tGAT tAwakeEnd hlen hGST hmonotone
      ⟨⟨hunforgeable, hcarried⟩, ⟨hwire, hdeps⟩, ⟨hrootInjective⟩, hhonestRootsNew⟩ hsync
      hawakeMultiples hcatchUp htime hhonestComm hthird hawake hopenings hsleepiness
      hroundSleepiness hcommitteeSleepiness v₁ v₂ i j hhonest₁ hhonest₂

/-- The theorem `claim13bf_holds` with `tHeal` chosen for each execution `x`: `x` and each
    hypothesis naming only `x` and the binders before it come before the colon, ahead of the
    `∃ tHeal`. It follows from `claim13bf_holds`, whose `tHeal` serves every execution. -/
theorem claim13bf_holds_perExecution
    -- ## The objects
    (S : Setup V)
    (Sched : Schedule V)
    -- A number of periods.
    (gap : Nat)
    (x : AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    -- The execution is admitted (`admittedExecution`):
    -- - `SignaturesUnforgeable`: an honest author's sent payload is in the sent log signed by them.
    -- - `IncludedSignaturesUnforgeable`: honest authors' included objects are sent signed by them.
    -- - `DeliveredMessagesWellFormed`: delivered blocks and votes have votes of committee members.
    -- - `DeliveredBlocksHaveParent`: a delivered block's parent is in the receiver's store.
    -- - `BlockRootsCollisionFree`: two ancestors of `blockInLog` blocks sharing a root are equal.
    -- - `HonestRootsNew`: at its proposal time, an honest proposer has no block of its `new_root`.
    -- - `TimeDiverges`: every natural number is at most some `x[i].time`.
    (hadmitted : admittedExecution (Model.spec (V := V)) S Sched x)
    -- ## The parameter
    -- `gap + 2` is at most `S.cfg.K`, the period of the nonjustifiable heights.
    (hgap : gap + 2 ≤ S.cfg.K)
    -- ## The adversary and the committees
    -- A validator the adversary holds at time `t` it holds at every later time.
    (hmonotone : Sched.MonotoneCorruption)
    -- Every committee is more than half honest through its slot's confirmation time.
    (hhonestComm : HonestCommittees (Model.spec (V := V)) S Sched
      (interface (Model.spec (V := V)) S Sched))
    -- ## The schedule
    -- A validator awake at `t` and not at `t - 1` has `t` a multiple of `S.E.Δ`.
    (hawakeMultiples : AwakeAtMultiples S Sched)
    -- ## The network
    -- An honest message sent at `t` reaches before `max t S.E.t_GST + S.E.Δ` all awake until then.
    (hsync : SynchronyFromWake (Model.spec (V := V)) S x)
    -- Woken at `t_w`, awake to `max t_w S.E.t_GST + S.E.Δ`, `w` gets prior honest messages by then.
    (hcatchUp : CatchUpOnWake (Model.spec (V := V)) S x) :
    -- There is a healing length `tHeal`, not negative, such that:
    ∃ tHeal : Int, 0 ≤ tHeal ∧ ∀
    -- ## The objects
    -- The start and the end of the window `[tGAT, tAwakeEnd]`.
    (tGAT tAwakeEnd : Int)
    -- Two validators.
    (v₁ v₂ : V)
    -- Two steps of `x`.
    (i j : Nat)
    -- ## The window
    -- The window lasts at least `tHeal`.
    (hlen : tGAT + tHeal ≤ tAwakeEnd)
    -- The window starts at or after `S.E.t_GST`.
    (hGST : S.E.t_GST ≤ tGAT)
    -- ## The adversary and the committees
    -- Up to `tAwakeEnd`, the adversary holds less than one third of the total weight.
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- ## The schedule
    -- From `tGAT` to `tAwakeEnd`, every validator the adversary does not hold is awake.
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    -- From `tAwakeEnd`, voters awake for `wVote S`, not held, outnumber the held and the other
    -- validators the awake rule lets vote.
    (hsleepiness : sleepinessW S Sched tAwakeEnd)
    -- From `tAwakeEnd`, attesters awake for `wAttest S`, not held, outweigh the held and the other
    -- validators the awake rule lets attest.
    (hroundSleepiness : roundSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- From `tAwakeEnd`, committee members awake for `wVote S`, not held, outnumber the other
    -- members the awake rule lets vote or the adversary holds.
    (hcommitteeSleepiness : committeeSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- ## The proposals
    -- Every `gap` periods in the window a round opens with honest first proposers, and recent ones.
    (hopenings : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tGAT tAwakeEnd gap)
    -- ## The two validators
    -- `v₁` is honest through step `i`: the adversary holds it at no time up to `x[i].time`.
    (hhonest₁ : HonestThrough (Model.spec (V := V)) Sched x i v₁)
    -- `v₂` is honest through step `j`: the adversary holds it at no time up to `x[j].time`.
    (hhonest₂ : HonestThrough (Model.spec (V := V)) Sched x j v₂),
    -- ## The conclusion
    -- The finalized blocks of `v₁` at step `i` and of `v₂` at step `j` are compatible.
    Block.Compatible (Read.finalized (Model.spec (V := V)) x[i][v₁].st)
      (Read.finalized (Model.spec (V := V)) x[j][v₂].st) := by
  obtain ⟨tHeal, h0, hall⟩ :=
    EndResults.claim13bf_holds S Sched gap hgap hmonotone hhonestComm hawakeMultiples
  exact ⟨tHeal, h0, fun tGAT tAwakeEnd v₁ v₂ i j hlen hGST hthird hawake hsleepiness
    hroundSleepiness hcommitteeSleepiness hopenings hhonest₁ hhonest₂ =>
      hall x hadmitted tGAT tAwakeEnd v₁ v₂ i j hlen hGST hthird hawake hsleepiness hroundSleepiness
        hcommitteeSleepiness hsync hcatchUp hopenings hhonest₁ hhonest₂⟩

/-- For every `gap` with `gap + 2 ≤ S.cfg.K` there is a `tHeal ≥ 0` such that, at `Model.spec`,
    every execution meeting the premises over a phase `[tGAT, tAwakeEnd]` of length at least
    `tHeal`, with honest awake proposers recurring within every `gapP` periods from `tAwakeEnd`
    on, satisfies `ConfirmedGrowsAfterHealing`. -/
theorem claimConfirmedGrowsAfterHealing_holds
    -- ## The objects
    (S : Setup V)
    (Sched : Schedule V)
    -- A number of periods.
    (gap : Nat)
    -- ## The parameter
    -- `gap + 2` is at most `S.cfg.K`, the period of the nonjustifiable heights.
    (hgap : gap + 2 ≤ S.cfg.K)
    -- ## The adversary and the committees
    -- A validator the adversary holds at time `t` it holds at every later time.
    (hmonotone : Sched.MonotoneCorruption)
    -- Every committee is more than half honest through its slot's confirmation time.
    (hhonestComm : HonestCommittees (Model.spec (V := V)) S Sched
      (interface (Model.spec (V := V)) S Sched))
    -- ## The schedule
    -- A validator awake at `t` and not at `t - 1` has `t` a multiple of `S.E.Δ`.
    (hawakeMultiples : AwakeAtMultiples S Sched) :
    -- There is a healing length `tHeal`, not negative, such that:
    ∃ tHeal : Int, 0 ≤ tHeal ∧ ∀
    -- ## The objects
    (x : AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    -- The execution is admitted (`admittedExecution`):
    -- - `SignaturesUnforgeable`: an honest author's sent payload is in the sent log signed by them.
    -- - `IncludedSignaturesUnforgeable`: honest authors' included objects are sent signed by them.
    -- - `DeliveredMessagesWellFormed`: delivered blocks and votes have votes of committee members.
    -- - `DeliveredBlocksHaveParent`: a delivered block's parent is in the receiver's store.
    -- - `BlockRootsCollisionFree`: two ancestors of `blockInLog` blocks sharing a root are equal.
    -- - `HonestRootsNew`: at its proposal time, an honest proposer has no block of its `new_root`.
    -- - `TimeDiverges`: every natural number is at most some `x[i].time`.
    (hadmitted : admittedExecution (Model.spec (V := V)) S Sched x)
    -- The start and the end of the window `[tGAT, tAwakeEnd]`.
    (tGAT tAwakeEnd : Int)
    -- A number of periods: honest awake proposers recur within every `gapP` periods.
    (gapP : Nat)
    -- ## The window
    -- The window lasts at least `tHeal`.
    (hlen : tGAT + tHeal ≤ tAwakeEnd)
    -- The window starts at or after `S.E.t_GST`.
    (hGST : S.E.t_GST ≤ tGAT)
    -- ## The adversary and the committees
    -- Up to `tAwakeEnd`, the adversary holds less than one third of the total weight.
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- ## The schedule
    -- From `tGAT` to `tAwakeEnd`, every validator the adversary does not hold is awake.
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    -- From `tAwakeEnd`, voters awake for `wVote S`, not held, outnumber the held and the other
    -- validators the awake rule lets vote.
    (hsleepiness : sleepinessW S Sched tAwakeEnd)
    -- From `tAwakeEnd`, attesters awake for `wAttest S`, not held, outweigh the held and the other
    -- validators the awake rule lets attest.
    (hroundSleepiness : roundSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- From `tAwakeEnd`, committee members awake for `wVote S`, not held, outnumber the other
    -- members the awake rule lets vote or the adversary holds.
    (hcommitteeSleepiness : committeeSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- ## The network
    -- An honest message sent at `t` reaches before `max t S.E.t_GST + S.E.Δ` all awake until then.
    (hsync : SynchronyFromWake (Model.spec (V := V)) S x)
    -- Woken at `t_w`, awake to `max t_w S.E.t_GST + S.E.Δ`, `w` gets prior honest messages by then.
    (hcatchUp : CatchUpOnWake (Model.spec (V := V)) S x)
    -- ## The proposals
    -- Every `gap` periods in the window a round opens with honest first proposers, and recent ones.
    (hopenings : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tGAT tAwakeEnd gap)
    -- Within every `gapP` periods from `tAwakeEnd`, some slot's proposer is honest and awake.
    (hproposers : honestAwakeProposersRecurFrom (Model.spec (V := V)) S Sched tAwakeEnd gapP),
    -- ## The conclusion
    -- From `tAwakeEnd`, honest proposals soon extend all honest confirmed outputs, then join those
    -- of the honest that ran a confirmation.
    ConfirmedGrowsAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd gapP := by
  obtain ⟨tHeal, h0, hall⟩ :=
    DecoupledConsensusModel.Sts.Restated.claimConfirmedGrowsAfterHealing_holds Model.spec_facts S
      Sched gap hgap
  refine ⟨tHeal, h0, fun x hadmitted tGAT tAwakeEnd gapP hlen hGST hthird hawake hsleepiness
      hroundSleepiness hcommitteeSleepiness hsync hcatchUp hopenings hproposers => ?_⟩
  obtain ⟨hunforgeable, hcarried, hwire, hdeps, hrootInjective, hhonestRootsNew, htime⟩ :=
    hadmitted
  exact hall x tGAT tAwakeEnd gapP hlen hGST hmonotone
      ⟨⟨hunforgeable, hcarried⟩, ⟨hwire, hdeps⟩, ⟨hrootInjective⟩, hhonestRootsNew⟩ hsync
      hawakeMultiples hcatchUp htime hhonestComm hthird hawake hopenings hsleepiness
      hroundSleepiness hcommitteeSleepiness hproposers

/-- The theorem `claimConfirmedGrowsAfterHealing_holds` with `tHeal` chosen for each execution `x`:
    `x` and each hypothesis naming only `x` and the binders before it come before the colon, ahead
    of the `∃ tHeal`. It follows from `claimConfirmedGrowsAfterHealing_holds`, whose `tHeal` serves
    every execution. -/
theorem claimConfirmedGrowsAfterHealing_holds_perExecution
    -- ## The objects
    (S : Setup V)
    (Sched : Schedule V)
    -- A number of periods.
    (gap : Nat)
    (x : AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    -- The execution is admitted (`admittedExecution`):
    -- - `SignaturesUnforgeable`: an honest author's sent payload is in the sent log signed by them.
    -- - `IncludedSignaturesUnforgeable`: honest authors' included objects are sent signed by them.
    -- - `DeliveredMessagesWellFormed`: delivered blocks and votes have votes of committee members.
    -- - `DeliveredBlocksHaveParent`: a delivered block's parent is in the receiver's store.
    -- - `BlockRootsCollisionFree`: two ancestors of `blockInLog` blocks sharing a root are equal.
    -- - `HonestRootsNew`: at its proposal time, an honest proposer has no block of its `new_root`.
    -- - `TimeDiverges`: every natural number is at most some `x[i].time`.
    (hadmitted : admittedExecution (Model.spec (V := V)) S Sched x)
    -- ## The parameter
    -- `gap + 2` is at most `S.cfg.K`, the period of the nonjustifiable heights.
    (hgap : gap + 2 ≤ S.cfg.K)
    -- ## The adversary and the committees
    -- A validator the adversary holds at time `t` it holds at every later time.
    (hmonotone : Sched.MonotoneCorruption)
    -- Every committee is more than half honest through its slot's confirmation time.
    (hhonestComm : HonestCommittees (Model.spec (V := V)) S Sched
      (interface (Model.spec (V := V)) S Sched))
    -- ## The schedule
    -- A validator awake at `t` and not at `t - 1` has `t` a multiple of `S.E.Δ`.
    (hawakeMultiples : AwakeAtMultiples S Sched)
    -- ## The network
    -- An honest message sent at `t` reaches before `max t S.E.t_GST + S.E.Δ` all awake until then.
    (hsync : SynchronyFromWake (Model.spec (V := V)) S x)
    -- Woken at `t_w`, awake to `max t_w S.E.t_GST + S.E.Δ`, `w` gets prior honest messages by then.
    (hcatchUp : CatchUpOnWake (Model.spec (V := V)) S x) :
    -- There is a healing length `tHeal`, not negative, such that:
    ∃ tHeal : Int, 0 ≤ tHeal ∧ ∀
    -- ## The objects
    -- The start and the end of the window `[tGAT, tAwakeEnd]`.
    (tGAT tAwakeEnd : Int)
    -- A number of periods: honest awake proposers recur within every `gapP` periods.
    (gapP : Nat)
    -- ## The window
    -- The window lasts at least `tHeal`.
    (hlen : tGAT + tHeal ≤ tAwakeEnd)
    -- The window starts at or after `S.E.t_GST`.
    (hGST : S.E.t_GST ≤ tGAT)
    -- ## The adversary and the committees
    -- Up to `tAwakeEnd`, the adversary holds less than one third of the total weight.
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- ## The schedule
    -- From `tGAT` to `tAwakeEnd`, every validator the adversary does not hold is awake.
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    -- From `tAwakeEnd`, voters awake for `wVote S`, not held, outnumber the held and the other
    -- validators the awake rule lets vote.
    (hsleepiness : sleepinessW S Sched tAwakeEnd)
    -- From `tAwakeEnd`, attesters awake for `wAttest S`, not held, outweigh the held and the other
    -- validators the awake rule lets attest.
    (hroundSleepiness : roundSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- From `tAwakeEnd`, committee members awake for `wVote S`, not held, outnumber the other
    -- members the awake rule lets vote or the adversary holds.
    (hcommitteeSleepiness : committeeSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- ## The proposals
    -- Every `gap` periods in the window a round opens with honest first proposers, and recent ones.
    (hopenings : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tGAT tAwakeEnd gap)
    -- Within every `gapP` periods from `tAwakeEnd`, some slot's proposer is honest and awake.
    (hproposers : honestAwakeProposersRecurFrom (Model.spec (V := V)) S Sched tAwakeEnd gapP),
    -- ## The conclusion
    -- From `tAwakeEnd`, honest proposals soon extend all honest confirmed outputs, then join those
    -- of the honest that ran a confirmation.
    ConfirmedGrowsAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd gapP := by
  obtain ⟨tHeal, h0, hall⟩ :=
    EndResults.claimConfirmedGrowsAfterHealing_holds S Sched gap hgap hmonotone hhonestComm
      hawakeMultiples
  exact ⟨tHeal, h0, fun tGAT tAwakeEnd gapP hlen hGST hthird hawake hsleepiness hroundSleepiness
    hcommitteeSleepiness hopenings hproposers =>
      hall x hadmitted tGAT tAwakeEnd gapP hlen hGST hthird hawake hsleepiness hroundSleepiness
        hcommitteeSleepiness hsync hcatchUp hopenings hproposers⟩

/-- For every `gap` with `gap + 2 ≤ S.cfg.K` there is a `tHeal ≥ 0` such that, at `Model.spec`,
    every execution meeting the premises over a phase `[tGAT, tAwakeEnd]` of length at least
    `tHeal`, with the adversary bound, the awake premise and the proposer recurrence continued to
    `tLive`, satisfies `FinalityIncludedAfterHealing` and `FinalityGrowsAfterHealing`. -/
theorem claimFinalityLiveAfterHealing_holds
    -- ## The objects
    (S : Setup V)
    (Sched : Schedule V)
    -- A number of periods.
    (gap : Nat)
    -- ## The parameter
    -- `gap + 2` is at most `S.cfg.K`, the period of the nonjustifiable heights.
    (hgap : gap + 2 ≤ S.cfg.K)
    -- ## The adversary and the committees
    -- A validator the adversary holds at time `t` it holds at every later time.
    (hmonotone : Sched.MonotoneCorruption)
    -- Every committee is more than half honest through its slot's confirmation time.
    (hhonestComm : HonestCommittees (Model.spec (V := V)) S Sched
      (interface (Model.spec (V := V)) S Sched))
    -- ## The schedule
    -- A validator awake at `t` and not at `t - 1` has `t` a multiple of `S.E.Δ`.
    (hawakeMultiples : AwakeAtMultiples S Sched) :
    -- There is a healing length `tHeal`, not negative, such that:
    ∃ tHeal : Int, 0 ≤ tHeal ∧ ∀
    -- ## The objects
    (x : AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    -- The execution is admitted (`admittedExecution`):
    -- - `SignaturesUnforgeable`: an honest author's sent payload is in the sent log signed by them.
    -- - `IncludedSignaturesUnforgeable`: honest authors' included objects are sent signed by them.
    -- - `DeliveredMessagesWellFormed`: delivered blocks and votes have votes of committee members.
    -- - `DeliveredBlocksHaveParent`: a delivered block's parent is in the receiver's store.
    -- - `BlockRootsCollisionFree`: two ancestors of `blockInLog` blocks sharing a root are equal.
    -- - `HonestRootsNew`: at its proposal time, an honest proposer has no block of its `new_root`.
    -- - `TimeDiverges`: every natural number is at most some `x[i].time`.
    (hadmitted : admittedExecution (Model.spec (V := V)) S Sched x)
    -- The start and the end of the window `[tGAT, tAwakeEnd]`.
    (tGAT tAwakeEnd : Int)
    -- The time up to which the adversary bound, the awake premise and the openings continue.
    (tLive : Int)
    -- ## The window
    -- The window lasts at least `tHeal`.
    (hlen : tGAT + tHeal ≤ tAwakeEnd)
    -- `tAwakeEnd` is at most `tLive`.
    (hlive : tAwakeEnd ≤ tLive)
    -- The window starts at or after `S.E.t_GST`.
    (hGST : S.E.t_GST ≤ tGAT)
    -- ## The adversary and the committees
    -- Up to `tLive`, the adversary holds less than one third of the total weight.
    (hthird : ∀ t : Int, t ≤ tLive →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- ## The schedule
    -- From `tGAT` to `tLive`, every validator the adversary does not hold is awake.
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tLive → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    -- From `tAwakeEnd`, voters awake for `wVote S`, not held, outnumber the held and the other
    -- validators the awake rule lets vote.
    (hsleepiness : sleepinessW S Sched tAwakeEnd)
    -- From `tAwakeEnd`, attesters awake for `wAttest S`, not held, outweigh the held and the other
    -- validators the awake rule lets attest.
    (hroundSleepiness : roundSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- From `tAwakeEnd`, committee members awake for `wVote S`, not held, outnumber the other
    -- members the awake rule lets vote or the adversary holds.
    (hcommitteeSleepiness : committeeSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- ## The network
    -- An honest message sent at `t` reaches before `max t S.E.t_GST + S.E.Δ` all awake until then.
    (hsync : SynchronyFromWake (Model.spec (V := V)) S x)
    -- Awake honest ones finalized `⪯ B` hold from `tGAT + S.E.Δ` each `B` honestly held by `tGAT`.
    (hcommonView : CommonViewOfFinalizedDescendantsAt (Model.spec (V := V)) S Sched x tGAT)
    -- ## The proposals
    -- Every `gap` periods in `[tGAT, tLive]` a round opens with honest proposers and recent ones.
    (hopenings : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tGAT tLive gap),
    -- ## The conclusion
    -- Honest proposals in the liveness window are finalized by honest validators after a deadline.
    FinalityIncludedAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd tLive gap ∧
    -- In the liveness window, honest proposals extend honest finalized blocks, then are finalized.
    FinalityGrowsAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd tLive gap := by
  obtain ⟨tHeal, h0, hall⟩ :=
    DecoupledConsensusModel.Sts.Restated.claimFinalityLiveAfterHealing_holds Model.spec_facts S
      Sched gap hgap
  refine ⟨tHeal, h0, fun x hadmitted tGAT tAwakeEnd tLive hlen hlive hGST hthird hawake hsleepiness
      hroundSleepiness hcommitteeSleepiness hsync hcommonView hopenings => ?_⟩
  obtain ⟨hunforgeable, hcarried, hwire, hdeps, hrootInjective, hhonestRootsNew, htime⟩ :=
    hadmitted
  exact hall x tGAT tAwakeEnd tLive hlen hlive hGST hmonotone
      ⟨⟨hunforgeable, hcarried⟩, ⟨hwire, hdeps⟩, ⟨hrootInjective⟩, hhonestRootsNew⟩ hsync
      hawakeMultiples hcommonView htime hhonestComm hthird hawake hopenings hsleepiness
      hroundSleepiness hcommitteeSleepiness

/-- The theorem `claimFinalityLiveAfterHealing_holds` with `tHeal` chosen for each execution `x`:
    `x` and each hypothesis naming only `x` and the binders before it come before the colon, ahead
    of the `∃ tHeal`. It follows from `claimFinalityLiveAfterHealing_holds`, whose `tHeal` serves
    every execution. -/
theorem claimFinalityLiveAfterHealing_holds_perExecution
    -- ## The objects
    (S : Setup V)
    (Sched : Schedule V)
    -- A number of periods.
    (gap : Nat)
    (x : AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    -- The execution is admitted (`admittedExecution`):
    -- - `SignaturesUnforgeable`: an honest author's sent payload is in the sent log signed by them.
    -- - `IncludedSignaturesUnforgeable`: honest authors' included objects are sent signed by them.
    -- - `DeliveredMessagesWellFormed`: delivered blocks and votes have votes of committee members.
    -- - `DeliveredBlocksHaveParent`: a delivered block's parent is in the receiver's store.
    -- - `BlockRootsCollisionFree`: two ancestors of `blockInLog` blocks sharing a root are equal.
    -- - `HonestRootsNew`: at its proposal time, an honest proposer has no block of its `new_root`.
    -- - `TimeDiverges`: every natural number is at most some `x[i].time`.
    (hadmitted : admittedExecution (Model.spec (V := V)) S Sched x)
    -- ## The parameter
    -- `gap + 2` is at most `S.cfg.K`, the period of the nonjustifiable heights.
    (hgap : gap + 2 ≤ S.cfg.K)
    -- ## The adversary and the committees
    -- A validator the adversary holds at time `t` it holds at every later time.
    (hmonotone : Sched.MonotoneCorruption)
    -- Every committee is more than half honest through its slot's confirmation time.
    (hhonestComm : HonestCommittees (Model.spec (V := V)) S Sched
      (interface (Model.spec (V := V)) S Sched))
    -- ## The schedule
    -- A validator awake at `t` and not at `t - 1` has `t` a multiple of `S.E.Δ`.
    (hawakeMultiples : AwakeAtMultiples S Sched)
    -- ## The network
    -- An honest message sent at `t` reaches before `max t S.E.t_GST + S.E.Δ` all awake until then.
    (hsync : SynchronyFromWake (Model.spec (V := V)) S x) :
    -- There is a healing length `tHeal`, not negative, such that:
    ∃ tHeal : Int, 0 ≤ tHeal ∧ ∀
    -- ## The objects
    -- The start and the end of the window `[tGAT, tAwakeEnd]`.
    (tGAT tAwakeEnd : Int)
    -- The time up to which the adversary bound, the awake premise and the openings continue.
    (tLive : Int)
    -- ## The window
    -- The window lasts at least `tHeal`.
    (hlen : tGAT + tHeal ≤ tAwakeEnd)
    -- `tAwakeEnd` is at most `tLive`.
    (hlive : tAwakeEnd ≤ tLive)
    -- The window starts at or after `S.E.t_GST`.
    (hGST : S.E.t_GST ≤ tGAT)
    -- ## The adversary and the committees
    -- Up to `tLive`, the adversary holds less than one third of the total weight.
    (hthird : ∀ t : Int, t ≤ tLive →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- ## The schedule
    -- From `tGAT` to `tLive`, every validator the adversary does not hold is awake.
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tLive → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    -- From `tAwakeEnd`, voters awake for `wVote S`, not held, outnumber the held and the other
    -- validators the awake rule lets vote.
    (hsleepiness : sleepinessW S Sched tAwakeEnd)
    -- From `tAwakeEnd`, attesters awake for `wAttest S`, not held, outweigh the held and the other
    -- validators the awake rule lets attest.
    (hroundSleepiness : roundSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- From `tAwakeEnd`, committee members awake for `wVote S`, not held, outnumber the other
    -- members the awake rule lets vote or the adversary holds.
    (hcommitteeSleepiness : committeeSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- ## The network
    -- Awake honest ones finalized `⪯ B` hold from `tGAT + S.E.Δ` each `B` honestly held by `tGAT`.
    (hcommonView : CommonViewOfFinalizedDescendantsAt (Model.spec (V := V)) S Sched x tGAT)
    -- ## The proposals
    -- Every `gap` periods in `[tGAT, tLive]` a round opens with honest proposers and recent ones.
    (hopenings : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tGAT tLive gap),
    -- ## The conclusion
    -- Honest proposals in the liveness window are finalized by honest validators after a deadline.
    FinalityIncludedAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd tLive gap ∧
    -- In the liveness window, honest proposals extend honest finalized blocks, then are finalized.
    FinalityGrowsAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd tLive gap := by
  obtain ⟨tHeal, h0, hall⟩ :=
    EndResults.claimFinalityLiveAfterHealing_holds S Sched gap hgap hmonotone hhonestComm
      hawakeMultiples
  exact ⟨tHeal, h0, fun tGAT tAwakeEnd tLive hlen hlive hGST hthird hawake hsleepiness
    hroundSleepiness hcommitteeSleepiness hcommonView hopenings =>
      hall x hadmitted tGAT tAwakeEnd tLive hlen hlive hGST hthird hawake hsleepiness
        hroundSleepiness hcommitteeSleepiness hsync hcommonView hopenings⟩

/-- For every `gap` with `gap + 2 ≤ S.cfg.K` there is a `tHeal ≥ 0` such that, at `Model.spec`,
    in every execution meeting the premises, with synchrony and catch-up suspended on an
    asynchronous period `[b₀, b₁)`, the phase's premises asked again on `[tAgain, tSafe]`, and
    `CommonViewAtGAT` at `tAgain`, the stable output persists from `b₀` on. -/
theorem claimStableThroughOneAsyncPeriodCommonViewAgain_holds
    -- ## The objects
    (S : Setup V)
    (Sched : Schedule V)
    -- A number of periods.
    (gap : Nat)
    -- ## The parameter
    -- `gap + 2` is at most `S.cfg.K`, the period of the nonjustifiable heights.
    (hgap : gap + 2 ≤ S.cfg.K)
    -- ## The adversary and the committees
    -- A validator the adversary holds at time `t` it holds at every later time.
    (hmonotone : Sched.MonotoneCorruption)
    -- Every committee is more than half honest through its slot's confirmation time.
    (hhonestComm : HonestCommittees (Model.spec (V := V)) S Sched
      (interface (Model.spec (V := V)) S Sched))
    -- ## The schedule
    -- A validator awake at `t` and not at `t - 1` has `t` a multiple of `S.E.Δ`.
    (hawakeMultiples : AwakeAtMultiples S Sched) :
    -- There is a healing length `tHeal`, not negative, such that:
    ∃ tHeal : Int, 0 ≤ tHeal ∧ ∀
    -- ## The objects
    (x : AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    -- The execution is admitted (`admittedExecution`):
    -- - `SignaturesUnforgeable`: an honest author's sent payload is in the sent log signed by them.
    -- - `IncludedSignaturesUnforgeable`: honest authors' included objects are sent signed by them.
    -- - `DeliveredMessagesWellFormed`: delivered blocks and votes have votes of committee members.
    -- - `DeliveredBlocksHaveParent`: a delivered block's parent is in the receiver's store.
    -- - `BlockRootsCollisionFree`: two ancestors of `blockInLog` blocks sharing a root are equal.
    -- - `HonestRootsNew`: at its proposal time, an honest proposer has no block of its `new_root`.
    -- - `TimeDiverges`: every natural number is at most some `x[i].time`.
    (hadmitted : admittedExecution (Model.spec (V := V)) S Sched x)
    -- The start and the end of the window `[tGAT, tAwakeEnd]`.
    (tGAT tAwakeEnd : Int)
    -- The start and the end of the asynchronous period `[b₀, b₁)`.
    (b₀ b₁ : Int)
    -- The start and the end of the window `[tAgain, tSafe]`, after the asynchronous period.
    (tAgain tSafe : Int)
    -- The round by whose action time the stable output is taken.
    (r : Nat)
    -- ## The window
    -- The window lasts at least `tHeal`.
    (hlen : tGAT + tHeal ≤ tAwakeEnd)
    -- The window starts at or after `S.E.t_GST`.
    (hGST : S.E.t_GST ≤ tGAT)
    -- ## The adversary and the committees
    -- Up to `tAwakeEnd`, the adversary holds less than one third of the total weight.
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- ## The schedule
    -- From `tGAT` to `tAwakeEnd`, every validator the adversary does not hold is awake.
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    -- From `tAwakeEnd`, voters awake for `wVote S`, not held, outnumber the held and the other
    -- validators the awake rule lets vote.
    (hsleepiness : sleepinessW S Sched tAwakeEnd)
    -- From `tAwakeEnd`, attesters awake for `wAttest S`, not held, outweigh the held and the other
    -- validators the awake rule lets attest.
    (hroundSleepiness : roundSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- From `tAwakeEnd`, committee members awake for `wVote S`, not held, outnumber the other
    -- members the awake rule lets vote or the adversary holds.
    (hcommitteeSleepiness : committeeSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- ## The network
    -- An honest message sent at `t` reaches all awake until `deadlineOutside S b₀ b₁ t` before it.
    (hsync : SynchronyFromWakeOutside (Model.spec (V := V)) S x b₀ b₁)
    -- Woken at `t_w`, awake to `deadlineOutside S b₀ b₁ t_w`, `w` gets prior honest sends by then.
    (hcatchUp : CatchUpOnWakeOutside (Model.spec (V := V)) S x b₀ b₁)
    -- Blocks honest ones held by `tGAT` are held from `tGAT + S.E.Δ` by awake honest ones.
    (hcommonView : CommonViewAtGAT (Model.spec (V := V)) S Sched x tGAT)
    -- ## The proposals
    -- Every `gap` periods in the window a round opens with honest first proposers, and recent ones.
    (hopenings : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tGAT tAwakeEnd gap)
    -- ## The round `r` and the asynchronous period
    -- Round `r`'s action time is at or after `confirmedSettleTime` of `tAwakeEnd`.
    (hsettle : confirmedSettleTime (Model.spec (V := V)) S tAwakeEnd ≤
      ((Model.spec (V := V)).a S.hc S.E.Δ r))
    -- Round `r + 2`'s action time plus `S.E.Δ` is at most `b₀`.
    (hafterRound : periodAfterRound (Model.spec (V := V)) S (r + 1) b₀)
    -- `b₀` is at most `b₁`.
    (hb₀b₁ : b₀ ≤ b₁)
    -- `b₁ + S.E.Δ` is at most the first cutoff round `r + S.hc.η_SG + 2`'s grade computation reads.
    (hbeforeExpiry : periodBeforeExpiry (Model.spec (V := V)) S (r + 1) b₁)
    -- Those awake from `wAttest S` before round `r + 1`'s action instant to `Δ` after round
    -- `r + 2`'s, not held, outweigh the held and the other validators the awake rule lets attest.
    (hfixedSleepiness : fixedRoundSleepinessCountedW (Model.spec (V := V)) S Sched (r + 1))
    -- The other validators the awake rule lets attest at rounds `r + 3` to `r + S.hc.η_SG + 1`
    -- weigh at most a third of the total.
    (houtsideThird : outsideAttestersUnderThird (Model.spec (V := V)) S Sched (r + 1))
    -- ## The window `[tAgain, tSafe]`
    -- `b₁ + S.E.Δ` is at most `tAgain`.
    (hagain : b₁ + S.E.Δ ≤ tAgain)
    -- `[tAgain, tSafe]` lasts at least `tHeal` plus `liveAgainAfterHealing` of `gap`.
    (hlenAgain : tAgain + (tHeal + liveAgainAfterHealing (Model.spec (V := V)) S gap) ≤ tSafe)
    -- Up to `tSafe`, the adversary holds less than one third of the total weight.
    (hthirdAgain : ∀ t : Int, t ≤ tSafe →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- From `tAgain` to `tSafe`, every validator the adversary does not hold is awake.
    (hawakeAgain : ∀ t : Int, tAgain ≤ t → t ≤ tSafe →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    -- Every `gap` periods in `[tAgain, tSafe]` a round opens with honest proposers and recent ones.
    (hopeningsAgain : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tAgain tSafe gap)
    -- Blocks honest ones held by `tAgain` are held from `tAgain + S.E.Δ` by awake honest ones.
    (hcommonViewAgain : CommonViewAtGAT (Model.spec (V := V)) S Sched x tAgain),
    -- ## The conclusion
    -- Ancestors of an honest stable output by round `r` stay in honest stable outputs from `b₀` on.
    StablePersistsFromRound (Model.spec (V := V)) S Sched x tAwakeEnd r b₀ := by
  obtain ⟨tHeal, h0, hall⟩ :=
    DecoupledConsensusModel.Sts.Restated.claimStableThroughOneAsyncPeriodCommonViewAgain_holds
      Model.spec_facts S Sched gap hgap
  refine ⟨tHeal, h0, fun x hadmitted tGAT tAwakeEnd b₀ b₁ tAgain tSafe r hlen hGST hthird hawake
      hsleepiness hroundSleepiness hcommitteeSleepiness hsync hcatchUp hcommonView hopenings hsettle
      hafterRound hb₀b₁ hbeforeExpiry hfixedSleepiness houtsideThird hagain hlenAgain hthirdAgain
      hawakeAgain hopeningsAgain hcommonViewAgain => ?_⟩
  obtain ⟨hunforgeable, hcarried, hwire, hdeps, hrootInjective, hhonestRootsNew, htime⟩ :=
    hadmitted
  exact hall x tGAT tAwakeEnd b₀ b₁ tAgain tSafe r hlen hGST hmonotone
      ⟨⟨hunforgeable, hcarried⟩, ⟨hwire, hdeps⟩, ⟨hrootInjective⟩, hhonestRootsNew⟩ hsync
      hawakeMultiples hcatchUp hcommonView htime hhonestComm hthird hawake hopenings hsleepiness
      hroundSleepiness hcommitteeSleepiness hsettle hafterRound hb₀b₁ hbeforeExpiry hfixedSleepiness
      houtsideThird hagain hlenAgain hthirdAgain hawakeAgain hopeningsAgain hcommonViewAgain

/-- The theorem `claimStableThroughOneAsyncPeriodCommonViewAgain_holds` with `tHeal` chosen for each
    execution `x`: `x` and each hypothesis naming only `x` and the binders before it come before the
    colon, ahead of the `∃ tHeal`. It follows from
    `claimStableThroughOneAsyncPeriodCommonViewAgain_holds`, whose `tHeal` serves every
    execution. -/
theorem claimStableThroughOneAsyncPeriodCommonViewAgain_holds_perExecution
    -- ## The objects
    (S : Setup V)
    (Sched : Schedule V)
    -- A number of periods.
    (gap : Nat)
    (x : AtomicExec (protocolOf (Model.spec (V := V)) S) Sched)
    -- The execution is admitted (`admittedExecution`):
    -- - `SignaturesUnforgeable`: an honest author's sent payload is in the sent log signed by them.
    -- - `IncludedSignaturesUnforgeable`: honest authors' included objects are sent signed by them.
    -- - `DeliveredMessagesWellFormed`: delivered blocks and votes have votes of committee members.
    -- - `DeliveredBlocksHaveParent`: a delivered block's parent is in the receiver's store.
    -- - `BlockRootsCollisionFree`: two ancestors of `blockInLog` blocks sharing a root are equal.
    -- - `HonestRootsNew`: at its proposal time, an honest proposer has no block of its `new_root`.
    -- - `TimeDiverges`: every natural number is at most some `x[i].time`.
    (hadmitted : admittedExecution (Model.spec (V := V)) S Sched x)
    -- ## The parameter
    -- `gap + 2` is at most `S.cfg.K`, the period of the nonjustifiable heights.
    (hgap : gap + 2 ≤ S.cfg.K)
    -- ## The adversary and the committees
    -- A validator the adversary holds at time `t` it holds at every later time.
    (hmonotone : Sched.MonotoneCorruption)
    -- Every committee is more than half honest through its slot's confirmation time.
    (hhonestComm : HonestCommittees (Model.spec (V := V)) S Sched
      (interface (Model.spec (V := V)) S Sched))
    -- ## The schedule
    -- A validator awake at `t` and not at `t - 1` has `t` a multiple of `S.E.Δ`.
    (hawakeMultiples : AwakeAtMultiples S Sched) :
    -- There is a healing length `tHeal`, not negative, such that:
    ∃ tHeal : Int, 0 ≤ tHeal ∧ ∀
    -- ## The objects
    -- The start and the end of the window `[tGAT, tAwakeEnd]`.
    (tGAT tAwakeEnd : Int)
    -- The start and the end of the asynchronous period `[b₀, b₁)`.
    (b₀ b₁ : Int)
    -- The start and the end of the window `[tAgain, tSafe]`, after the asynchronous period.
    (tAgain tSafe : Int)
    -- The round by whose action time the stable output is taken.
    (r : Nat)
    -- ## The window
    -- The window lasts at least `tHeal`.
    (hlen : tGAT + tHeal ≤ tAwakeEnd)
    -- The window starts at or after `S.E.t_GST`.
    (hGST : S.E.t_GST ≤ tGAT)
    -- ## The adversary and the committees
    -- Up to `tAwakeEnd`, the adversary holds less than one third of the total weight.
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- ## The schedule
    -- From `tGAT` to `tAwakeEnd`, every validator the adversary does not hold is awake.
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    -- From `tAwakeEnd`, voters awake for `wVote S`, not held, outnumber the held and the other
    -- validators the awake rule lets vote.
    (hsleepiness : sleepinessW S Sched tAwakeEnd)
    -- From `tAwakeEnd`, attesters awake for `wAttest S`, not held, outweigh the held and the other
    -- validators the awake rule lets attest.
    (hroundSleepiness : roundSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- From `tAwakeEnd`, committee members awake for `wVote S`, not held, outnumber the other
    -- members the awake rule lets vote or the adversary holds.
    (hcommitteeSleepiness : committeeSleepinessW (Model.spec (V := V)) S Sched tAwakeEnd)
    -- ## The network
    -- An honest message sent at `t` reaches all awake until `deadlineOutside S b₀ b₁ t` before it.
    (hsync : SynchronyFromWakeOutside (Model.spec (V := V)) S x b₀ b₁)
    -- Woken at `t_w`, awake to `deadlineOutside S b₀ b₁ t_w`, `w` gets prior honest sends by then.
    (hcatchUp : CatchUpOnWakeOutside (Model.spec (V := V)) S x b₀ b₁)
    -- Blocks honest ones held by `tGAT` are held from `tGAT + S.E.Δ` by awake honest ones.
    (hcommonView : CommonViewAtGAT (Model.spec (V := V)) S Sched x tGAT)
    -- ## The proposals
    -- Every `gap` periods in the window a round opens with honest first proposers, and recent ones.
    (hopenings : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tGAT tAwakeEnd gap)
    -- ## The round `r` and the asynchronous period
    -- Round `r`'s action time is at or after `confirmedSettleTime` of `tAwakeEnd`.
    (hsettle : confirmedSettleTime (Model.spec (V := V)) S tAwakeEnd ≤
      ((Model.spec (V := V)).a S.hc S.E.Δ r))
    -- Round `r + 2`'s action time plus `S.E.Δ` is at most `b₀`.
    (hafterRound : periodAfterRound (Model.spec (V := V)) S (r + 1) b₀)
    -- `b₀` is at most `b₁`.
    (hb₀b₁ : b₀ ≤ b₁)
    -- `b₁ + S.E.Δ` is at most the first cutoff round `r + S.hc.η_SG + 2`'s grade computation reads.
    (hbeforeExpiry : periodBeforeExpiry (Model.spec (V := V)) S (r + 1) b₁)
    -- Those awake from `wAttest S` before round `r + 1`'s action instant to `Δ` after round
    -- `r + 2`'s, not held, outweigh the held and the other validators the awake rule lets attest.
    (hfixedSleepiness : fixedRoundSleepinessCountedW (Model.spec (V := V)) S Sched (r + 1))
    -- The other validators the awake rule lets attest at rounds `r + 3` to `r + S.hc.η_SG + 1`
    -- weigh at most a third of the total.
    (houtsideThird : outsideAttestersUnderThird (Model.spec (V := V)) S Sched (r + 1))
    -- ## The window `[tAgain, tSafe]`
    -- `b₁ + S.E.Δ` is at most `tAgain`.
    (hagain : b₁ + S.E.Δ ≤ tAgain)
    -- `[tAgain, tSafe]` lasts at least `tHeal` plus `liveAgainAfterHealing` of `gap`.
    (hlenAgain : tAgain + (tHeal + liveAgainAfterHealing (Model.spec (V := V)) S gap) ≤ tSafe)
    -- Up to `tSafe`, the adversary holds less than one third of the total weight.
    (hthirdAgain : ∀ t : Int, t ≤ tSafe →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- From `tAgain` to `tSafe`, every validator the adversary does not hold is awake.
    (hawakeAgain : ∀ t : Int, tAgain ≤ t → t ≤ tSafe →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    -- Every `gap` periods in `[tAgain, tSafe]` a round opens with honest proposers and recent ones.
    (hopeningsAgain : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tAgain tSafe gap)
    -- Blocks honest ones held by `tAgain` are held from `tAgain + S.E.Δ` by awake honest ones.
    (hcommonViewAgain : CommonViewAtGAT (Model.spec (V := V)) S Sched x tAgain),
    -- ## The conclusion
    -- Ancestors of an honest stable output by round `r` stay in honest stable outputs from `b₀` on.
    StablePersistsFromRound (Model.spec (V := V)) S Sched x tAwakeEnd r b₀ := by
  obtain ⟨tHeal, h0, hall⟩ :=
    EndResults.claimStableThroughOneAsyncPeriodCommonViewAgain_holds S Sched gap hgap hmonotone
      hhonestComm hawakeMultiples
  exact ⟨tHeal, h0, fun tGAT tAwakeEnd b₀ b₁ tAgain tSafe r hlen hGST hthird hawake hsleepiness
    hroundSleepiness hcommitteeSleepiness hsync hcatchUp hcommonView hopenings hsettle hafterRound
    hb₀b₁ hbeforeExpiry hfixedSleepiness houtsideThird hagain hlenAgain hthirdAgain hawakeAgain
    hopeningsAgain hcommonViewAgain =>
      hall x hadmitted tGAT tAwakeEnd b₀ b₁ tAgain tSafe r hlen hGST hthird hawake hsleepiness
        hroundSleepiness hcommitteeSleepiness hsync hcatchUp hcommonView hopenings hsettle
        hafterRound hb₀b₁ hbeforeExpiry hfixedSleepiness houtsideThird hagain hlenAgain hthirdAgain
        hawakeAgain hopeningsAgain hcommonViewAgain⟩

end EndResults
