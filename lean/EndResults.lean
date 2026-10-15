import Proofs.Instance.Facts.Assembly
import Proofs.Claims.Restated.Constants
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
# The end results at the spec's model

This file holds `constants_holds` and, for each claim, the explicit form `…_holds_explicit`. The
existential forms `…_holds` and `…_holds_perExecution`, which state that there is a healing length
`tHeal`, are in `lean/EndResults/ExistentialForms.lean`. The paragraphs that follow describe the
statements of both files.

Each top-level theorem `…_holds` of the claims, applied to `Model.spec_facts`, so that it
states the result for the spec's model `Model.spec`. Each theorem has the name of the
`…_holds` theorem it applies, in the namespace `EndResults`. Each statement is the body of the
definition the `…_holds` theorem concludes, written out one level, with
`(Model.spec (V := V))` in place of the model `M`; the conditions that body names
stay as names. Each hypothesis is a named binder. The `∀ gap` and its condition, which
come before the `∃ tHeal`, are binders before the colon, and so is every hypothesis that names no
variable bound by the `∃ tHeal` or by the `∀` under it. The other hypotheses stay under the
`∃ tHeal`, as the binders of its `∀`. Each statement with an `∃ tHeal` takes `admittedExecution`,
which names each constraint, in place of the premises `ExecutionValid` and `TimeDiverges`, and its
hypotheses, before the colon and under the `∃ tHeal`, are grouped by kind, each with a comment that
says what it requires. Each proof passes the hypotheses back to the `…_holds` theorem in the body's
order.

Each theorem with an `∃ tHeal` is followed by its per-execution form `…_holds_perExecution`, where
the execution `x`, and each hypothesis naming only `x` and the binders before it, also come before
the colon: `tHeal` is chosen for each execution. Its proof takes `tHeal` from the theorem before it.

Each theorem with an `∃ tHeal` also has an explicit form `…_holds_explicit`, which follows its
per-execution form with `tHeal` written out as the value the proof of `…_holds` picks, and with the
times and every hypothesis before the colon.
-/

set_option autoImplicit false

namespace EndResults

open DecoupledConsensusModel
open DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Restated
open DecoupledConsensusModel.Sts.Record
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- For every setup `S`, the timing constants `C` at `Model.spec` are well formed: the period
    is positive, the window and the lag are not negative, there is at least one proposer slot,
    the maximum gap is at least two, every delay is not negative, the prefix ends no later than
    the recovery, and `C.outageStart T < C.expiry T` for every `T`. -/
theorem constants_holds
    (S : Setup V) :
    let C := constants (Model.spec (V := V)) S
    -- The period, from round 0's action time to round 1's, is positive.
    0 < C.period ∧
    -- The participation window, `S.hc.η_SG` periods, is not negative.
    0 ≤ C.participationWindow ∧
    -- The participation lag, one period, is not negative.
    0 ≤ C.participationLag ∧
    -- There is at least one proposer slot.
    0 < C.proposerSlots ∧
    -- The maximum recurrence gap, `S.cfg.K` periods, is at least two.
    2 ≤ C.maxGap ∧
    -- For every `gap`, every inclusion, growth, startup and deadline delay is not negative.
    (∀ gap,
      0 ≤ C.confirmationDelay ∧
      0 ≤ C.growthDelay gap ∧
      0 ≤ C.stableGrowthDelay gap ∧
      0 ≤ C.stableInclusionDelay gap ∧
      0 ≤ C.finalityStartup gap ∧
      0 ≤ C.finalityDeadline gap) ∧
    -- For every `t₀` and `gap`, the source prefix ends no later than the recovery.
    (∀ t₀ gap, C.prefixEnd t₀ gap ≤ C.recoveryEnd t₀ gap) ∧
    -- For every `T`, the stable output read at `T` has its earliest outage start before its expiry.
    ∀ T, C.outageStart T < C.expiry T :=
  let h := DecoupledConsensusModel.Sts.Restated.constants_holds Model.spec_facts S
  ⟨h.period_pos,
    h.participationWindow_nonneg,
    h.participationLag_nonneg,
    h.proposerSlots_pos,
    h.maxGap_ge_two,
    h.delays_nonneg,
    h.prefixEnd_le_recoveryEnd,
    h.outage_window_nonempty⟩

/-- The theorem `claimConfirmedAfterHealing_holds_perExecution` with its healing length written out:
    the conclusion holds over every phase `[tGAT, tAwakeEnd]` of length at least `healingLengthη` of
    `gap` plus `gap + 2` periods, the value of `tHeal` that the proof of
    `claimConfirmedAfterHealing_holds` picks. -/
theorem claimConfirmedAfterHealing_holds_explicit
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
    -- The start and the end of the window `[tGAT, tAwakeEnd]`.
    (tGAT tAwakeEnd : Int)
    -- ## The parameter
    -- `gap + 2` is at most `S.cfg.K`, the period of the nonjustifiable heights.
    (hgap : gap + 2 ≤ S.cfg.K)
    -- ## The window
    -- The window lasts at least `healingLengthη` of `gap` plus `gap + 2` periods.
    (hlen : tGAT + (healingLengthη (Model.spec (V := V)) S gap + ((gap : Int) + 2) *
      (constants (Model.spec (V := V)) S).period) ≤ tAwakeEnd)
    -- The window starts at or after `S.E.t_GST`.
    (hGST : S.E.t_GST ≤ tGAT)
    -- ## The adversary and the committees
    -- A validator the adversary holds at time `t` it holds at every later time.
    (hmonotone : Sched.MonotoneCorruption)
    -- Up to `tAwakeEnd`, the adversary holds less than one third of the total weight.
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- Every committee is more than half honest through its slot's confirmation time.
    (hhonestComm : HonestCommittees (Model.spec (V := V)) S Sched
      (interface (Model.spec (V := V)) S Sched))
    -- ## The schedule
    -- A validator awake at `t` and not at `t - 1` has `t` a multiple of `S.E.Δ`.
    (hawakeMultiples : AwakeAtMultiples S Sched)
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
    (hopenings : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tGAT tAwakeEnd gap) :
    -- ## The conclusion
    -- From `confirmedSettleTime`, honest validators awake for `wVote S` confirm compatible blocks.
    ConfirmedAgreeAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd ∧
    -- From `confirmedSettleTime`, an honest `v` awake for `wVote S` later confirms descendants.
    ConfirmedMonotoneAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd := by
  obtain ⟨hunforgeable, hcarried, hwire, hdeps, hrootInjective, hhonestRootsNew, htime⟩ :=
    hadmitted
  exact DecoupledConsensusModel.Sts.Restated.claimConfirmedAfterHealing_holds_at
      Model.spec_facts S Sched gap hgap x tGAT tAwakeEnd hlen hGST hmonotone
      ⟨⟨hunforgeable, hcarried⟩, ⟨hwire, hdeps⟩, ⟨hrootInjective⟩, hhonestRootsNew⟩ hsync
      hawakeMultiples hcatchUp htime hhonestComm hthird hawake hopenings hsleepiness
      hroundSleepiness hcommitteeSleepiness

/-- The theorem `claimStableLiveAfterHealing_holds_perExecution` with its healing length written
    out: the conclusion holds over every phase `[tGAT, tAwakeEnd]` of length at least
    `healingLengthη` of `gap` plus `gap + 2` periods, the value of `tHeal` that the proof of
    `claimStableLiveAfterHealing_holds` picks. -/
theorem claimStableLiveAfterHealing_holds_explicit
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
    -- The start and the end of the window `[tGAT, tAwakeEnd]`.
    (tGAT tAwakeEnd : Int)
    -- ## The parameter
    -- `gap + 2` is at most `S.cfg.K`, the period of the nonjustifiable heights.
    (hgap : gap + 2 ≤ S.cfg.K)
    -- ## The window
    -- The window lasts at least `healingLengthη` of `gap` plus `gap + 2` periods.
    (hlen : tGAT + (healingLengthη (Model.spec (V := V)) S gap + ((gap : Int) + 2) *
      (constants (Model.spec (V := V)) S).period) ≤ tAwakeEnd)
    -- The window starts at or after `S.E.t_GST`.
    (hGST : S.E.t_GST ≤ tGAT)
    -- ## The adversary and the committees
    -- A validator the adversary holds at time `t` it holds at every later time.
    (hmonotone : Sched.MonotoneCorruption)
    -- Up to `tAwakeEnd`, the adversary holds less than one third of the total weight.
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- Every committee is more than half honest through its slot's confirmation time.
    (hhonestComm : HonestCommittees (Model.spec (V := V)) S Sched
      (interface (Model.spec (V := V)) S Sched))
    -- ## The schedule
    -- A validator awake at `t` and not at `t - 1` has `t` a multiple of `S.E.Δ`.
    (hawakeMultiples : AwakeAtMultiples S Sched)
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
    (hopenings : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tGAT tAwakeEnd gap) :
    -- ## The conclusion
    -- From `tAwakeEnd`, honest proposals enter the stable outputs of the honest that ran a
    -- confirmation after them.
    StableIncludedAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd ∧
    -- From `tAwakeEnd`, an honest validator's stable output is a descendant of its earlier ones.
    StableOnlyExtendsAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd ∧
    -- If honest awake proposers recur every `gapP` periods from `tAwakeEnd`, stable outputs grow.
    ∀ gapP : Nat, honestAwakeProposersRecurFrom (Model.spec (V := V)) S Sched tAwakeEnd gapP →
      StableGrowsAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd gapP := by
  obtain ⟨hunforgeable, hcarried, hwire, hdeps, hrootInjective, hhonestRootsNew, htime⟩ :=
    hadmitted
  exact DecoupledConsensusModel.Sts.Restated.claimStableLiveAfterHealing_holds_at
      Model.spec_facts S Sched gap hgap x tGAT tAwakeEnd hlen hGST hmonotone
      ⟨⟨hunforgeable, hcarried⟩, ⟨hwire, hdeps⟩, ⟨hrootInjective⟩, hhonestRootsNew⟩ hsync
      hawakeMultiples hcatchUp htime hhonestComm hthird hawake hopenings hsleepiness
      hroundSleepiness hcommitteeSleepiness

/-- The theorem `claimConfirmedIncludedAfterHealing_holds_perExecution` with its healing length
    written out: the conclusion holds over every phase `[tGAT, tAwakeEnd]` of length at least
    `healingLengthη` of `gap` plus `gap + 2` periods, the value of `tHeal` that the proof of
    `claimConfirmedIncludedAfterHealing_holds` picks. -/
theorem claimConfirmedIncludedAfterHealing_holds_explicit
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
    -- The start and the end of the window `[tGAT, tAwakeEnd]`.
    (tGAT tAwakeEnd : Int)
    -- ## The parameter
    -- `gap + 2` is at most `S.cfg.K`, the period of the nonjustifiable heights.
    (hgap : gap + 2 ≤ S.cfg.K)
    -- ## The window
    -- The window lasts at least `healingLengthη` of `gap` plus `gap + 2` periods.
    (hlen : tGAT + (healingLengthη (Model.spec (V := V)) S gap + ((gap : Int) + 2) *
      (constants (Model.spec (V := V)) S).period) ≤ tAwakeEnd)
    -- The window starts at or after `S.E.t_GST`.
    (hGST : S.E.t_GST ≤ tGAT)
    -- ## The adversary and the committees
    -- A validator the adversary holds at time `t` it holds at every later time.
    (hmonotone : Sched.MonotoneCorruption)
    -- Up to `tAwakeEnd`, the adversary holds less than one third of the total weight.
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- Every committee is more than half honest through its slot's confirmation time.
    (hhonestComm : HonestCommittees (Model.spec (V := V)) S Sched
      (interface (Model.spec (V := V)) S Sched))
    -- ## The schedule
    -- A validator awake at `t` and not at `t - 1` has `t` a multiple of `S.E.Δ`.
    (hawakeMultiples : AwakeAtMultiples S Sched)
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
    (hopenings : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tGAT tAwakeEnd gap) :
    -- ## The conclusion
    -- From `tAwakeEnd`, honest proposals enter the confirmed outputs of the honest that ran a
    -- confirmation after them.
    ConfirmedIncludedAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd ∧
    -- From `tAwakeEnd`, an honest validator's confirmed output is a descendant of its earlier ones.
    ConfirmedOnlyExtendsAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd := by
  obtain ⟨hunforgeable, hcarried, hwire, hdeps, hrootInjective, hhonestRootsNew, htime⟩ :=
    hadmitted
  exact DecoupledConsensusModel.Sts.Restated.claimConfirmedIncludedAfterHealing_holds_at
      Model.spec_facts S Sched gap hgap x tGAT tAwakeEnd hlen hGST hmonotone
      ⟨⟨hunforgeable, hcarried⟩, ⟨hwire, hdeps⟩, ⟨hrootInjective⟩, hhonestRootsNew⟩ hsync
      hawakeMultiples hcatchUp htime hhonestComm hthird hawake hopenings hsleepiness
      hroundSleepiness hcommitteeSleepiness

/-- The theorem `claimStableThroughOneAsyncPeriod_holds_perExecution` with its healing length
    written out: the conclusion holds over every phase `[tGAT, tAwakeEnd]` of length at least
    `healingLengthη` of `gap` plus `gap + 2` periods, the value of `tHeal` that the proof of
    `claimStableThroughOneAsyncPeriod_holds` picks, also in the length of `[tAgain, tSafe]`. -/
theorem claimStableThroughOneAsyncPeriod_holds_explicit
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
    -- The start and the end of the window `[tGAT, tAwakeEnd]`.
    (tGAT tAwakeEnd : Int)
    -- The start and the end of the asynchronous period `[b₀, b₁)`.
    (b₀ b₁ : Int)
    -- The start and the end of the window `[tAgain, tSafe]`, after the asynchronous period.
    (tAgain tSafe : Int)
    -- The round by whose action time the stable output is taken.
    (r : Nat)
    -- ## The parameter
    -- `gap + 2` is at most `S.cfg.K`, the period of the nonjustifiable heights.
    (hgap : gap + 2 ≤ S.cfg.K)
    -- ## The window
    -- The window lasts at least `healingLengthη` of `gap` plus `gap + 2` periods.
    (hlen : tGAT + (healingLengthη (Model.spec (V := V)) S gap + ((gap : Int) + 2) *
      (constants (Model.spec (V := V)) S).period) ≤ tAwakeEnd)
    -- The window starts at or after `S.E.t_GST`.
    (hGST : S.E.t_GST ≤ tGAT)
    -- ## The adversary and the committees
    -- A validator the adversary holds at time `t` it holds at every later time.
    (hmonotone : Sched.MonotoneCorruption)
    -- Up to `tAwakeEnd`, the adversary holds less than one third of the total weight.
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- Every committee is more than half honest through its slot's confirmation time.
    (hhonestComm : HonestCommittees (Model.spec (V := V)) S Sched
      (interface (Model.spec (V := V)) S Sched))
    -- ## The schedule
    -- A validator awake at `t` and not at `t - 1` has `t` a multiple of `S.E.Δ`.
    (hawakeMultiples : AwakeAtMultiples S Sched)
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
    -- `[tAgain, tSafe]` lasts at least `hlen`'s length plus `liveAgainAfterHealing` of `gap`.
    (hlenAgain : tAgain + (healingLengthη (Model.spec (V := V)) S gap + ((gap : Int) + 2) *
      (constants (Model.spec (V := V)) S).period + liveAgainAfterHealing
      (Model.spec (V := V)) S gap) ≤ tSafe)
    -- Up to `tSafe`, the adversary holds less than one third of the total weight.
    (hthirdAgain : ∀ t : Int, t ≤ tSafe →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- From `tAgain` to `tSafe`, every validator the adversary does not hold is awake.
    (hawakeAgain : ∀ t : Int, tAgain ≤ t → t ≤ tSafe →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    -- Every `gap` periods in `[tAgain, tSafe]` a round opens with honest proposers and recent ones.
    (hopeningsAgain : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tAgain tSafe gap) :
    -- ## The conclusion
    -- Ancestors of an honest stable output by round `r` stay in honest stable outputs from `b₀` on.
    StablePersistsFromRound (Model.spec (V := V)) S Sched x tAwakeEnd r b₀ := by
  obtain ⟨hunforgeable, hcarried, hwire, hdeps, hrootInjective, hhonestRootsNew, htime⟩ :=
    hadmitted
  exact DecoupledConsensusModel.Sts.Restated.claimStableThroughOneAsyncPeriod_holds_at
      Model.spec_facts S Sched gap hgap x tGAT tAwakeEnd b₀ b₁ tAgain tSafe r hlen hGST
      hmonotone ⟨⟨hunforgeable, hcarried⟩, ⟨hwire, hdeps⟩, ⟨hrootInjective⟩, hhonestRootsNew⟩ hsync
      hawakeMultiples hcatchUp htime hhonestComm hthird hawake hopenings hsleepiness
      hroundSleepiness hcommitteeSleepiness hsettle hafterRound hb₀b₁ hbeforeExpiry hfixedSleepiness
      houtsideThird hagain hlenAgain hthirdAgain hawakeAgain hopeningsAgain

/-- The theorem `claim13bf_holds_perExecution` with its healing length written out: the conclusion
    holds over every phase `[tGAT, tAwakeEnd]` of length at least `healingLengthη` of `gap` plus one
    period, the value of `tHeal` that the proof of `claim13bf_holds` picks. -/
theorem claim13bf_holds_explicit
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
    -- The start and the end of the window `[tGAT, tAwakeEnd]`.
    (tGAT tAwakeEnd : Int)
    -- Two validators.
    (v₁ v₂ : V)
    -- Two steps of `x`.
    (i j : Nat)
    -- ## The parameter
    -- `gap + 2` is at most `S.cfg.K`, the period of the nonjustifiable heights.
    (hgap : gap + 2 ≤ S.cfg.K)
    -- ## The window
    -- The window lasts at least `healingLengthη` of `gap` plus one period.
    (hlen : tGAT + (healingLengthη (Model.spec (V := V)) S gap +
      (constants (Model.spec (V := V)) S).period) ≤ tAwakeEnd)
    -- The window starts at or after `S.E.t_GST`.
    (hGST : S.E.t_GST ≤ tGAT)
    -- ## The adversary and the committees
    -- A validator the adversary holds at time `t` it holds at every later time.
    (hmonotone : Sched.MonotoneCorruption)
    -- Up to `tAwakeEnd`, the adversary holds less than one third of the total weight.
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- Every committee is more than half honest through its slot's confirmation time.
    (hhonestComm : HonestCommittees (Model.spec (V := V)) S Sched
      (interface (Model.spec (V := V)) S Sched))
    -- ## The schedule
    -- A validator awake at `t` and not at `t - 1` has `t` a multiple of `S.E.Δ`.
    (hawakeMultiples : AwakeAtMultiples S Sched)
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
    (hhonest₂ : HonestThrough (Model.spec (V := V)) Sched x j v₂) :
    -- ## The conclusion
    -- The finalized blocks of `v₁` at step `i` and of `v₂` at step `j` are compatible.
    Block.Compatible (Read.finalized (Model.spec (V := V)) x[i][v₁].st)
      (Read.finalized (Model.spec (V := V)) x[j][v₂].st) := by
  obtain ⟨hunforgeable, hcarried, hwire, hdeps, hrootInjective, hhonestRootsNew, htime⟩ :=
    hadmitted
  exact DecoupledConsensusModel.Sts.Restated.claim13bf_holds_at Model.spec_facts S Sched
      gap hgap x tGAT tAwakeEnd hlen hGST hmonotone
      ⟨⟨hunforgeable, hcarried⟩, ⟨hwire, hdeps⟩, ⟨hrootInjective⟩, hhonestRootsNew⟩ hsync
      hawakeMultiples hcatchUp htime hhonestComm hthird hawake hopenings hsleepiness
      hroundSleepiness hcommitteeSleepiness v₁ v₂ i j hhonest₁ hhonest₂

/-- The theorem `claimConfirmedGrowsAfterHealing_holds_perExecution` with its healing length written
    out: the conclusion holds over every phase `[tGAT, tAwakeEnd]` of length at least
    `healingLengthη` of `gap` plus `gap + 2` periods, the value of `tHeal` that the proof of
    `claimConfirmedGrowsAfterHealing_holds` picks. -/
theorem claimConfirmedGrowsAfterHealing_holds_explicit
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
    -- The start and the end of the window `[tGAT, tAwakeEnd]`.
    (tGAT tAwakeEnd : Int)
    -- A number of periods: honest awake proposers recur within every `gapP` periods.
    (gapP : Nat)
    -- ## The parameter
    -- `gap + 2` is at most `S.cfg.K`, the period of the nonjustifiable heights.
    (hgap : gap + 2 ≤ S.cfg.K)
    -- ## The window
    -- The window lasts at least `healingLengthη` of `gap` plus `gap + 2` periods.
    (hlen : tGAT + (healingLengthη (Model.spec (V := V)) S gap + ((gap : Int) + 2) *
      (constants (Model.spec (V := V)) S).period) ≤ tAwakeEnd)
    -- The window starts at or after `S.E.t_GST`.
    (hGST : S.E.t_GST ≤ tGAT)
    -- ## The adversary and the committees
    -- A validator the adversary holds at time `t` it holds at every later time.
    (hmonotone : Sched.MonotoneCorruption)
    -- Up to `tAwakeEnd`, the adversary holds less than one third of the total weight.
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- Every committee is more than half honest through its slot's confirmation time.
    (hhonestComm : HonestCommittees (Model.spec (V := V)) S Sched
      (interface (Model.spec (V := V)) S Sched))
    -- ## The schedule
    -- A validator awake at `t` and not at `t - 1` has `t` a multiple of `S.E.Δ`.
    (hawakeMultiples : AwakeAtMultiples S Sched)
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
    (hproposers : honestAwakeProposersRecurFrom (Model.spec (V := V)) S Sched tAwakeEnd gapP) :
    -- ## The conclusion
    -- From `tAwakeEnd`, honest proposals soon extend all honest confirmed outputs, then join those
    -- of the honest that ran a confirmation.
    ConfirmedGrowsAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd gapP := by
  obtain ⟨hunforgeable, hcarried, hwire, hdeps, hrootInjective, hhonestRootsNew, htime⟩ :=
    hadmitted
  exact DecoupledConsensusModel.Sts.Restated.claimConfirmedGrowsAfterHealing_holds_at
      Model.spec_facts S Sched gap hgap x tGAT tAwakeEnd gapP hlen hGST hmonotone
      ⟨⟨hunforgeable, hcarried⟩, ⟨hwire, hdeps⟩, ⟨hrootInjective⟩, hhonestRootsNew⟩ hsync
      hawakeMultiples hcatchUp htime hhonestComm hthird hawake hopenings hsleepiness
      hroundSleepiness hcommitteeSleepiness hproposers

/-- The theorem `claimFinalityLiveAfterHealing_holds_perExecution` with its healing length written
    out: the conclusion holds over every phase `[tGAT, tAwakeEnd]` of length at least
    `healingLengthη` of `gap` plus one period, the value of `tHeal` that the proof of
    `claimFinalityLiveAfterHealing_holds` picks. -/
theorem claimFinalityLiveAfterHealing_holds_explicit
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
    -- The start and the end of the window `[tGAT, tAwakeEnd]`.
    (tGAT tAwakeEnd : Int)
    -- The time up to which the adversary bound, the awake premise and the openings continue.
    (tLive : Int)
    -- ## The parameter
    -- `gap + 2` is at most `S.cfg.K`, the period of the nonjustifiable heights.
    (hgap : gap + 2 ≤ S.cfg.K)
    -- ## The window
    -- The window lasts at least `healingLengthη` of `gap` plus one period.
    (hlen : tGAT + (healingLengthη (Model.spec (V := V)) S gap +
      (constants (Model.spec (V := V)) S).period) ≤ tAwakeEnd)
    -- `tAwakeEnd` is at most `tLive`.
    (hlive : tAwakeEnd ≤ tLive)
    -- The window starts at or after `S.E.t_GST`.
    (hGST : S.E.t_GST ≤ tGAT)
    -- ## The adversary and the committees
    -- A validator the adversary holds at time `t` it holds at every later time.
    (hmonotone : Sched.MonotoneCorruption)
    -- Up to `tLive`, the adversary holds less than one third of the total weight.
    (hthird : ∀ t : Int, t ≤ tLive →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- Every committee is more than half honest through its slot's confirmation time.
    (hhonestComm : HonestCommittees (Model.spec (V := V)) S Sched
      (interface (Model.spec (V := V)) S Sched))
    -- ## The schedule
    -- A validator awake at `t` and not at `t - 1` has `t` a multiple of `S.E.Δ`.
    (hawakeMultiples : AwakeAtMultiples S Sched)
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
    (hopenings : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tGAT tLive gap) :
    -- ## The conclusion
    -- Honest proposals in the liveness window are finalized by honest validators after a deadline.
    FinalityIncludedAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd tLive gap ∧
    -- In the liveness window, honest proposals extend honest finalized blocks, then are finalized.
    FinalityGrowsAfterHealing (Model.spec (V := V)) S Sched x tAwakeEnd tLive gap := by
  obtain ⟨hunforgeable, hcarried, hwire, hdeps, hrootInjective, hhonestRootsNew, htime⟩ :=
    hadmitted
  exact DecoupledConsensusModel.Sts.Restated.claimFinalityLiveAfterHealing_holds_at
      Model.spec_facts S Sched gap hgap x tGAT tAwakeEnd tLive hlen hlive hGST hmonotone
      ⟨⟨hunforgeable, hcarried⟩, ⟨hwire, hdeps⟩, ⟨hrootInjective⟩, hhonestRootsNew⟩ hsync
      hawakeMultiples hcommonView htime hhonestComm hthird hawake hopenings
      hsleepiness hroundSleepiness hcommitteeSleepiness

/-- The theorem `claimStableThroughOneAsyncPeriodCommonViewAgain_holds_perExecution` with its
    healing length written out: the conclusion holds over every phase `[tGAT, tAwakeEnd]` of length
    at least `healingLengthη` of `gap` plus `gap + 2` periods, the value of `tHeal` that the proof
    of `claimStableThroughOneAsyncPeriodCommonViewAgain_holds` picks, also in the length of
    `[tAgain, tSafe]`. -/
theorem claimStableThroughOneAsyncPeriodCommonViewAgain_holds_explicit
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
    -- The start and the end of the window `[tGAT, tAwakeEnd]`.
    (tGAT tAwakeEnd : Int)
    -- The start and the end of the asynchronous period `[b₀, b₁)`.
    (b₀ b₁ : Int)
    -- The start and the end of the window `[tAgain, tSafe]`, after the asynchronous period.
    (tAgain tSafe : Int)
    -- The round by whose action time the stable output is taken.
    (r : Nat)
    -- ## The parameter
    -- `gap + 2` is at most `S.cfg.K`, the period of the nonjustifiable heights.
    (hgap : gap + 2 ≤ S.cfg.K)
    -- ## The window
    -- The window lasts at least `healingLengthη` of `gap` plus `gap + 2` periods.
    (hlen : tGAT + (healingLengthη (Model.spec (V := V)) S gap + ((gap : Int) + 2) *
      (constants (Model.spec (V := V)) S).period) ≤ tAwakeEnd)
    -- The window starts at or after `S.E.t_GST`.
    (hGST : S.E.t_GST ≤ tGAT)
    -- ## The adversary and the committees
    -- A validator the adversary holds at time `t` it holds at every later time.
    (hmonotone : Sched.MonotoneCorruption)
    -- Up to `tAwakeEnd`, the adversary holds less than one third of the total weight.
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- Every committee is more than half honest through its slot's confirmation time.
    (hhonestComm : HonestCommittees (Model.spec (V := V)) S Sched
      (interface (Model.spec (V := V)) S Sched))
    -- ## The schedule
    -- A validator awake at `t` and not at `t - 1` has `t` a multiple of `S.E.Δ`.
    (hawakeMultiples : AwakeAtMultiples S Sched)
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
    -- `[tAgain, tSafe]` lasts at least `hlen`'s length plus `liveAgainAfterHealing` of `gap`.
    (hlenAgain : tAgain + (healingLengthη (Model.spec (V := V)) S gap + ((gap : Int) + 2) *
      (constants (Model.spec (V := V)) S).period + liveAgainAfterHealing
      (Model.spec (V := V)) S gap) ≤ tSafe)
    -- Up to `tSafe`, the adversary holds less than one third of the total weight.
    (hthirdAgain : ∀ t : Int, t ≤ tSafe →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    -- From `tAgain` to `tSafe`, every validator the adversary does not hold is awake.
    (hawakeAgain : ∀ t : Int, tAgain ≤ t → t ≤ tSafe →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    -- Every `gap` periods in `[tAgain, tSafe]` a round opens with honest proposers and recent ones.
    (hopeningsAgain : strongOpeningsRecurFrom (Model.spec (V := V)) S Sched tAgain tSafe gap)
    -- Blocks honest ones held by `tAgain` are held from `tAgain + S.E.Δ` by awake honest ones.
    (hcommonViewAgain : CommonViewAtGAT (Model.spec (V := V)) S Sched x tAgain) :
    -- ## The conclusion
    -- Ancestors of an honest stable output by round `r` stay in honest stable outputs from `b₀` on.
    StablePersistsFromRound (Model.spec (V := V)) S Sched x tAwakeEnd r b₀ := by
  obtain ⟨hunforgeable, hcarried, hwire, hdeps, hrootInjective, hhonestRootsNew, htime⟩ :=
    hadmitted
  exact
      DecoupledConsensusModel.Sts.Restated.claimStableThroughOneAsyncPeriodCommonViewAgain_holds_at
      Model.spec_facts S Sched gap hgap x tGAT tAwakeEnd b₀ b₁ tAgain tSafe r hlen hGST
      hmonotone ⟨⟨hunforgeable, hcarried⟩, ⟨hwire, hdeps⟩, ⟨hrootInjective⟩, hhonestRootsNew⟩ hsync
      hawakeMultiples hcatchUp hcommonView htime hhonestComm hthird hawake hopenings
      hsleepiness hroundSleepiness hcommitteeSleepiness hsettle hafterRound hb₀b₁ hbeforeExpiry
      hfixedSleepiness houtsideThird hagain hlenAgain hthirdAgain hawakeAgain hopeningsAgain
      hcommonViewAgain

end EndResults
