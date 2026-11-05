import LARuns.Trace
import RStsVariant2

/-!
# The readings that Goldilocks's redelivery condition reads

The readings that Goldilocks's redelivery condition
(`LARuns.GoldilocksInstance.RedeliveredAfterReleaseFromDelivery`), an extra condition of Goldilocks's claim,
reads. The condition is read on the observed run of a run (`RStsVariant2.ObservedRun`), and written
over any execution with an `RStsVariant2.Observable`; its readings are those of the section "The
readings of the redelivery condition, on any execution with an `Observable`": `TickAtG`,
`RestartAtG`, `DeliversToUpAndHonestG`, `HonestSendAtG`, `ReactedAtLeastG`, `NoTickAtLeastBetweenG`,
`ActsFromOnlyAfterStepG` and `DeliveredAgainByG`.

The section "The readings of the redelivery condition, on a `RealTrace`" holds the same readings
over a real-time trace: `NoTickAtLeastBetween`, `ActsFromOnlyAfterStep` and `DeliveredAgainBy`, with
those of `LARuns.Trace`. No statement reads them.

Statement 4 (`LARuns.ConfirmedPersistsThroughAsyncPeriodOnRuns`) reads no condition on a trace.

`x i` is the configuration after `i` steps, entered at the real time `(x i).time`; step `i` is taken
at `(x (i + 1)).time`. Every definition's docstring ends with its kind: here, a reading of a trace
(assumes nothing).

This page imports `LARuns.Trace` and `RStsVariant2` (for `Observable`).
-/

set_option autoImplicit false

namespace LARuns

open RealTrace

/-! ## The readings of the redelivery condition, on a `RealTrace` (read by no statement) -/

section Network

variable {Node Msg Block : Type} [DecidableEq Node] [DecidableEq Msg]

/-- No tick of `v` strictly between steps `iAfter` and `iBefore` is at a reading at least
`tRelease`: every such tick is at a reading less than `tRelease` (in `RedeliveredAfterReleaseFromDelivery`,
`tRelease` is the message's release reading).

Read aloud: between steps `iAfter` and `iBefore`, `v` does not tick at `tRelease` or later.

Kind: a reading of a trace. -/
def RealTrace.NoTickAtLeastBetween (x : RealTrace Node Msg Block) (iAfter iBefore : ℕ)
    (tRelease : ℕ) (v : Node) : Prop :=
  ∀ (i : ℕ) (tTick : ℕ), iAfter < i → i < iBefore → x.action i = .tick v tTick →
    tTick < tRelease

/-- Every acting step of `v` taken at the real time `tFrom` or later comes after step `iAfter`.

Read aloud: from the real time `tFrom` on, `v` acts only after step `iAfter`.

Kind: a reading of a trace. -/
def RealTrace.ActsFromOnlyAfterStep (x : RealTrace Node Msg Block) (tFrom : ℝ) (iAfter : ℕ)
    (v : Node) : Prop :=
  ∀ l : ℕ, x.ActingStep l v → tFrom ≤ (x (l + 1)).time → iAfter < l

/-- Some step after step `kAct`, taken at the real time `tBy` or earlier, delivers `e` to `v`,
before any acting step of `v` taken at `tBy` or later (in `RedeliveredAfterReleaseFromDelivery`, `kAct` is a
step at which `v` acts, a tick).

Read aloud: after step `kAct`, `e` is delivered to `v` again by the real time `tBy`, and before `v`
acts from `tBy` on.

Kind: a reading of a trace. -/
def RealTrace.DeliveredAgainBy (x : RealTrace Node Msg Block) (kAct : ℕ) (tBy : ℝ) (v : Node)
    (e : Envelope Node Msg) : Prop :=
  ∃ jDeliver : ℕ, kAct < jDeliver ∧ x.action jDeliver = .deliver v e ∧
    (x (jDeliver + 1)).time ≤ tBy ∧ x.ActsFromOnlyAfterStep (tFrom := tBy) (iAfter := jDeliver) v

end Network

/-! ## The readings of the redelivery condition, on any execution with an `Observable`

The readings `RedeliveredAfterReleaseFromDelivery` reads, written once over any type of
execution with an `RStsVariant2.Observable` (a run of a protocol of `RStsVariant2`, or an observed
run): the steps, the clocks, the sent envelopes, the crashed and corrupted sets, and whether a
node's state is known, each read through the class (`Observable.lbl x i`, `Observable.clock x i v`,
…). The suffix `G` marks a definition written over the class, as in `RStsVariant2`; each has a
namesake over `RealTrace` in the section before, and on the trace of a run the two say the same. -/

section NetworkG

open RStsVariant2 (Observable HonestG)
open RStsVariant2.Observable

variable {X Node Msg L Ev : Type} [DecidableEq Node] [DecidableEq Msg] [Observable X Node Msg L Ev]

/-- Step `k` of `x` is `v`'s tick at its clock reading `tTick`: the step is `tick v`, and `v`'s
clock reads `tTick` in configuration `k`, the configuration the step is taken from.

Read aloud: at step `k`, `v` ticks at the reading `tTick`.

Kind: a reading of an execution. -/
def TickAtG (x : X) (k : ℕ) (v : Node) (tTick : ℕ) : Prop :=
  lbl x k = .tick v ∧ clock x k v = some tTick

/-- Step `k` of `x` is `v`'s restart at its clock reading `tRestart`, keeping its memory or not
(`keep`): the step is `restart v keep`, and `v`'s clock reads `tRestart` in configuration `k`.

Read aloud: at step `k`, `v` restarts at the reading `tRestart`.

Kind: a reading of an execution. -/
def RestartAtG (x : X) (k : ℕ) (v : Node) (tRestart : ℕ) (keep : Bool) : Prop :=
  lbl x k = .restart v keep ∧ clock x k v = some tRestart

/-- Step `j` of `x` delivers the envelope `e` to `v` while `v` is up and honest: the step is
`deliver v e`, and in configuration `j` `v` is outside the crashed set, its state is known, and it
is outside the corrupted set.

Read aloud: at step `j`, `e` reaches `v`, which is up and honest.

Kind: a reading of an execution. -/
def DeliversToUpAndHonestG (x : X) (j : ℕ) (v : Node) (e : RStsVariant2.Envelope Node Msg) :
    Prop :=
  lbl x j = .deliver v e ∧ v ∉ crashed x j ∧ state x j v ≠ none ∧ HonestG x j v

/-- Step `i` of `x` puts the envelope `e` on the wire (one more copy of it among the envelopes sent
after the step) and `e`'s signer is honest in configuration `i`, the configuration the step is
taken from.

Read aloud: at step `i`, an honest validator sends `e`.

Kind: a reading of an execution. -/
def HonestSendAtG (x : X) (i : ℕ) (e : RStsVariant2.Envelope Node Msg) : Prop :=
  e ∈ sent x (i + 1) - sent x i ∧ HonestG x i e.sender

/-- By step `iBefore`, `v` has reacted to the reading `tAtLeast`: at some step `iReact` before
`iBefore`, `v` ticked, or was restarted, at a clock reading `tReact` at least `tAtLeast`.

Read aloud: before step `iBefore`, `v` has run its reaction at a reading at least `tAtLeast`.

Kind: a reading of an execution. -/
def ReactedAtLeastG (x : X) (iBefore : ℕ) (v : Node) (tAtLeast : ℕ) : Prop :=
  ∃ (iReact : ℕ) (tReact : ℕ), iReact < iBefore ∧ tAtLeast ≤ tReact ∧
    (TickAtG x iReact v tReact ∨ ∃ keep : Bool, RestartAtG x iReact v tReact keep)

/-- No tick of `v` strictly between steps `iAfter` and `iBefore` is at a clock reading at least
`tRelease`: every such tick is at a reading less than `tRelease` (in `RedeliveredAfterReleaseFromDelivery`,
`tRelease` is the message's release reading).

Read aloud: between steps `iAfter` and `iBefore`, `v` does not tick at `tRelease` or later.

Kind: a reading of an execution. -/
def NoTickAtLeastBetweenG (x : X) (iAfter iBefore : ℕ) (tRelease : ℕ) (v : Node) : Prop :=
  ∀ (i : ℕ) (tTick : ℕ), iAfter < i → i < iBefore → TickAtG x i v tTick → tTick < tRelease

/-- Every tick of `v`, at any clock reading, taken at the real time `tFrom` or later comes after
step `iAfter`.

Read aloud: from the real time `tFrom` on, `v` ticks only after step `iAfter`.

Kind: a reading of an execution. -/
def ActsFromOnlyAfterStepG (x : X) (tFrom : ℝ) (iAfter : ℕ) (v : Node) : Prop :=
  ∀ l : ℕ, (∃ tTick : ℕ, TickAtG x l v tTick) → tFrom ≤ stamp x (l + 1) → iAfter < l

/-- Some step after step `kAct`, taken at the real time `tBy` or earlier, delivers `e` to `v` while
`v` is up and honest, before any tick of `v` taken at `tBy` or later (in `RedeliveredAfterReleaseFromDelivery`,
`kAct` is a tick of `v`).

Read aloud: after step `kAct`, `e` is delivered to `v` again by the real time `tBy`, and before `v`
ticks from `tBy` on.

Kind: a reading of an execution. -/
def DeliveredAgainByG (x : X) (kAct : ℕ) (tBy : ℝ) (v : Node)
    (e : RStsVariant2.Envelope Node Msg) : Prop :=
  ∃ jDeliver : ℕ, kAct < jDeliver ∧ DeliversToUpAndHonestG x jDeliver v e ∧
    stamp x (jDeliver + 1) ≤ tBy ∧ ActsFromOnlyAfterStepG x (tFrom := tBy) (iAfter := jDeliver) v

end NetworkG

end LARuns
