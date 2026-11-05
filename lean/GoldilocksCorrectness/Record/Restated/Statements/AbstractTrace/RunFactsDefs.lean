module
public import GoldilocksCorrectness.Statements.AbstractTrace.TraceDefs
public import GoldilocksCorrectness.Record.Model
public import GoldilocksSts

@[expose] public section

/-!
# What a model's steps do to a trace

`RunFacts M S x`: the trace `x` is a run of the node of the model `M` with the setup `S`. A tick is
an outcome of the model's tick and puts exactly that outcome's objects on the wire; a restart is the
model's wake at the restart's reading and sends nothing; a delivery is of a message on the wire and is the model's receive,
with the model's relays put on the wire; every other step leaves the validator's node state as it
was. Time is a real number; it starts at `0`, never moves back, and moves only at a step that is not
a tick, a restart or a delivery; every node starts from the model's
initial state with nothing on the wire; the sent log only grows.

And the facts that follow from these alone: time and the sent log never decrease along the trace,
and honesty up to a later step gives honesty up to an earlier one.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Record.Statements.AbstractTrace

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity)
open Framework.StsMultisetLog (SignedMsg)
open Goldilocks (NamedObject RootOrder)
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- The trace `x` is a run of the node of the model `M` with the setup `S`. -/
structure RunFacts (M : GoldilocksModel V) (S : Setup V) (x : Trace V (NamedObject V) M.N) :
    Prop where
  /-- The time after `0` steps is `0`. -/
  time_zero : x.time 0 = 0
  /-- No step moves the time back. -/
  time_le_succ : ∀ i : ℕ, x.time i ≤ x.time (i + 1)
  /-- A tick, a restart or a delivery keeps the time: only a step of another kind moves it. -/
  time_keep : ∀ i : ℕ, x.lbl i ≠ Event.other → x.time (i + 1) = x.time i
  /-- Every validator starts from the model's initial state. -/
  init : ∀ v : V, x.st 0 v = M.initial S.C v
  /-- Nothing is on the wire after `0` steps. -/
  sent_zero : x.sent 0 = 0
  /-- Each step keeps every message already on the wire. -/
  sent_mono : ∀ i : ℕ, x.sent i ≤ x.sent (i + 1)
  /-- At `v`'s tick to the reading `t`, `v` takes an `.ok` outcome of the model's tick from its
  node state, and the step puts exactly that outcome's objects on the wire, signed by `v`. -/
  tick : ∀ (i : ℕ) (v : V) (t : ℕ), x.lbl i = Event.tick v t →
    ∃ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.st i v) (t : Int) ∧
      x.st (i + 1) v = n' ∧
      x.sent (i + 1) = x.sent i + (sent : Multiset (NamedObject V)).map (SignedMsg.mk v)
  /-- At `v`'s restart at the reading `t`, `v` takes the model's wake of its node state at `t`, and
  nothing is sent. -/
  restart : ∀ (i : ℕ) (v : V) (t : ℕ) (keep : Bool), x.lbl i = Event.restart v t keep →
    x.st (i + 1) v = M.wake (x.st i v) (t : Int) ∧ x.sent (i + 1) = x.sent i
  /-- At the delivery of `sm` to `v`, `sm` is on the wire, `v` takes the model's receive of the
  object of `sm`, and the step puts the model's relays of that object on the wire, signed by `v`. -/
  deliver : ∀ (i : ℕ) (v : V) (sm : SignedMsg V (NamedObject V)), x.lbl i = Event.deliver v sm →
    sm ∈ x.sent i ∧
    x.st (i + 1) v = M.receive S.C S.P S.X (x.st i v) sm.msg ∧
    x.sent (i + 1) = x.sent i + (M.relayedObjects sm.msg).map (SignedMsg.mk v)
  /-- A step that is not `v`'s tick, restart or delivery leaves `v`'s node state as it was. -/
  untouched : ∀ (i : ℕ) (v : V),
    -- the step is not a tick of `v`
    (∀ t : ℕ, x.lbl i ≠ Event.tick v t) →
    -- the step is not a restart of `v`
    (∀ (t : ℕ) (keep : Bool), x.lbl i ≠ Event.restart v t keep) →
    -- the step is not a delivery to `v`
    (∀ sm : SignedMsg V (NamedObject V), x.lbl i ≠ Event.deliver v sm) →
    x.st (i + 1) v = x.st i v

namespace RunFacts

variable {M : GoldilocksModel V} {S : Setup V} {x : Trace V (NamedObject V) M.N}

/-- The time never decreases along a run.

The variables:
- `R`: the run's facts; `i`, `j`: the two steps.

Read aloud: the time after `i` steps is at most the time after `j ≥ i` steps. -/
theorem time_mono (R : RunFacts M S x) {i j : ℕ} (hij : i ≤ j) : x.time i ≤ x.time j :=
  monotone_nat_of_le_succ R.time_le_succ hij

/-- The sent log never loses a message along a run.

The variables:
- `R`: the run's facts; `i`, `j`: the two steps.

Read aloud: the sent log after `i` steps is contained in the one after `j ≥ i` steps. -/
theorem sent_le (R : RunFacts M S x) {i j : ℕ} (hij : i ≤ j) : x.sent i ≤ x.sent j := by
  induction hij with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (R.sent_mono _)

/-- Honesty up to a later step gives honesty up to an earlier one.

The variables:
- `A`: the activity; `R`: the run's facts; `i`, `j`: the two steps; `v`: the validator.

Read aloud: a validator honest up to step `j` has been honest up to any step `i ≤ j`. -/
theorem honestThrough_of_le {A : Activity V} (_R : RunFacts M S x) {i j : ℕ} (hij : i ≤ j) {v : V}
    (h : x.HonestThrough A j v) : x.HonestThrough A i v :=
  Activity.HonestThroughStep.mono hij h

end RunFacts

end GoldilocksCorrectness.Record.Statements.AbstractTrace
