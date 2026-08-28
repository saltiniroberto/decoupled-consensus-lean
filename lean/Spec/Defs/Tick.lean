import Spec.Defs.Nondet

/-!
# The tick the outside world calls

`on_tick(Σ, t)` is the protocol's one entry point from the clock: it is called whenever time
advances, sets the store's clock, and runs whatever the schedule puts at that instant. Every
layer redefines it, because every layer adds an action to the schedule.

So a caller names no reading. It writes `S.onTick t is_proposer`, the field of `Tick` below,
and the layer that owns the protocol's reading supplies the instance.

## Why the tick is redefined and not extended

The SG layer's text says `on_tick` "gains one line", and a layer that only appends can be
written as a call to the earlier reading. The graded layer does not append: its round lines
run at instants a slot duty also runs at — the SG root is stored at `Γ_1`, which is the
opening slot's vote time, and the round's action instant is the tick at which that slot's
confirmation is evaluated. Which of the two runs first is a protocol decision, and a call
cannot state it: it can only put the new lines wholly before or wholly after.

So each layer's reading writes its tick out in full, in the order it wants, exactly as the
draft prints `on_tick` again in the figure of a layer that changes it. What a reading repeats
from the layer below is figure content, the same as `Fig1.getHead` and `Fig4.getHead`
repeating the walk.

## One instance, and moving it is how a layer takes over

The same discipline as `GoldfishWalk` (`Defs/GoldfishWalk.lean`). The class carries **exactly
one** instance: two would leave the protocol's tick to instance resolution. A later layer
takes it over by moving the instance to its own reading, not by adding a second, and every
superseded reading stays a plain `Fig<n>.onTick` that nothing calls.
-/

set_option autoImplicit false

namespace DC

variable {Validator : Type} [Roots] [Params]

/-- The protocol's tick: the reading of `on_tick` the assembled protocol has. Exactly one
    instance exists, supplied by the layer whose reading is the protocol's. -/
class Tick (Validator : Type) [Roots] [Params] where
  /-- Run the instant `t`: set the clock, then whatever the schedule puts there.
      `is_proposer` is ambient in the protocol's figures, which write `on_tick(Σ, t)`. -/
  onTick : (S : Store Validator) → (t : Int) →
    (isProposer : (s : Nat) → (i : Validator) → Bool) → NDREB Validator (Store Validator)

/-- `on_tick(Σ, t)`, as the figures call it: the instance's reading, reached by dot notation,
    so a caller writes `S.onTick t is_proposer` and means whichever tick the assembled
    protocol has. -/
abbrev Store.onTick [Tick Validator] (S : Store Validator) (t : Int)
    (isProposer : (s : Nat) → (i : Validator) → Bool) : NDREB Validator (Store Validator) :=
  Tick.onTick S t isProposer

end DC
