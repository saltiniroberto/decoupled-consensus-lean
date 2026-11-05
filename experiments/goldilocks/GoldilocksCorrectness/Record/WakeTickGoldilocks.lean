module
public import GoldilocksCorrectness.Record.ModelGoldilocks
import all Goldilocks.Node

@[expose] public section

/-!
# The spec's tick after a wake does not depend on the wake's time

`wakeTick_goldilocks`: at `Model.goldilocks`, the outcomes of a tick from a woken node state are
the same whatever time was given to the wake. The spec's `wake n a` is `n` with `awakeSince` set to
none and the clock set to `a`; the spec's `tick` first runs `record_awake`, which reads and writes
`awakeSince` only, and then sets the clock to the tick's time before it reads anything else, so the
clock `a` is overwritten before it is read (this page sees the spec's bodies of `wake`,
`record_awake` and `tick`).

The hypothesis `hWakeTick` of `runFacts_ofAtomic`
(`Record/Restated/Proofs/AbstractTrace/OfAtomic.lean`) is this statement at a general model.
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Record

open Goldilocks (Config Provisional External RootOrder Time NodeState record_awake wake)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- At the spec's model, a tick's outcomes from a woken node state do not depend on the time given
to the wake.

Why: `wake n a` and `wake n b` differ in the clock only; `record_awake` keeps the clock, and the
tick sets the clock to its own time `r` right after `record_awake`, so from there on the two runs
of the tick read the same node state.

The variables:
- `C`, `P`, `X`: the parameters, the values and the digest; `n`: the node state; `a`, `b`: the two
  wake times; `r`: the tick's time.

Read aloud: at the spec's model, waking at `a` or at `b` makes no difference to the next tick. -/
theorem wakeTick_goldilocks [RootOrder] (C : Config) (P : Provisional V) (X : External V)
    (n : (Model.goldilocks (V := V)).N) (a b r : Time) :
    (Model.goldilocks (V := V)).tick C P X ((Model.goldilocks (V := V)).wake n a) r =
      (Model.goldilocks (V := V)).tick C P X ((Model.goldilocks (V := V)).wake n b) r := by
  show (Goldilocks.tick C P X (wake n a) r).outcomes = (Goldilocks.tick C P X (wake n b) r).outcomes
  -- `record_awake` after a wake at `c` is the same state with the clock `c`
  have h : ∀ c : Time, record_awake (wake n c) r =
      { record_awake { n with awakeSince := none } r with t := c } := fun _ => rfl
  unfold Goldilocks.tick
  simp only [h]

end GoldilocksCorrectness.Record
