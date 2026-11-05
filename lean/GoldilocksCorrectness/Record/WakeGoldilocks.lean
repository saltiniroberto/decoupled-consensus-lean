module
public import GoldilocksCorrectness.Record.WakeFacts
public import GoldilocksCorrectness.Record.ModelGoldilocks
import all Goldilocks.Node

@[expose] public section

/-!
# The spec's wake facts

`wakeFacts_goldilocks`: the spec's model satisfies `WakeFacts`. At `Model.goldilocks` a wake is the
spec's `wake n t`, the node state `n` with `awakeSince` set to none and the clock set to `t`; each
field holds by definition
(this page sees the spec's body of `wake`: the landed `wake_eq` of
`GoldilocksCorrectness/Proofs/Routines/Node.lean` is proved the same way).
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Record

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The spec's model satisfies the facts about the wake.

Read aloud: a Goldilocks wake forgets the wake time, sets the clock to the wake time, and changes
nothing else. -/
theorem wakeFacts_goldilocks : WakeFacts (Model.goldilocks (V := V)) where
  wake_awakeSince := fun _ _ => rfl
  wake_readers := fun _ _ =>
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- In the spec's model two wakes in a row are one wake, at the second time: a wake sets
`awakeSince` and the clock only, so the second wake overwrites both writes of the first.

The variables:
- `n`: the node state; `t₁`, `t₂`: the times of the two wakes.

Read aloud: a Goldilocks node woken at `t₁` and then at `t₂` is in the state of the node woken at
`t₂` only. -/
theorem wakeWake_goldilocks : ∀ (n : (Model.goldilocks (V := V)).N) (t₁ t₂ : Goldilocks.Time),
    (Model.goldilocks (V := V)).wake ((Model.goldilocks (V := V)).wake n t₁) t₂ =
      (Model.goldilocks (V := V)).wake n t₂ :=
  fun _ _ _ => rfl

end GoldilocksCorrectness.Record
