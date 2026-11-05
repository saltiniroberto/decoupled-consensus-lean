module
public import GoldilocksCorrectness.Record.InitialAddedFacts
public import GoldilocksCorrectness.Record.ModelGoldilocks
public import GoldilocksCorrectness.Proofs.Routines.FGState
public import GoldilocksCorrectness.Proofs.Routines.Node

@[expose] public section

/-!
# The spec's initial node state: the least height of a viable block

`initialAddedFacts_goldilocks`: the spec's model satisfies `InitialAddedFacts`. The initial node
state's FG state is `FGState.initial` (`initial_eq`), whose `head_height_floor` is `0` (the
library's `head_height_floor_initial`).
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Record

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The spec's model satisfies the added facts of the initial node state.

Read aloud: Goldilocks' initial node state has the least height of a viable block at `0`. -/
theorem initialAddedFacts_goldilocks : InitialAddedFacts (Model.goldilocks (V := V)) where
  head_height_floor_initial C v := by
    show Goldilocks.head_height_floor (Goldilocks.initial C v).S = 0
    rw [GoldilocksCorrectness.Proofs.Routines.initial_eq]
    exact GoldilocksCorrectness.Proofs.Routines.head_height_floor_initial

end GoldilocksCorrectness.Record
