module
public import GoldilocksCorrectness.Record.ModelSpellings

@[expose] public section

/-!
# The initial node state: the least height of a viable block

`InitialAddedFacts M` holds, for a model `M`, what the derived reader `head_height_floor` answers on
the node state `M.initial C v` a node of the validator `v` starts from. Added beside `InitialFacts`
(whose fields are not changed). This file holds the structure only.
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Record

open Goldilocks (Config)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The facts of `M` about the initial node state added beside `InitialFacts`.

Read aloud: a node starts with the least chain-state height of a viable block at `0`. -/
structure InitialAddedFacts (M : GoldilocksModel V) : Prop where
  /-- On the initial state, the least chain-state height a viable block may have,
      `M.head_height_floor`, is `0`.

      Read aloud: a node starts with the least height of a viable block at `0`. -/
  head_height_floor_initial : ∀ (C : Config) (v : V), M.head_height_floor (M.initial C v) = 0

end GoldilocksCorrectness.Record
