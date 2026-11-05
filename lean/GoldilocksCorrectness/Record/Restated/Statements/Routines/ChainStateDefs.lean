module
public import GoldilocksCorrectness.Record.ModelSpellings
public import GoldilocksCorrectness.Record.ModelGoldilocks
public import GoldilocksCorrectness.Statements.Routines.ChainStateDefs

@[expose] public section

/-!
# The entry block of a chain, over a model

`IsEntry M C E`: the block `E` is the block that took its chain into its height, read on the
chain state `M.chainStateOf C E`. It is the definition `IsEntry` of
`GoldilocksCorrectness/Statements/Routines/ChainStateDefs.lean` over a model `M`. The chain state of
a block is the record's member `M.chainStateOf C B`, so the page's other definition, `chainStateOf`,
has no twin. At the spec's model `IsEntry` is the landed definition (the equation
`goldilocks_IsEntry`, in the simp set `record_goldilocks`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Record

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `IsEntry M C E`: the block that took the chain of `E` into its height, the `T_h` of the chain
state `M.chainStateOf C E`, is `E` itself.

The variables:
- `M`: the model;
- `C`: the parameters; `E`: the block.

Read aloud: `E` is the block that took its own chain into its height, in the model `M`. -/
def IsEntry (M : GoldilocksModel V) (C : Config) (E : Block V) : Prop :=
  (M.chainStateOf C E).T_h = E

/-! ## At the spec's model -/

/-- At the spec's model, `IsEntry` is the landed definition.

The variables:
- `C`, `E`: as in `IsEntry`, at the spec's model.

Read aloud: the spec's model has the landed `IsEntry`. -/
@[record_goldilocks]
theorem goldilocks_IsEntry (C : Config) (E : Block V) :
    GoldilocksCorrectness.Statements.Routines.IsEntry C E =
      IsEntry (Model.goldilocks (V := V)) C E := rfl

end GoldilocksCorrectness.Record.Statements.Routines
