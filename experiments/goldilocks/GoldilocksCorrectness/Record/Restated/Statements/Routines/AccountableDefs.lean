module
public import GoldilocksCorrectness.Record.ModelSpellings
public import GoldilocksCorrectness.Record.ModelGoldilocks
public import GoldilocksCorrectness.Statements.Routines.AccountableDefs

@[expose] public section

/-!
# The slashable pairs between two chains, over a model

`SlashableBetween M B B'`: the definition of
`GoldilocksCorrectness/Statements/Routines/AccountableDefs.lean` with the record's member
`M.on_chain` in place of the spec's `on_chain`. At the spec's model it is the landed definition
(`goldilocks_SlashableBetween`, in the simp set `record_goldilocks`). The page's other definitions,
`E1`, `E2`, `RootsNameBlocksOn`, `RootCollisionOn` and `RootCollisionIn`, name no member of the
record: they are shared, used as they are.
-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks (Block Attestation quorum validator_count)
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Statements.Routines (E1 E2)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `SlashableBetween M B B'`: at least `2 * quorum V - validator_count V` validators each signed
two attestations, one included in `B` or an ancestor of `B` and the other in `B'` or an ancestor
of `B'`, in either order, that together meet `E1` or `E2`; inclusion read by the model's
`M.on_chain`.

The variables:
- `M`: the model; `B`, `B'`: the two blocks whose chains hold the attestations.

Read aloud: at least `2q − n` validators each signed two attestations, one included on each of
the two chains, that together meet E1 or E2. -/
def SlashableBetween (M : GoldilocksModel V) (B B' : Block V) : Prop :=
  ∃ A : Finset V, 2 * quorum V - validator_count V ≤ |A| ∧
    ∀ v ∈ A, ∃ a a' : Attestation V, a.val_index = v ∧ a'.val_index = v ∧
      ((M.on_chain a B = true ∧ M.on_chain a' B' = true) ∨
        (M.on_chain a' B = true ∧ M.on_chain a B' = true)) ∧
      (E1 a a' ∨ E2 a a')

/-! ## At the spec's model -/

/-- At the spec's model, `SlashableBetween` is the landed definition.

The variables:
- `B`, `B'`: the two blocks.

Read aloud: the spec's model has the spec's slashable pairs. -/
@[record_goldilocks]
theorem goldilocks_SlashableBetween (B B' : Block V) :
    GoldilocksCorrectness.Statements.Routines.SlashableBetween B B' =
      SlashableBetween (Model.goldilocks (V := V)) B B' := rfl

end GoldilocksCorrectness.Record.Statements.Routines
