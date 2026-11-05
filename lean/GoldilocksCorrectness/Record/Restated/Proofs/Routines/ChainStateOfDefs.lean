module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ChainStateDefs
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOf

@[expose] public section

/-!
# A justification on a chain, over a model

The definition `JustifiedOnChainWith` of `GoldilocksCorrectness/Proofs/Routines/ChainStateOf.lean`
over a model `M`. It is on a page of its own, which imports no facts, so that the facts of the
chain-state family may name it. At the spec's model it is the landed definition (the equation
`goldilocks_JustifiedOnChainWith`, in the simp set `record_goldilocks`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Record.Statements.Routines (IsEntry)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `JustifiedOnChainWith M C H OnChain B`: when the justification height of `B`'s chain state is
greater than `H`, the justified block of that chain state satisfies `OnChain`, is the block that
took its chain into its height, and has that justification height as its own chain-state height.

The variables:
- `M`: the model;
- `C`: the parameters; `H`: the height; `OnChain`: the condition on blocks; `B`: the block.

Read aloud: a justification of `B`'s chain at a height greater than `H` is of a block that
satisfies `OnChain` and entered that height. -/
def JustifiedOnChainWith (M : GoldilocksModel V) (C : Config) (H : ℕ) (OnChain : Block V → Prop)
    (B : Block V) : Prop :=
  H < (M.chainStateOf C B).h_j →
    OnChain (M.chainStateOf C B).J ∧ IsEntry M C (M.chainStateOf C B).J ∧
      (M.chainStateOf C (M.chainStateOf C B).J).h = (M.chainStateOf C B).h_j

/-! ## At the spec's model -/

/-- At the spec's model, `JustifiedOnChainWith` is the landed definition.

The variables:
- `C`, `H`, `OnChain`, `B`: as in `JustifiedOnChainWith`, at the spec's model.

Read aloud: the spec's model has the landed `JustifiedOnChainWith`. -/
@[record_goldilocks]
theorem goldilocks_JustifiedOnChainWith (C : Config) (H : ℕ) (OnChain : Block V → Prop)
    (B : Block V) :
    GoldilocksCorrectness.Proofs.Routines.JustifiedOnChainWith C H OnChain B =
      JustifiedOnChainWith (Model.goldilocks (V := V)) C H OnChain B := rfl

end GoldilocksCorrectness.Record.Proofs.Routines
