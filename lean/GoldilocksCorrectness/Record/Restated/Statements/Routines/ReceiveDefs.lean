module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ChainStateDefs
public import GoldilocksCorrectness.Statements.Routines.ReceiveDefs

@[expose] public section

/-!
# ReceiveDefs, over a model

The definition of `GoldilocksCorrectness/Statements/Routines/ReceiveDefs.lean` over a model `M`,
read on a node state `n : M.N`: the node's justification height is greater than a threshold, its
justified block is compatible with a block, is an entry block and has that chain-state height, and
its finalized block is its justified block or an ancestor of it.

The recovery section at the end of the page states, for each definition, the equation
`goldilocks_<name>`: at the spec's model the definition is the landed one.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Record.Statements.Routines

section

open Goldilocks
open Goldilocks.Sts (Setup)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)

section

variable (S : Setup V)

/-- `CachesCompatibleWith M S B H n`: the justification height `n.justifiedHeight` is greater than
`H`; the justified block `n.justified` is compatible with `B`, is an entry block, and has the
chain-state height `n.justifiedHeight`; the finalized block `n.finalized` is `n.justified` or an
ancestor of it.

The variables:
- `M`: the model;
- `S`: the setup; `B`: the protected block; `H`: the height threshold; `n`: the node state.

Read aloud: the node's caches do not conflict with `B`, and its justified block is an entry at a
height greater than `H`. -/
def CachesCompatibleWith (B : Block V) (H : ℕ) (n : M.N) : Prop :=
  H < n.justifiedHeight ∧ (n.justified.AncestorEq B ∨ B.AncestorEq n.justified) ∧
    IsEntry M S.C n.justified ∧
    (M.chainStateOf S.C n.justified).h = n.justifiedHeight ∧ n.finalized.AncestorEq n.justified

end

end

end GoldilocksCorrectness.Record.Statements.Routines

namespace GoldilocksCorrectness.Record.Statements.Routines

open scoped DC
open DC (DRE)
open Goldilocks
open Goldilocks.Sts (Setup)

/-! ## At the spec's model -/

/-- At the spec's model, `CachesCompatibleWith` is the landed definition.

The variables:
- as in `CachesCompatibleWith`, at the spec's model.

Read aloud: the spec's model has the landed `CachesCompatibleWith`. -/
@[record_goldilocks]
theorem goldilocks_CachesCompatibleWith {V : Type} [DecidableEq V] [Fintype V] (S : Setup V)
    (B : Block V) (H : ℕ) (n : NodeState V) :
    GoldilocksCorrectness.Statements.Routines.CachesCompatibleWith S B H n =
      CachesCompatibleWith Model.goldilocks S B H n := by
  simp only [GoldilocksCorrectness.Statements.Routines.CachesCompatibleWith,
    CachesCompatibleWith, record_goldilocks]

end GoldilocksCorrectness.Record.Statements.Routines
