module
public import GoldilocksCorrectness.Statements.Routines.ChainStateDefs
public import GoldilocksSts

@[expose] public section

/-!
# A condition on a node state's FG caches, relative to a block

`CachesCompatibleWith S B H n`: the justification height of the node state `n` is greater than `H`,
its justified block is compatible with the block `B`, is an entry block and has the chain-state
height `n.S.h_j`, and its finalized block is its justified block or an ancestor of it. Nothing is
proved here.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

section

open Goldilocks
open Goldilocks.Sts (Setup)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

section

variable (S : Setup V)

/-- `CachesCompatibleWith S B H n`: the justification height `n.S.h_j` is greater than `H`; the
justified block `n.S.J` is compatible with `B`, is an entry block, and has the chain-state height
`n.S.h_j`; the finalized block `n.S.F` is `n.S.J` or an ancestor of it.

The variables:
- `S`: the setup; `B`: the protected block; `H`: the height threshold; `n`: the node state.

Read aloud: the node's caches do not conflict with `B`, and its justified block is an entry at a
height greater than `H`. -/
def CachesCompatibleWith (B : Block V) (H : ℕ) (n : NodeState V) : Prop :=
  H < n.S.h_j ∧ (n.S.J.AncestorEq B ∨ B.AncestorEq n.S.J) ∧ IsEntry S.C n.S.J ∧
    (chainStateOf S.C n.S.J).h = n.S.h_j ∧ n.S.F.AncestorEq n.S.J

end

end

end GoldilocksCorrectness.Statements.Routines
