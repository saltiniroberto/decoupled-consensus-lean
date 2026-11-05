module
public import Goldilocks.FG.ChainState

@[expose] public section

/-!
# The chain state of a block

`chainStateOf C B`: the chain state the block `B` has under the parameters `C` (the initial chain
state for the genesis block, and for any other block the state transition from its parent's);
`IsEntry C B`: the block `B` is the block that took its chain into its height. Nothing is proved
here.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `chainStateOf C B`: the chain state of the block `B` computed from `B` alone: the initial chain
state for the genesis block, and for any other block the state transition from its parent's.

Read aloud: the chain state a block has, whoever computes it. -/
def chainStateOf (C : Config) : Block V → ChainState V
  | .genesis => ChainState.initial
  | B@(.node p _ _ _ _ _ _) => state_transition C (chainStateOf C p) B

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `IsEntry C E`: the block that took the chain of `E` into its height, the `T_h` of `E`'s chain
state, is `E` itself.

The variables:
- `C`: the parameters; `E`: the block.

Read aloud: `E` is the entry block of its chain at its height. -/
def IsEntry (C : Config) (E : Block V) : Prop := (chainStateOf C E).T_h = E

end

end GoldilocksCorrectness.Statements.Routines
