module
public import Goldilocks.FG.State

@[expose] public section

/-!
# The cache `h_max` is the height of a block of the tree

`HeightCacheAttained S`: a condition on one FG state `S`, stated in its docstring. Nothing is
proved here. With `HeightCacheBounds S` (`Statements/Routines/FGStateDefs.lean`) it says that
`S.h_max` is the greatest chain-state height of a block of the tree `S.T`.

Added for the record migration, step L1: the record has no member for `h_max`; the
library reads it as the greatest chain-state height of the tree, and this condition is what lets
Goldilocks' stored `h_max` be read that way.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

section

open Goldilocks
variable {V : Type}

/-- `HeightCacheAttained S`: some block `B` of the tree `S.T` of the FG state `S` has the
chain-state height `(S.σ B).h` equal to the cache `S.h_max`.

The variables:
- `S`: the FG state.

Read aloud: the cache `h_max` is the chain-state height of some block of the tree. -/
def HeightCacheAttained (S : FGState V) : Prop := ∃ B ∈ S.T, (S.σ B).h = S.h_max

end

end GoldilocksCorrectness.Statements.Routines
