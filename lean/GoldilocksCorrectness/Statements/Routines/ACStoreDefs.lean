module
public import Goldilocks.AC.State

@[expose] public section

/-!
# Conditions on the Goldfish vote pool of an AC state

`PoolKeyed P A`: every Goldfish vote filed under a slot `s` in `A` has the slot `s` and a
validator of the committee `P.committee s`; `PoolStamped A`: every Goldfish vote filed in `A` has
a stamp. Nothing is proved here.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `PoolKeyed P A`: every Goldfish vote filed under a slot `s` in `A` has the slot `s` and a
validator of the committee `P.committee s`.

The variables:
- `P`: the values given to the node, with the committees; `A`: the AC state.

Read aloud: the pool is filed by slot, and holds only committee members' votes. -/
def PoolKeyed (P : Provisional V) (A : ACState V) : Prop :=
  ∀ s : Slot, ∀ vote ∈ A.gf_votes s, vote.slot = s ∧ vote.val_index ∈ P.committee s

/-- `PoolStamped A`: every Goldfish vote filed in `A` has a stamp.

The variables:
- `A`: the AC state.

Read aloud: every vote of the pool is stamped. -/
def PoolStamped (A : ACState V) : Prop :=
  ∀ s : Slot, ∀ vote ∈ A.gf_votes s, A.timestamp_vote vote ≠ none

end

end GoldilocksCorrectness.Statements.Routines
