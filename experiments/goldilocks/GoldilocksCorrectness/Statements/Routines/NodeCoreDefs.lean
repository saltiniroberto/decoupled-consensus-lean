module
public import GoldilocksCorrectness.Statements.Routines.NodeDefs

@[expose] public section

/-!
# The node invariant split: its clock-free part and its clock part

`NodeInv` (`NodeDefs.lean`) is the conjunction of eleven clauses. Two of them compare a stamp with
the node's clock: `StampsBounded` and `StampOrder`. `NodeInvCore` is the other nine, in their order;
`NodeInvClock` is the two. `NodeInv` itself is unchanged; the two projections relating the three are
in `Proofs/Routines/NodeCore.lean`.
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Statements.Routines

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

/-- `NodeInvCore C P X n`: the clauses of `NodeInv C P X n` that read no clock, in their order:
`PoolKeyed`, `PoolStamped`, `TreeClosed`, the finalized block in the tree, `TreeStamped`,
`ChainStatesComputed`, `AttestationsValid`, then `RootsNameBlocksIn`, `FinalizedAncestorJustified`,
`HeightCacheBounds`, `JustificationCacheBounds`, `JustifiedHeight`, `JustifiedInTree`,
`LockBelowJustified`, `RecordConsistent`, and `PoolAttestationsWellFormed`. `NodeInv` is this
together with `NodeInvClock`.

The variables:
- `C`: the parameters; `P`: the provisional values; `X`: the external values; `n`: the node state.

Read aloud: everything the node invariant says that does not compare a stamp with the clock. -/
def NodeInvCore (C : Config) (P : Provisional V) (X : External V) (n : NodeState V) : Prop :=
  PoolKeyed P n.A ∧ PoolStamped n.A ∧ TreeClosed P X n.S ∧ n.S.F ∈ n.S.T ∧ TreeStamped n ∧
    ChainStatesComputed C n.S ∧ AttestationsValid n.S ∧
      (RootsNameBlocksIn n.S.T ∧ (FinalizedAncestorJustified n.S ∧ HeightCacheBounds n.S) ∧
        (JustificationCacheBounds n.S ∧ JustifiedHeight n.S ∧ JustifiedInTree n.S ∧
          LockBelowJustified n ∧ RecordConsistent n.Λ)) ∧
        PoolAttestationsWellFormed n.S

/-- `NodeInvClock n`: the two clauses of `NodeInv` that compare a stamp with the clock,
`StampsBounded n` and `StampOrder n`.

The variables:
- `n`: the node state.

Read aloud: nothing the node holds is stamped later than its clock, and a block is stamped no
earlier than its parent. -/
def NodeInvClock (n : NodeState V) : Prop := StampsBounded n ∧ StampOrder n

end

end GoldilocksCorrectness.Statements.Routines
