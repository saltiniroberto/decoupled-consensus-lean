module
public import GoldilocksCorrectness.Proofs.Routines.NodeTick

@[expose] public section

/-!
# The tick raises no error

`tick_ok`: from a node state satisfying the node invariant `NodeInv`, at a time no earlier than its
clock, the tick answers. Proved in `Proofs/Routines/NodeTick.lean`.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

section

open Goldilocks
open GoldilocksCorrectness.Proofs.Routines (DREBOk)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **The node's tick answers.** From a node state satisfying `NodeInv`, the tick at a time no
earlier than the node's clock answers, whatever was sent before it (`DREBOk`: from every list of
objects sent so far, the tick returns a node state and the objects sent, rather than failing).

Why: the spec fails only when a root names two blocks of the node's tree, or when a vote or a block
it reads has no stamp, and three clauses of `NodeInv` exclude all three; the proposal and the
attestation duty run on node states that satisfy `NodeInv` too.

Read aloud: a node whose state satisfies the node invariant never fails a tick at a time no
earlier than its clock.

The variables:
- `C`: the configuration; `P`: the provisional parameters; `X`: the digest; `n`: the node state;
  `t`: the time of the tick. -/
theorem tick_ok (C : Config) (P : Provisional V) (X : External V) (n : NodeState V) (t : Time)
    (h : NodeInv C P X n) (ht : n.t ≤ t) : DREBOk (tick C P X n t) :=
  GoldilocksCorrectness.Proofs.Routines.tick_ok C P X n t h ht

end

end GoldilocksCorrectness.Statements.Routines
