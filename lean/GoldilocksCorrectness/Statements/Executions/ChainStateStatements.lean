module
public import GoldilocksCorrectness.Proofs.Executions.ChainState
public import GoldilocksCorrectness.Statements.Routines.ChainStateStatements

@[expose] public section

/-!
# The statements about the chain states along a chain

The audited statements about the chain state a block has, `chainStateOf C B` (the initial chain
state for the genesis block, and for any other block the state transition from its parent's),
proved in `GoldilocksCorrectness/Proofs/Executions/ChainState.lean`: Lemma 47 (the heights along a
chain, and the block `T_h` that took the chain into each height) and its corollary
`J_eq_T_h_of_same_height` (the justified block at a height on the chain is that height's `T_h`).
-/

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V]

/-- **Corollary of Lemma 47, the justified block at a height is the block that took the chain
there.** When `B` is an ancestor of `D` or `D` itself, and `D`'s chain state has the justification
height `B`'s height, the justified block of `D`'s chain state is `B`'s `T_h`.

Why: the justification height is at least `1`, since `B`'s height is; a justification at a height
`H ≥ 1` was written at an ancestor-or-self of `D` whose parent had the height `H` and whose `T_h`
it took; that parent and `B` are on `D`'s chain at the same height, so they have the same `T_h`
(Lemma 47 (e)).

The variables:
- `C`: the parameters; `B`: the block at the justification height; `D`: the block whose
  justification is read.

Read aloud: when `D`'s chain justified the height of `B`, it justified the block that took `B`'s
chain into that height.

 -/
theorem J_eq_T_h_of_same_height (C : Config) (B D : Block V)
    -- `B` is an ancestor of `D`, or `D` itself
    (hBD : B.AncestorEq D)
    -- `D`'s chain state has the justification height `B`'s height
    (hJ : (chainStateOf C D).h_j = (chainStateOf C B).h) :
    (chainStateOf C D).J = (chainStateOf C B).T_h :=
  GoldilocksCorrectness.Proofs.Executions.J_eq_T_h_of_same_height C B D hBD hJ

end GoldilocksCorrectness.Statements.Executions
