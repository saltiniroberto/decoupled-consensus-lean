module
public import GoldilocksCorrectness.Statements.Executions.InvariantDefs
public import GoldilocksCorrectness.Proofs.Routines.ChainState
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOf

@[expose] public section

/-!
# The chain-state facts along a chain

The proofs of the statements of
`GoldilocksCorrectness/Statements/Executions/ChainStateStatements.lean`: Lemma 47 over the chain
state a block has, `chainStateOf C B`, and its corollary `J_eq_T_h_of_same_height`.

The route: `chainStateOf` is the state transition from the parent's chain state, so parts (a) to
(c) are the routine-level parts of `Proofs/Routines/ChainState.lean` by induction on the block
(part (a) carrying the bound on the pending justifications); parts (d) and (e) are inductions on
ancestry. The corollary goes through `exists_ancestor_of_h_j`: a justification height `H ≥ 1` of a
chain state is the height of an ancestor-or-self whose `T_h` is the justified block.
-/

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_T_h_of_same_height chainStateOf_bounds
  exists_ancestor_of_h_j)

namespace GoldilocksCorrectness.Proofs.Executions

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (chainStateOf)
open GoldilocksCorrectness.Proofs.Routines (lem47a_state_transition_bounds
  lem47b_state_transition_height lem47c_state_transition_T_h state_transition_justification
  ancestorEq_node_iff ancestorEq_genesis_iff ancestorEq_refl ancestorEq_trans
  ancestorEq_compatible ancestorEq_antisymm)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

omit [RootOrder] in
/-- **Corollary of Lemma 47, the justified block at a height is the block that took the chain
there.** The proof; the audited statement is in
`Statements/Executions/ChainStateStatements.lean`.

The variables:
- `C`: the parameters; `B`: the ancestor; `D`: the descendant. -/
theorem J_eq_T_h_of_same_height (C : Config) (B D : Block V)
    (hBD : B.AncestorEq D) (hJ : (chainStateOf C D).h_j = (chainStateOf C B).h) :
    (chainStateOf C D).J = (chainStateOf C B).T_h := by
  obtain ⟨h1, -, -, -⟩ := chainStateOf_bounds C B
  obtain ⟨Y, hYD, hYh, hYT⟩ := exists_ancestor_of_h_j C D _ hJ h1
  rw [← hYT]
  rcases ancestorEq_compatible hYD hBD with hYB | hBY
  · exact chainStateOf_T_h_of_same_height C hYB hYh
  · exact (chainStateOf_T_h_of_same_height C hBY hYh.symm).symm

end GoldilocksCorrectness.Proofs.Executions
