module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Statements.Executions.InvariantDefs
public import GoldilocksCorrectness.Proofs.Routines.ChainState
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.RunFactsDefs
public import GoldilocksCorrectness.Statements.AbstractTrace.DeliveryDefs
public import GoldilocksCorrectness.Statements.Executions.UnforgeabilityDefs

@[expose] public section

/-!
# ChainState, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/ChainState.lean` over a model `M` whose
facts `F` hold: the justified block at a height is the block that took the chain there.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Executions

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Record.Statements.Routines (IsEntry JustificationCertOn ProgressCertOn FinalityCertOn)
open GoldilocksCorrectness.Record.Proofs.Routines (JustifiedOnChainWith)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_compatible)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- **Corollary of Lemma 47, the justified block at a height is the block that took the chain
there.** The proof; the audited statement is in
`Statements/Executions/ChainStateStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `B`: the ancestor; `D`: the descendant.

Read aloud: the justified block at a height is the block that took the chain there. -/
theorem J_eq_T_h_of_same_height (C : Config) (B D : Block V)
    (hBD : B.AncestorEq D) (hJ : (M.chainStateOf C D).h_j = (M.chainStateOf C B).h) :
    (M.chainStateOf C D).J = (M.chainStateOf C B).T_h := by
  obtain ⟨h1, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_bounds M F) C B
  obtain ⟨Y, hYD, hYh, hYT⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.exists_ancestor_of_h_j M F) C D _ hJ h1
  rw [← hYT]
  rcases ancestorEq_compatible hYD hBD with hYB | hBY
  · exact (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_T_h_of_same_height M F) C hYB hYh
  · exact ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_T_h_of_same_height M F) C hBY hYh.symm).symm

end

end GoldilocksCorrectness.Record.Proofs.Executions
