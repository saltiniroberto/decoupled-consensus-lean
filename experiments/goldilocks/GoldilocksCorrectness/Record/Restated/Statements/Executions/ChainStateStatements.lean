module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ChainState
public import GoldilocksCorrectness.Statements.Routines.ChainStateStatements

@[expose] public section

/-!
# ChainStateStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/ChainStateStatements.lean` over a
model `M` whose facts `F` hold.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Executions

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Record.Statements.Routines (IsEntry JustificationCertOn ProgressCertOn FinalityCertOn)
open GoldilocksCorrectness.Record.Proofs.Routines (JustifiedOnChainWith)
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
there.** When `B` is an ancestor of `D` or `D` itself, and `D`'s chain state has the justification
height `B`'s height, the justified block of `D`'s chain state is `B`'s `T_h`.

Why: the justification height is at least `1`, since `B`'s height is; a justification at a height
`H ≥ 1` was written at an ancestor-or-self of `D` whose parent had the height `H` and whose `T_h`
it took; that parent and `B` are on `D`'s chain at the same height, so they have the same `T_h`
(Lemma 47 (e)).

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `B`: the block at the justification height; `D`: the block whose
  justification is read.

Read aloud: when `D`'s chain justified the height of `B`, it justified the block that took `B`'s
chain into that height.

 -/
theorem J_eq_T_h_of_same_height (C : Config) (B D : Block V)
    -- `B` is an ancestor of `D`, or `D` itself
    (hBD : B.AncestorEq D)
    -- `D`'s chain state has the justification height `B`'s height
    (hJ : (M.chainStateOf C D).h_j = (M.chainStateOf C B).h) :
    (M.chainStateOf C D).J = (M.chainStateOf C B).T_h :=
  (GoldilocksCorrectness.Record.Proofs.Executions.J_eq_T_h_of_same_height M F) C B D hBD hJ

end

end GoldilocksCorrectness.Record.Statements.Executions
