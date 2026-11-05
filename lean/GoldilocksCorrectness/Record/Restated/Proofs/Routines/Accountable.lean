module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOf

@[expose] public section

/-!
# Accountable, over a model

The theorems of `GoldilocksCorrectness/Proofs/Routines/Accountable.lean` over a model `M` whose
facts `F` hold that need no step along a chain for an included attestation: a chain state with
finalization height `0` has the genesis block finalized.

The recovery section at the end of the page states each landed theorem again, as the
landed statement (`type_of%`), and proves it from its record form at the spec's model
`Model.goldilocks` and its facts `goldilocksFacts`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

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

/-- A chain state with finalization height `0` has the genesis block as its finalized block.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `B`: the block.

Read aloud: a chain state with finalization height `0` has the genesis block finalized. -/
theorem chainStateOf_F_genesis (C : Config) (B : Block V)
    -- the finalization height of the chain state of `B` is `0`
    (h0 : (M.chainStateOf C B).h_F = 0) :
    (M.chainStateOf C B).F = Block.genesis :=
  F.cs.chainStateOf_F_genesis C B h0

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.chainStateOf_F_genesis`,
recovered from its record form at the spec's model.

Read aloud: the landed `chainStateOf_F_genesis` holds, as the record's theorem at the spec's
model. -/
theorem chainStateOf_F_genesis_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.chainStateOf_F_genesis V _ _) := by
  exact chainStateOf_F_genesis Model.goldilocks goldilocksFacts

end GoldilocksCorrectness.Record.Proofs.Routines
