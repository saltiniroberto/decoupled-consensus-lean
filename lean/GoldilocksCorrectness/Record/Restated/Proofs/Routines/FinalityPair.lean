module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOf

@[expose] public section

/-!
# FinalityPair, over a model

The chain-state theorem of `GoldilocksCorrectness/Proofs/Routines/FinalityPair.lean` over a model
`M` whose facts `F` hold: Lemma 93, a block including a quorum of finality pairs finalizes the
pending pair.

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

/-- **Lemma 93, a block including a quorum of finality pairs finalizes the pair.** The proof; the
audited statement is in `Statements/Routines/FinalityPairStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `B`: the block; `H'`: its parent; `j`: the pending height; `T`: the
  pending block; `Q`: the quorum.

Read aloud: a block that brings a quorum of finality pairs for a pending justification finalizes it. -/
theorem lem93_block_finalizes_pending (C : Config) (B H' : Block V) (j : Height) (T : Block V)
    (Q : Finset V)
    (hParent : B.parent = H')
    (hPending : ∃ e ∈ (M.chainStateOf C H').pending_finality, e.j = j ∧ e.T = T)
    (hQ : M.quorumAt B ≤ |Q|)
    (hAtts : ∀ v ∈ Q, v ∈ (M.chainStateOf C H').finality_participation j ∨
      ∃ a ∈ B.attestations, a.val_index = v ∧ a.finality_pair = some (FinalityPair.mk j T.root)) :
    j ≤ (M.chainStateOf C B).h_F :=
  F.cs.lem93_block_finalizes_pending C B H' j T Q hParent hPending hQ hAtts

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.lem93_block_finalizes_pending`,
recovered from its record form at the spec's model.

Read aloud: the landed `lem93_block_finalizes_pending` holds, as the record's theorem at the spec's
model. -/
theorem lem93_block_finalizes_pending_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.lem93_block_finalizes_pending V _ _) := by
  exact lem93_block_finalizes_pending Model.goldilocks goldilocksFacts

end GoldilocksCorrectness.Record.Proofs.Routines
