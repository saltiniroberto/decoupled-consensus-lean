module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FinalityPair
public import GoldilocksCorrectness.Statements.Routines.FinalityPairStatements

@[expose] public section

/-!
# FinalityPairStatements, over a model

The chain-state statement of `GoldilocksCorrectness/Statements/Routines/FinalityPairStatements.lean`
over a model `M` whose facts `F` hold: Lemma 93.

The recovery section at the end of the page states each landed theorem again, as the
landed statement (`type_of%`), and proves it from its record form at the spec's model
`Model.goldilocks` and its facts `goldilocksFacts`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Routines

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

/-- **Lemma 93, a block including a quorum of finality pairs finalizes the pair.** When the chain
state of `B`'s parent `H'` has a pending justification at the height `j` naming the block `T`, and
every member `v` of a quorum `Q` is counted in the parent's finality participation at `j` or has
an attestation included in `B` with the finality pair `(j, T.root)`, the chain state of `B` has a
finalization height at least `j`.

Why: counting `B`'s attestations adds every such `v` to the finality participation at `j` (the
pair names a pending justification) and keeps those already there, so the participation at `j` is
a quorum; the pending justifications are in strictly increasing order of heights, so the first
step of `process_height_events` leaves the quorate pending justification of greatest height, at a
height at least `j`; nothing after it writes `h_F`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `B`: the block; `H'`: its parent;
- `j`, `T`: the height and the block of the pending justification; `Q`: the quorum.

Read aloud: a quorum's finality pairs finalize what they name.

 -/
theorem lem93_block_finalizes_pending (C : Config) (B H' : Block V) (j : Height) (T : Block V)
    (Q : Finset V)
    -- `H'` is `B`'s parent
    (hParent : B.parent = H')
    -- the parent's chain state has a pending justification at `j` naming `T`
    (hPending : ∃ e ∈ (M.chainStateOf C H').pending_finality, e.j = j ∧ e.T = T)
    -- `Q` is a quorum
    (hQ : M.quorumAt B ≤ |Q|)
    -- every member of `Q` is counted at `j` in the parent's chain state, or has an attestation
    -- included in `B` with the finality pair `(j, T.root)`
    (hAtts : ∀ v ∈ Q, v ∈ (M.chainStateOf C H').finality_participation j ∨
      ∃ a ∈ B.attestations, a.val_index = v ∧ a.finality_pair = some (FinalityPair.mk j T.root)) :
    j ≤ (M.chainStateOf C B).h_F :=
  (GoldilocksCorrectness.Record.Proofs.Routines.lem93_block_finalizes_pending M F) C B H' j T Q hParent
    hPending hQ hAtts

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Statements.Routines.lem93_block_finalizes_pending`,
recovered from its record form at the spec's model.

Read aloud: the landed `lem93_block_finalizes_pending` holds, as the record's theorem at the spec's
model. -/
theorem lem93_block_finalizes_pending_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Statements.Routines.lem93_block_finalizes_pending V _ _) := by
  exact lem93_block_finalizes_pending Model.goldilocks goldilocksFacts

end GoldilocksCorrectness.Record.Statements.Routines
