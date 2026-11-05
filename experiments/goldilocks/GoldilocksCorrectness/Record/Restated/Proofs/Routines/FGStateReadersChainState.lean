module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOf

@[expose] public section

/-!
# FGStateReadersChainState, over a model

The chain-state theorem of `GoldilocksCorrectness/Proofs/Routines/FGStateReaders.lean` over a model
`M` whose facts `F` hold: an attestation included on a chain at the chain's height is counted. The
page's other theorems are about the readers of a node state: they are restated with family E.

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

/-- **Kit fact, an attestation on a chain is counted.** When the attestation `a` is on the chain
of `H`, every attestation a non-genesis block of that chain includes is valid against its parent's
chain state, and `a` is at the height of `H`'s chain state, then `a`'s validator is in the progress
set of `H`'s chain state, and in its target participation when `a` is a target.

Why: the block that includes `a` has a parent at height at least `a.h` by validity, hence exactly
`a.h`, the height of `H`; that block counts `a`, and the chain keeps its counts up to `H` at that
height.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `H`: the block; `a`: the attestation.

Read aloud: a vote at the chain's height already included on the chain is already counted. -/
theorem on_chain_counted (C : Config) (H : Block V) (a : Attestation V)
    (hon : M.on_chain a H = true)
    (hValid : ∀ Y : Block V, Y.AncestorEq H → Y ≠ Block.genesis →
      ∀ a' ∈ Y.attestations, M.valid_attestation (M.chainStateOf C Y.parent) a' = true)
    (hh : a.h = (M.chainStateOf C H).h) :
    a.val_index ∈ (M.chainStateOf C H).progress ∧
      (a.τ = false → a.val_index ∈ (M.chainStateOf C H).target_participation) :=
  F.cs.on_chain_counted C H a hon hValid hh

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.on_chain_counted`,
recovered from its record form at the spec's model.

Read aloud: the landed `on_chain_counted` holds, as the record's theorem at the spec's
model. -/
theorem on_chain_counted_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.on_chain_counted V _ _) := by
  exact on_chain_counted Model.goldilocks goldilocksFacts

end GoldilocksCorrectness.Record.Proofs.Routines
