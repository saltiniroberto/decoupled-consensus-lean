module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.CertificatesFGState
public import GoldilocksCorrectness.Proofs.Routines.Accountable

@[expose] public section

/-!
# AccountableFGState, over a model

The theorem of `GoldilocksCorrectness/Proofs/Routines/Accountable.lean` on the reader
`on_chain`, over a model `M` whose facts `F` hold: an attestation on a block's chain is on
the chain of each of its descendants. (The page's other theorems are restated on
`Record/Restated/Proofs/Routines/Accountable.lean`, `AccountableValidatorClient.lean` and
`AccountableChains.lean`.)

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
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_genesis_iff ancestorEq_node_iff)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- An attestation included on the chain of `Y` is included on the chain of every block of which
`Y` is an ancestor, or which is `Y`.

The variables:
- `M`: the model; `F`: its facts;
- `a`: the attestation; `Y`: the block whose chain includes it; `B`: the descendant.

Read aloud: an attestation on a block's chain is on the chain of each of its descendants. -/
theorem on_chain_mono (a : Attestation V) {Y B : Block V}
    -- `Y` is `B` or an ancestor of `B`
    (hYB : Y.AncestorEq B)
    -- `a` is included on the chain of `Y`
    (h : M.on_chain a Y = true) :
    M.on_chain a B = true := by
  induction B with
  | genesis =>
      rw [(ancestorEq_genesis_iff Y).1 hYB] at h
      exact h
  | node p s r votes support ats v ih =>
      rcases (ancestorEq_node_iff _ _ _ _ _ _ _ _).1 hYB with hY | hY
      · rw [hY] at h
        exact h
      · exact (on_chain_node_of_parent M F) a p s r votes support ats v (ih hY)

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.on_chain_mono`,
recovered from its record form at the spec's model.

Read aloud: the landed `on_chain_mono` holds, as the record's theorem at the spec's
model. -/
theorem on_chain_mono_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.on_chain_mono V _) := by
  exact on_chain_mono Model.goldilocks goldilocksFacts

end GoldilocksCorrectness.Record.Proofs.Routines
