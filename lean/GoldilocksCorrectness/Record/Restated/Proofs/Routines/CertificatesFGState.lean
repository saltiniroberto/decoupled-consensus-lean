module
public import GoldilocksCorrectness.Record.Facts

@[expose] public section

/-!
# CertificatesFGState, over a model

The theorems of `GoldilocksCorrectness/Proofs/Routines/Certificates.lean` on the readers
`on_chain` and `attestations_on_chain`, over a model `M` whose facts `F` hold: an
attestation on the parent's chain, or included in the block, is on the block's chain. (The
page's chain-state theorems are restated on `Record/Restated/Proofs/Routines/Certificates.lean`.)

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

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- An attestation included on the parent's chain is included on the block's chain.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: an attestation on the parent's chain is on the block's chain. -/
theorem on_chain_node_of_parent (a : Attestation V) (p : Block V) (s : Slot) (r : BlockId)
    (votes support : List (GoldfishVote V)) (ats : List (Attestation V)) (v : V)
    -- `a` is included on the parent's chain
    (h : M.on_chain a p = true) :
    M.on_chain a (.node p s r votes support ats v) = true := by
  simp only [F.rd.on_chain_eq, F.rd.attestations_on_chain_node, decide_eq_true_eq, List.mem_append] at h ⊢
  exact Or.inr h

/-- An attestation the block includes is included on the block's chain.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: an attestation the block includes is on the block's chain. -/
theorem on_chain_node_of_mem (a : Attestation V) (p : Block V) (s : Slot) (r : BlockId)
    (votes support : List (GoldfishVote V)) (ats : List (Attestation V)) (v : V)
    -- the block includes `a`
    (h : a ∈ ats) :
    M.on_chain a (.node p s r votes support ats v) = true := by
  simp only [F.rd.on_chain_eq, F.rd.attestations_on_chain_node, decide_eq_true_eq, List.mem_append]
  exact Or.inl h

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.on_chain_node_of_parent`,
recovered from its record form at the spec's model.

Read aloud: the landed `on_chain_node_of_parent` holds, as the record's theorem at the spec's
model. -/
theorem on_chain_node_of_parent_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.on_chain_node_of_parent V _) := by
  exact on_chain_node_of_parent Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.on_chain_node_of_mem`,
recovered from its record form at the spec's model.

Read aloud: the landed `on_chain_node_of_mem` holds, as the record's theorem at the spec's
model. -/
theorem on_chain_node_of_mem_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.on_chain_node_of_mem V _) := by
  exact on_chain_node_of_mem Model.goldilocks goldilocksFacts

end GoldilocksCorrectness.Record.Proofs.Routines
