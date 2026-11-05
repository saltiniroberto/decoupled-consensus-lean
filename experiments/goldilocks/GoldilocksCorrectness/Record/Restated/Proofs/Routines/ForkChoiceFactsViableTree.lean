module
public import GoldilocksCorrectness.Record.Facts
public import GoldilocksCorrectness.Proofs.Routines.ForkChoiceFacts

@[expose] public section

/-!
# ForkChoiceFactsViableTree, over a model

The theorem of `GoldilocksCorrectness/Proofs/Routines/ForkChoiceFacts.lean` on the reader
`viable_tree` alone, over a model `M` whose facts `F` hold: when every viable head descends
from `B`, no block of a viable tree conflicts with `B`.

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
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_compatible compatible_iff)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- When every viable head descends from `B`, every block of the viable tree of any tree is
compatible with `B`.

The variables:
- `M`: the model; `F`: its facts;
- `Φ`: the frame; `tree`: the tree; `B`: the block.

Read aloud: when every viable head is `B` or a descendant of `B`, no block of a viable tree
conflicts with `B`. -/
theorem viable_tree_compatible [RootOrder] (Φ : Frame V) (tree : Finset (Block V)) (B : Block V)
    (hH : ∀ W ∈ Φ.viable_heads, B.AncestorEq W) :
    ∀ D ∈ M.viable_tree Φ tree, D.compatible B = true := by
  intro D hD
  simp only [F.rd.viable_tree_eq, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hD
  obtain ⟨-, -, W, hW, hDW⟩ := hD
  have hBW := hH W (Finset.mem_inter.1 hW).2
  exact (compatible_iff _ _).2 (ancestorEq_compatible hDW hBW)

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.viable_tree_compatible`,
recovered from its record form at the spec's model.

Read aloud: the landed `viable_tree_compatible` holds, as the record's theorem at the spec's
model. -/
theorem viable_tree_compatible_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.viable_tree_compatible V _ _ _) := by
  exact viable_tree_compatible Model.goldilocks goldilocksFacts

end GoldilocksCorrectness.Record.Proofs.Routines
