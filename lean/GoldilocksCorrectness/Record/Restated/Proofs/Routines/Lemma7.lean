module
public import GoldilocksCorrectness.Record.Facts
public import GoldilocksCorrectness.Proofs.Routines.Lemma7

@[expose] public section

/-!
# Lemma 7, over a model

The theorem of `GoldilocksCorrectness/Proofs/Routines/Lemma7.lean` over a model `M` whose facts `F`
hold: a start compatible with a block starts towards it in the viable tree `M.viable_tree Φ tree`.
It reads a frame and a tree, not a node state, and is stated as landed with the model's viable
tree.

The recovery section at the end of the page states the landed theorem again, as the landed
statement (`type_of%`), and proves it from its record form at the spec's model `Model.goldilocks`
and its facts `goldilocksFacts`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Statements.Routines (StartsTowards)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans compatible_iff)

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- **Lemma 7, a start compatible with a block starts towards it in the viable tree.** A start
`X` compatible with `R` starts towards `R` in the viable tree of `tree`, when `Φ.fc_root` is an
ancestor of `X` or `X`, every block after `X` up to `R` is in `tree`, and `tree` holds a viable
head `W` of the frame that is `R` or a descendant of `R`.

Why: when `R` is `X` or an ancestor of `X`, that is the first case of `StartsTowards`. Otherwise
`X` is an ancestor of `R`, and every block `P` after `X` up to `R` is in `tree`, has `Φ.fc_root`
as an ancestor through `X`, and is an ancestor of `W` through `R`: it is in the viable tree.

The variables:
- `M`: the model; `F`: its facts;
- `Φ`: the frame; `tree`: the tree whose viable tree is walked;
- `X`: the start; `R`: the block the walk is to reach; `W`: the viable head.

Read aloud: Lemma 7: a start `X` compatible with `R`, with the fgroot `Φ.fc_root` an ancestor of `X`
or `X`, every block after `X` up to `R` in `tree`, and a viable head of `Φ` in `tree` that is `R` or
a descendant of `R`, starts towards `R` in the viable tree of `tree`. -/
theorem lem7_startsTowards_of_compatible (Φ : Frame V) (tree : Finset (Block V))
    (X R W : Block V)
    -- `X` is compatible with `R`
    (hXR : X.compatible R = true)
    -- `Φ.fc_root` is `X` or an ancestor of `X`
    (hRootX : Φ.fc_root.AncestorEq X)
    -- every block after `X` up to `R`, `R` included, is in `tree`
    (hPath : ∀ P : Block V, X.AncestorEq P → P ≠ X → P.AncestorEq R → P ∈ tree)
    -- `W` is a block of `tree` and a viable head of the frame
    (hW : W ∈ tree ∧ W ∈ Φ.viable_heads)
    -- `W` is `R` or a descendant of `R`
    (hRW : R.AncestorEq W) :
    -- then `X` starts towards `R` in the viable tree of `tree`
    StartsTowards X R (M.viable_tree Φ tree) := by
  rcases (compatible_iff X R).1 hXR with hXR' | hRX
  · refine Or.inr ⟨hXR', fun P hXP hPX hPR => ?_⟩
    simp only [F.rd.viable_tree_eq, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hPath P hXP hPX hPR, ancestorEq_trans hRootX hXP,
      W, Finset.mem_inter.2 hW, ancestorEq_trans hPR hRW⟩
  · exact Or.inl hRX

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.lem7_startsTowards_of_compatible`, recovered
from its record form at the spec's model.

Read aloud: the landed `lem7_startsTowards_of_compatible` holds, as the record's theorem at the
spec's model. -/
theorem lem7_startsTowards_of_compatible_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.lem7_startsTowards_of_compatible V _) := by
  exact lem7_startsTowards_of_compatible Model.goldilocks goldilocksFacts

end GoldilocksCorrectness.Record.Proofs.Routines
