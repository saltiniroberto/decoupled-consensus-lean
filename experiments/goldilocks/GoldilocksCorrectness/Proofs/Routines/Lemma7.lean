module
public import GoldilocksCorrectness.Proofs.Routines.Blocks
public import GoldilocksCorrectness.Statements.Routines.WalkDefs
import all Goldilocks.AC.ForkChoice

@[expose] public section

/-!
# Lemma 7: a start compatible with a block starts towards it in the viable tree

The proof of `lem7_startsTowards_of_compatible`, stated in
`GoldilocksCorrectness/Statements/Routines/LockStatements.lean`.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V]

/-- **Lemma 7, a start compatible with a block starts towards it in the viable tree.** A start
`X` compatible with `R` starts towards `R` in the viable tree of `tree`, when `Φ.fc_root` is an
ancestor of `X` or `X`, every block after `X` up to `R` is in `tree`, and `tree` holds a viable
head `W` of the frame that is `R` or a descendant of `R`.

Why: when `R` is `X` or an ancestor of `X`, that is the first case of `StartsTowards`. Otherwise
`X` is an ancestor of `R`, and every block `P` after `X` up to `R` is in `tree`, has `Φ.fc_root`
as an ancestor through `X`, and is an ancestor of `W` through `R`: it is in the viable tree.

The variables:
- `Φ`: the frame; `tree`: the tree whose viable tree is walked;
- `X`: the start; `R`: the block the walk is to reach; `W`: the viable head. -/
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
    StartsTowards X R (viable_tree Φ tree) := by
  rcases (compatible_iff X R).1 hXR with hXR' | hRX
  · refine Or.inr ⟨hXR', fun P hXP hPX hPR => ?_⟩
    simp only [viable_tree, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hPath P hXP hPX hPR, ancestorEq_trans hRootX hXP,
      W, Finset.mem_inter.2 hW, ancestorEq_trans hPR hRW⟩
  · exact Or.inl hRX

end GoldilocksCorrectness.Proofs.Routines
