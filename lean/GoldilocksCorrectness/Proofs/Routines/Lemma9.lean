module
public import GoldilocksCorrectness.Proofs.Routines.Merge

@[expose] public section

/-!
# Lemma 9: the walk ends at the proposal of a shared block

The proof of `lem9_walk_ends_at_proposal_of_shared_block`, stated in
`GoldilocksCorrectness/Statements/Routines/WalkStatements.lean`: the merge `ghost_merge` of
`Proofs/Routines/Merge.lean`.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V] [RootOrder]

/-- **Lemma 9, the walk ends at the proposal of a shared block.** Two walks: the first, from `A_p`
over `tree_p`, ends at `P`'s parent; the second, from `A_w` over `tree_w`, ends at `H_w`. If the
two scores answer the same number on every child of a block from `X` to `P`'s parent, the first
walk passes `X`, the second starts at `X` or an ancestor of `X` and passes `X`, the blocks of the
first walk after `X` and `P` are in `tree_w`, `P` is eligible in the second walk and has no child
in `tree_w`, the second test accepts every block after `X` up to `P`'s parent, and every child in
`tree_w` of a block from `X` to `P`'s parent, other than `P`, that the second test accepts is in
`tree_p` and accepted by the first test, then the second walk ends at `P`.

Why: up to `X` the second walk follows its own steps; from `X` to `P`'s parent it takes the steps
of the first (`ghost_step_transfer`); at `P`'s parent `P` is its only eligible child, since the
first walk stopped there (`ghost_step_none_of_ghost_eq`, `ghost_step_none_not_eligible`,
`ghost_step_eq_of_only`); at `P` it stops (`ghost_step_none_of_no_child`); so it ends at `P`
(`ghost_reaches`).



The variables:
- `A_p`, `tree_p`, `score_p`, `eligible_p`: the first walk; `A_w`, `tree_w`, `score_w`,
  `eligible_w`: the second; `H_w`: where the second ends;
- `X`: the block both pass; `P`: the block after the first walk's end;
- `n`: the scores' answers; `b_p`, `b_w`: the two tests' answers. -/
theorem lem9_walk_ends_at_proposal_of_shared_block {A_p A_w X P H_w : Block V}
    {tree_p tree_w : Finset (Block V)}
    {score_p score_w : Block V → DRE Nat} {eligible_p eligible_w : Block V → DRE Bool}
    (n : Block V → ℕ) (b_p b_w : Block V → Bool)
    -- the first score answers `n D` on every child `D` of a block from `X` to `P`'s parent
    (hScoreP : ∀ Y : Block V, X.AncestorEq Y → Y.AncestorEq P.parent →
      ∀ D : Block V, D.parent? = some Y → score_p D = .ok (n D))
    -- the second score answers `n D` on every child `D` of a block from `X` to `P`'s parent
    (hScoreW : ∀ Y : Block V, X.AncestorEq Y → Y.AncestorEq P.parent →
      ∀ D : Block V, D.parent? = some Y → score_w D = .ok (n D))
    -- the first test answers `b_p D` on every block `D`
    (hTestP : ∀ D : Block V, eligible_p D = .ok (b_p D))
    -- the second test answers `b_w D` on every block `D`
    (hTestW : ∀ D : Block V, eligible_w D = .ok (b_w D))
    -- no two blocks of `tree_p` share a root
    (hRootsP : RootsNameBlocksIn tree_p)
    -- `P` is a child of its parent: `P` is not the genesis block
    (hPpar : P.parent? = some P.parent)
    -- the first walk ends at `P`'s parent
    (hWalkP : ghost A_p tree_p score_p eligible_p = .ok P.parent)
    -- the second walk ends at `H_w`
    (hWalkW : ghost A_w tree_w score_w eligible_w = .ok H_w)
    -- `X` is `A_p` or a descendant of it, and `P`'s parent or an ancestor of it
    (hXOnWalkP : A_p.AncestorEq X ∧ X.AncestorEq P.parent)
    -- `X` is `A_w` or a descendant of it
    (hRootWX : A_w.AncestorEq X)
    -- `X` is `H_w` or an ancestor of it
    (hXW : X.AncestorEq H_w)
    -- every block after `X` up to `P`'s parent is in `tree_w`
    (hPathInTreeW : ∀ Y : Block V, X.AncestorEq Y → Y ≠ X → Y.AncestorEq P.parent → Y ∈ tree_w)
    -- `P` is in `tree_w`
    (hPInTree : P ∈ tree_w)
    -- the second test answers `true` on `P`
    (hPTest : b_w P = true)
    -- no block of `tree_w` is a child of `P`
    (hNoChildP : ∀ D ∈ tree_w, D.parent? ≠ some P)
    -- the second test answers `true` on every block after `X` up to `P`'s parent
    (hPathTest : ∀ Y : Block V, X.AncestorEq Y → Y ≠ X → Y.AncestorEq P.parent → b_w Y = true)
    -- every child in `tree_w` of a block from `X` to `P`'s parent, other than `P`, on which the
    -- second test answers `true`, is in `tree_p` and the first test answers `true` on it
    (hEligSub : ∀ Y : Block V, X.AncestorEq Y → Y.AncestorEq P.parent →
      ∀ D ∈ tree_w, D.parent? = some Y → D ≠ P → b_w D = true → D ∈ tree_p ∧ b_p D = true) :
    -- then the second walk ends at `P`
    H_w = P :=
  ghost_merge n b_p b_w hScoreP hScoreW hTestP hTestW hRootsP hPpar hWalkP hWalkW hXOnWalkP
    hRootWX hXW hPathInTreeW hPInTree hPTest hNoChildP hPathTest hEligSub

end GoldilocksCorrectness.Proofs.Routines
