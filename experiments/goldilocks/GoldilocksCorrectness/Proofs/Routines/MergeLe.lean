module
public import GoldilocksCorrectness.Proofs.Routines.Merge
import all Goldilocks.AC.ForkChoice

@[expose] public section

/-!
# The merge of two walks with the score argument

Two walks with the same scores on the children of a path: the first, from `A_p` over `tree_p`,
ends at the parent of a block `P`; the second, from `A_w` over `tree_w`, ends at `H_w`. This file
proves that the second walk ends at `P` (`ghost_merge_le`) when, at each block of the path before
`P`'s parent, every child the second test accepts is a child the first walk could step to, or
scores less than every child of that block on the path that the first test accepts; and, at `P`'s
parent, every child other than `P` the second test accepts is a child the first test accepts.

- One step, read on two walks: `ghost_step_transfer_le` (a step the first walk takes is the step
  the second takes, when each child the second test accepts is a child the first test accepts or
  scores less than the first walk's choice).
- The merge: `ghost_merge_le`.


-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V] [RootOrder]

/-- When the walk over `tree` steps from `Y` to `C`, the walk over `tree'` steps from `Y` to `C`
too, if the two scores give every child of `Y` the same answer, `C` is an eligible block of
`tree'`, and every eligible child of `Y` in `tree'` is an eligible child of `Y` in `tree` or has a
score less than `C`'s.

Why: `C` outranks every eligible child of `Y` in `tree` (`outranks_of_argmax?_eq_some`); a child
with a score less than `C`'s is outranked by `C` too; so `C` outranks every eligible child of `Y`
in `tree'`, and `argmax?` picks it there (`argmax?_eq_some_of_outranks`).

The variables:
- `tree`, `score`, `eligible`: the first walk; `tree'`, `score'`, `eligible'`: the second;
- `Y`: the block stepped from; `C`: the block stepped to; `n`: the scores' answers;
- `b`, `b'`: the two tests' answers on the children of `Y`.

Read aloud: the second walk takes the first walk's step from `Y` when every child the second
walk could step to either is one the first could step to or scores less than the first's choice.

 -/
theorem ghost_step_transfer_le {tree tree' : Finset (Block V)} {score score' : Block V → DRE Nat}
    {eligible eligible' : Block V → DRE Bool} {Y C : Block V} (n : Block V → ℕ)
    (b b' : Block V → Bool)
    -- the first score answers `n D` on every child `D` of `Y`
    (hScore : ∀ D : Block V, D.parent? = some Y → score D = .ok (n D))
    -- the second score answers `n D` on every child `D` of `Y`
    (hScore' : ∀ D : Block V, D.parent? = some Y → score' D = .ok (n D))
    -- the first test answers `b D` on every child `D` of `Y` in `tree`
    (hTest : ∀ D ∈ tree, D.parent? = some Y → eligible D = .ok (b D))
    -- the second test answers `b' D` on every child `D` of `Y` in `tree'`
    (hTest' : ∀ D ∈ tree', D.parent? = some Y → eligible' D = .ok (b' D))
    -- the first walk steps from `Y` to `C`
    (h : ghost_step tree score eligible Y = .ok (some C))
    -- `C` is in `tree'`, and the second test answers `true` on it
    (hC : C ∈ tree' ∧ b' C = true)
    -- every child of `Y` in `tree'` the second test passes is in `tree` and passes the first, or
    -- has a score less than `C`'s
    (hSub : ∀ D ∈ tree', D.parent? = some Y → b' D = true →
      (D ∈ tree ∧ b D = true) ∨ n D < n C) :
    -- then the second walk steps from `Y` to `C`
    ghost_step tree' score' eligible' Y = .ok (some C) := by
  have hch := ghost_children_eq b hTest
  have hch' := ghost_children_eq b' hTest'
  unfold ghost_step at h ⊢
  rw [hch] at h
  rw [hch']
  simp only [bind, Except.bind] at h ⊢
  obtain ⟨hCmem, hdom⟩ := outranks_of_argmax?_eq_some n
    (fun D hD => hScore D (Finset.mem_filter.1 hD).2.1) h
  obtain ⟨-, hCpar, -⟩ := Finset.mem_filter.1 hCmem
  refine argmax?_eq_some_of_outranks (Finset.mem_filter.2 ⟨hC.1, hCpar, hC.2⟩) n
    (fun D hD => hScore' D (Finset.mem_filter.1 hD).2.1) (fun D hD hne => ?_)
  obtain ⟨hDt, hDpar, hDb⟩ := Finset.mem_filter.1 hD
  rcases hSub D hDt hDpar hDb with ⟨hDt', hDb'⟩ | hlt
  · exact hdom D (Finset.mem_filter.2 ⟨hDt', hDpar, hDb'⟩) hne
  · exact Or.inl hlt

/-- **The merge with the score argument.** Two walks whose scores agree on the children of the
blocks from `X` to `P`'s parent: the first, from `A_p` over `tree_p`, ends at `P`'s parent; the
second, from `A_w` over `tree_w`, ends at `H_w`. If the first walk passes `X`, the second starts
at `X` or an ancestor of `X` and passes `X`, the blocks after `X` up to `P`'s parent and `P` are
in `tree_w`, the second test accepts `P` and every block after `X` up to `P`'s parent, `P` has no
child in `tree_w`; if every child in `tree_w` of a block from `X` to `P`'s parent, other than that
parent, that the second test accepts, is in `tree_p` and accepted by the first test, or has a
score less than that of every child of that block in `tree_p` that is `P`'s parent or an ancestor
of it and that the first test accepts; and if every child of `P`'s parent in `tree_w`, other than
`P`, that the second test accepts, is in `tree_p` and accepted by the first test, then the second
walk ends at `P`.

Why: up to `X` the second walk follows its own steps; from `X` to `P`'s parent the first walk
steps to a child `C` on the path, accepted by the first test and in `tree_p`
(`ghost_step_some`), so every child the second test accepts is one the first walk could step to
or scores less than `C`, and the second walk steps to `C` (`ghost_step_transfer_le`); at `P`'s
parent `P` is its only eligible child, since the first walk stopped there
(`ghost_step_none_of_ghost_eq`, `ghost_step_none_not_eligible`, `ghost_step_eq_of_only`); at `P`
it stops (`ghost_step_none_of_no_child`); so it ends at `P` (`ghost_reaches`).

The variables:
- `A_p`, `tree_p`, `score_p`, `eligible_p`: the first walk; `A_w`, `tree_w`, `score_w`,
  `eligible_w`: the second; `H_w`: where the second ends;
- `X`: the block both pass; `P`: the block after the first walk's end;
- `n`: the scores' answers; `b_p`, `b_w`: the two tests' answers.

Read aloud: when, along the path, each child the second walk could step to is one the first walk
could step to or loses to every child of the path the first walk accepts, and at the end of the
first walk only `P` is left to the second, the second walk ends at `P`.

 -/
theorem ghost_merge_le {A_p A_w X P H_w : Block V} {tree_p tree_w : Finset (Block V)}
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
    -- every child in `tree_w` of a block `Y` from `X` to `P`'s parent, other than that parent, on
    -- which the second test answers `true`, is in `tree_p` with the first test answering `true`
    -- on it, or has a score less than every child of `Y` in `tree_p` that is `P`'s parent or an
    -- ancestor of it and on which the first test answers `true`
    (hEligSubLe : ∀ Y : Block V, X.AncestorEq Y → Y.AncestorEq P.parent → Y ≠ P.parent →
      ∀ D ∈ tree_w, D.parent? = some Y → b_w D = true →
        (D ∈ tree_p ∧ b_p D = true) ∨
          ∀ D' ∈ tree_p, D'.parent? = some Y → D'.AncestorEq P.parent → b_p D' = true →
            n D < n D')
    -- every child in `tree_w` of `P`'s parent, other than `P`, on which the second test answers
    -- `true`, is in `tree_p` and the first test answers `true` on it
    (hEligSubEnd : ∀ D ∈ tree_w, D.parent? = some P.parent → D ≠ P → b_w D = true →
      D ∈ tree_p ∧ b_p D = true) :
    -- then the second walk ends at `P`
    H_w = P := by
  -- from `X` up to `P`'s parent, the second walk takes the first walk's steps
  have hStep : ∀ Y : Block V, X.AncestorEq Y → Y.AncestorEq P.parent → Y ≠ P.parent →
      ∃ C : Block V, ghost_step tree_w score_w eligible_w Y = .ok (some C) ∧
        C.AncestorEq P.parent := by
    intro Y hXY hYH hne
    obtain ⟨C, hstepC, hCpar, hCH⟩ :=
      ghost_step_of_visited hWalkP Y (ancestorEq_trans hXOnWalkP.1 hXY) hYH hne
    have hXC : X.AncestorEq C := ancestorEq_trans hXY (ancestorEq_of_parent? hCpar)
    have hCX : C ≠ X := by
      intro h
      have h1 := depth_of_parent? hCpar
      have h2 := depth_le_of_ancestorEq hXY
      rw [h] at h1
      omega
    -- the first walk's choice `C` is in `tree_p` and accepted by the first test
    obtain ⟨hCp, -, hCe⟩ := ghost_step_some hstepC
    have hCb : b_p C = true := by
      rw [hTestP C] at hCe
      exact Except.ok.inj hCe
    refine ⟨C, ghost_step_transfer_le n b_p b_w (hScoreP Y hXY hYH) (hScoreW Y hXY hYH)
      (fun D _ _ => hTestP D) (fun D _ _ => hTestW D) hstepC
      ⟨hPathInTreeW C hXC hCX hCH, hPathTest C hXC hCX hCH⟩
      (fun D hD hDpar hDb => ?_), hCH⟩
    rcases hEligSubLe Y hXY hYH hne D hD hDpar hDb with hin | hlt
    · exact Or.inl hin
    · exact Or.inr (hlt C hCp hCpar hCH hCb)
  -- at `P`'s parent, the second walk steps to `P`
  have hStepH : ghost_step tree_w score_w eligible_w P.parent = .ok (some P) := by
    have hno := ghost_step_none_not_eligible n b_p
      (hScoreP P.parent hXOnWalkP.2 (ancestorEq_refl _)) (fun D _ _ => hTestP D) hRootsP
      (ghost_step_none_of_ghost_eq hWalkP)
    refine ghost_step_eq_of_only n b_w (hScoreW P.parent hXOnWalkP.2 (ancestorEq_refl _))
      (fun D _ _ => hTestW D) hPInTree hPpar hPTest (fun D hD hDpar hDb => ?_)
    by_contra hDP
    obtain ⟨hDp, hbp⟩ := hEligSubEnd D hD hDpar hDP hDb
    have h := hno D hDp hDpar
    rw [hbp] at h
    cases h
  have hHP : P.parent.AncestorEq P := ancestorEq_of_parent? hPpar
  have hXP : X.AncestorEq P := ancestorEq_trans hXOnWalkP.2 hHP
  have hReach : ghost A_w tree_w score_w eligible_w = .ok P := by
    refine ghost_reaches (ancestorEq_trans hRootWX hXP) (fun C hAC hCA hCP => ?_)
      (ghost_step_none_of_no_child hNoChildP) (fun Y hAY hYP hYne => ?_)
    · -- the path from `A_w` to `P` is in `tree_w`
      by_cases hCeq : C = P
      · rw [hCeq]
        exact hPInTree
      by_cases hCX : C.AncestorEq X
      · exact visited_mem_tree hWalkW C hAC hCA (ancestorEq_trans hCX hXW)
      · have hXC : X.AncestorEq C := (ancestorEq_compatible hCP hXP).resolve_left hCX
        have hCX' : C ≠ X := fun h => hCX (h ▸ ancestorEq_refl _)
        exact hPathInTreeW C hXC hCX' (ancestorEq_parent_of_ne hCP hCeq)
    · -- every block before `P` steps towards `P`
      have hYH : Y.AncestorEq P.parent := ancestorEq_parent_of_ne hYP hYne
      by_cases hXY : X.AncestorEq Y
      · by_cases hYeq : Y = P.parent
        · rw [hYeq]
          exact ⟨P, hStepH, ancestorEq_refl _⟩
        · obtain ⟨C, hC, hCH⟩ := hStep Y hXY hYH hYeq
          exact ⟨C, hC, ancestorEq_trans hCH hHP⟩
      · have hYX : Y.AncestorEq X := (ancestorEq_compatible hYP hXP).resolve_right hXY
        have hXY' : X ≠ Y := fun h => hXY (h ▸ ancestorEq_refl _)
        have hYHw : Y ≠ H_w := fun h => hXY (h ▸ hXW)
        obtain ⟨C, hC, hCpar, hCHw⟩ :=
          ghost_step_of_visited hWalkW Y hAY (ancestorEq_trans hYX hXW) hYHw
        exact ⟨C, hC, ancestorEq_trans
          (child_ancestorEq_of_between hYX hXY' hXW hCpar hCHw) hXP⟩
  exact Except.ok.inj (hWalkW.symm.trans hReach)

end GoldilocksCorrectness.Proofs.Routines
