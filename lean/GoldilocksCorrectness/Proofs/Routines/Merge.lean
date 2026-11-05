module
public import GoldilocksCorrectness.Proofs.Routines.WalkMerge
public import GoldilocksCorrectness.Statements.Routines.WalkDefs
import all Goldilocks.AC.ForkChoice

@[expose] public section

/-!
# The merge of two walks that share a block

Two walks with the same scores: the first, from `A_p` over `tree_p`, ends at the parent of a
block `P`; the second, from `A_w` over `tree_w`, ends at `H_w`. This file proves that, when the
two walks share a block `X` and the tests agree where the walks look, the second walk ends at `P`
(`ghost_merge`).

- On blocks: `parent?_eq_some_parent`, `parent_eq_of_parent?`, `ancestorEq_parent_of_ne`.
- One step, read on two walks: `ghost_step_transfer` (a step the first walk takes is the step the
  second takes, when the second's eligible children are among the first's and include the first's
  choice), `ghost_step_eq_of_only` (a step with one eligible child takes it),
  `ghost_step_none_not_eligible` (a step that answers none has no eligible child, when roots name
  the blocks of the tree), with `exists_root_before_none` for the tie through `RootOrder.before`.
- The merge: `ghost_merge`, over any two walks whose scores agree on the children of the first
  walk's blocks from the shared block on; `ghost_visited_test_true` (every block a walk passes
  after its start passes the walk's test), for callers that compare the two tests.

A port, renaming only, of the part of
`experiments/correctness/Correctness/Proofs/SpecDraft/GoldfishMerge.lean` that reads no state,
with the tie of `outranks` read through `RootOrder.before`.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V] [RootOrder]

omit [DecidableEq V] [RootOrder] in
/-- A block other than the genesis block has its parent as `parent?`.

The variables:
- `B`: the block. -/
theorem parent?_eq_some_parent {B : Block V}
    -- `B` is not the genesis block
    (h : B ≠ Block.genesis) :
    -- then `B.parent?` is `B`'s parent
    B.parent? = some B.parent := by
  cases B with
  | genesis => exact absurd rfl h
  | node => rfl

omit [DecidableEq V] [RootOrder] in
/-- A block whose `parent?` is `H` has `H` as its parent.

The variables:
- `B`: the block; `H`: its parent. -/
theorem parent_eq_of_parent? {B H : Block V}
    -- `B`'s parent is `H`
    (h : B.parent? = some H) :
    -- then `B.parent` is `H`
    B.parent = H := by
  cases B with
  | genesis => cases h
  | node p => exact Option.some.inj h

omit [RootOrder] in
/-- An ancestor of `C` other than `C` is an ancestor of `C`'s parent, or that parent.

The variables:
- `B`: the ancestor; `C`: the block. -/
theorem ancestorEq_parent_of_ne {B C : Block V}
    -- `B` is an ancestor of `C`, or `C`
    (h : B.AncestorEq C)
    -- `B` is not `C`
    (hne : B ≠ C) :
    -- then `B` is an ancestor of `C`'s parent, or that parent
    B.AncestorEq C.parent := by
  cases C with
  | genesis => exact absurd ((ancestorEq_genesis_iff B).1 h) hne
  | node p s ib gv gs ats v =>
    rcases (ancestorEq_node_iff B p s ib gv gs ats v).1 h with h' | h'
    · exact absurd h' hne
    · exact h'

/-- When the walk over `tree` steps from `Y` to `C`, the walk over `tree'` steps from `Y` to `C`
too, if the two scores give every child of `Y` the same answer, `C` is an eligible block of
`tree'`, and every eligible child of `Y` in `tree'` is an eligible child of `Y` in `tree`.

Why: `C` outranks every eligible child of `Y` in `tree` (`outranks_of_argmax?_eq_some`), so it
outranks every eligible child of `Y` in `tree'`, and `argmax?` picks it there
(`argmax?_eq_some_of_outranks`).

The variables:
- `tree`, `score`, `eligible`: the first walk; `tree'`, `score'`, `eligible'`: the second;
- `Y`: the block stepped from; `C`: the block stepped to; `n`: the scores' answers;
- `b`, `b'`: the two tests' answers on the children of `Y`. -/
theorem ghost_step_transfer {tree tree' : Finset (Block V)} {score score' : Block V → DRE Nat}
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
    -- every child of `Y` in `tree'` the second test passes is in `tree` and passes the first
    (hSub : ∀ D ∈ tree', D.parent? = some Y → b' D = true → D ∈ tree ∧ b D = true) :
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
  obtain ⟨hDt', hDb'⟩ := hSub D hDt hDpar hDb
  exact hdom D (Finset.mem_filter.2 ⟨hDt', hDpar, hDb'⟩) hne

/-- A step from `Y` with exactly one eligible child `P` in `tree` takes `P`.

Why: `P` is then the only member of the children, and outranks every other member vacuously
(`argmax?_eq_some_of_outranks`).

The variables:
- `tree`, `score`, `eligible`: the walk; `Y`: the block stepped from; `P`: its eligible child;
- `n`: the score's answers; `b`: the test's answers on the children of `Y`. -/
theorem ghost_step_eq_of_only {tree : Finset (Block V)} {score : Block V → DRE Nat}
    {eligible : Block V → DRE Bool} {Y P : Block V} (n : Block V → ℕ) (b : Block V → Bool)
    -- the score answers `n D` on every child `D` of `Y`
    (hScore : ∀ D : Block V, D.parent? = some Y → score D = .ok (n D))
    -- the test answers `b D` on every child `D` of `Y` in `tree`
    (hTest : ∀ D ∈ tree, D.parent? = some Y → eligible D = .ok (b D))
    -- `P` is in `tree`
    (hP : P ∈ tree)
    -- `P` is a child of `Y`
    (hPpar : P.parent? = some Y)
    -- the test answers `true` on `P`
    (hPb : b P = true)
    -- every child of `Y` in `tree` the test passes is `P`
    (hOnly : ∀ D ∈ tree, D.parent? = some Y → b D = true → D = P) :
    -- then the step from `Y` takes `P`
    ghost_step tree score eligible Y = .ok (some P) := by
  unfold ghost_step
  rw [ghost_children_eq b hTest]
  simp only [bind, Except.bind]
  refine argmax?_eq_some_of_outranks (Finset.mem_filter.2 ⟨hP, hPpar, hPb⟩) n
    (fun D hD => hScore D (Finset.mem_filter.1 hD).2.1) (fun D hD hne => ?_)
  obtain ⟨hDt, hDpar, hDb⟩ := Finset.mem_filter.1 hD
  exact absurd (hOnly D hDt hDpar hDb) hne

/-- A nonempty set of blocks has a member whose root comes before the root of no member.

Why: induction on the set; the member kept is replaced by the new one when its root comes before
the new one's (`RootOrder.trans`, `RootOrder.irrefl`).

The variables:
- `T`: the set. -/
theorem exists_root_before_none (T : Finset (Block V)) (hT : T.Nonempty) :
    ∃ C ∈ T, ∀ D ∈ T, RootOrder.before C.root D.root = false := by
  induction T using Finset.induction_on with
  | empty => exact absurd hT Finset.not_nonempty_empty
  | @insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      refine ⟨a, Finset.mem_insert_self a ∅, fun D hD => ?_⟩
      simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hD
      subst hD
      exact RootOrder.irrefl _
    · obtain ⟨C, hC, hCmax⟩ := ih hs
      by_cases hCa : RootOrder.before C.root a.root = true
      · refine ⟨a, Finset.mem_insert_self a s, fun D hD => ?_⟩
        rcases Finset.mem_insert.1 hD with rfl | hD
        · exact RootOrder.irrefl _
        · cases h : RootOrder.before a.root D.root with
          | false => rfl
          | true =>
            have := RootOrder.trans _ _ _ hCa h
            rw [hCmax D hD] at this
            cases this
      · refine ⟨C, Finset.mem_insert_of_mem hC, fun D hD => ?_⟩
        rcases Finset.mem_insert.1 hD with rfl | hD
        · simpa using hCa
        · exact hCmax D hD

/-- A step from `Y` that answers none has no eligible child in `tree`, when the score answers on
every child of `Y` and no two blocks of `tree` share a root.

Why: a nonempty set of children has a member of greatest score and, among those, one whose root
comes before no other's (`exists_root_before_none`); with distinct roots every other such root
comes before its root (`RootOrder.total`), so it outranks every other member, and `argmax?` would
pick it (`argmax?_eq_some_of_outranks`).

The variables:
- `tree`, `score`, `eligible`: the walk; `Y`: the block stepped from; `n`: the score's answers;
- `b`: the test's answers on the children of `Y`. -/
theorem ghost_step_none_not_eligible {tree : Finset (Block V)} {score : Block V → DRE Nat}
    {eligible : Block V → DRE Bool} {Y : Block V} (n : Block V → ℕ) (b : Block V → Bool)
    -- the score answers `n D` on every child `D` of `Y`
    (hScore : ∀ D : Block V, D.parent? = some Y → score D = .ok (n D))
    -- the test answers `b D` on every child `D` of `Y` in `tree`
    (hTest : ∀ D ∈ tree, D.parent? = some Y → eligible D = .ok (b D))
    -- no two blocks of `tree` share a root
    (hRoots : RootsNameBlocksIn tree)
    -- the step from `Y` answers none
    (h : ghost_step tree score eligible Y = .ok none) :
    -- then the test answers `false` on every child of `Y` in `tree`
    ∀ D ∈ tree, D.parent? = some Y → b D = false := by
  intro D hD hDpar
  by_contra hb
  have hDb : b D = true := by simpa using hb
  unfold ghost_step at h
  rw [ghost_children_eq b hTest] at h
  simp only [bind, Except.bind] at h
  set children := tree.filter (fun D => D.parent? = some Y ∧ b D = true) with hchildren
  have hne : children.Nonempty := ⟨D, Finset.mem_filter.2 ⟨hD, hDpar, hDb⟩⟩
  -- a member of greatest score, then one whose root comes before no other's among those
  obtain ⟨C₀, hC₀, hC₀max⟩ := Finset.exists_max_image children n hne
  set top := children.filter (fun D => n D = n C₀) with htop
  have htne : top.Nonempty := ⟨C₀, Finset.mem_filter.2 ⟨hC₀, rfl⟩⟩
  obtain ⟨C, hC, hCmax⟩ := exists_root_before_none top htne
  obtain ⟨hCch, hCn⟩ := Finset.mem_filter.1 hC
  have hsome : argmax? score children = .ok (some C) := by
    refine argmax?_eq_some_of_outranks hCch n
      (fun D hD => hScore D (Finset.mem_filter.1 hD).2.1) (fun D' hD' hne' => ?_)
    have hle := hC₀max D' hD'
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact Or.inl (by omega)
    · refine Or.inr ⟨by omega, ?_⟩
      have hCD' := hCmax D' (Finset.mem_filter.2 ⟨hD', heq⟩)
      have hroot : D'.root ≠ C.root := fun hr =>
        hne' (hRoots D' (Finset.mem_filter.1 hD').1 C (Finset.mem_filter.1 hCch).1 hr)
      rcases RootOrder.total D'.root C.root hroot with h' | h'
      · exact h'
      · rw [hCD'] at h'
        cases h'
  rw [hsome] at h
  cases h

/-- **The merge.** Two walks whose scores agree on the children of the first walk's blocks from
`X` on: the first, from `A_p` over `tree_p`, ends at `P`'s parent; the second, from `A_w` over
`tree_w`, ends at `H_w`. If the first walk passes `X`, the second starts at or before `X` and
passes it, the blocks of the first walk after `X` and `P` are in `tree_w`, `P` is eligible in the
second walk and has no child in `tree_w`, the second test accepts every block of the first walk
after `X`, and every child in `tree_w` of a block of the first walk from `X` on, other than `P`,
that the second test accepts is in `tree_p` and passes the first test, then the second walk ends
at `P`.

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
theorem ghost_merge {A_p A_w X P H_w : Block V} {tree_p tree_w : Finset (Block V)}
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
    refine ⟨C, ghost_step_transfer n b_p b_w (hScoreP Y hXY hYH) (hScoreW Y hXY hYH)
      (fun D _ _ => hTestP D) (fun D _ _ => hTestW D) hstepC
      ⟨hPathInTreeW C hXC hCX hCH, hPathTest C hXC hCX hCH⟩
      (fun D hD hDpar hDb => ?_), hCH⟩
    have hDP : D ≠ P := by
      rintro rfl
      rw [hPpar] at hDpar
      exact hne (Option.some.inj hDpar).symm
    exact hEligSub Y hXY hYH D hD hDpar hDP hDb
  -- at `P`'s parent, the second walk steps to `P`
  have hStepH : ghost_step tree_w score_w eligible_w P.parent = .ok (some P) := by
    have hno := ghost_step_none_not_eligible n b_p
      (hScoreP P.parent hXOnWalkP.2 (ancestorEq_refl _)) (fun D _ _ => hTestP D) hRootsP
      (ghost_step_none_of_ghost_eq hWalkP)
    refine ghost_step_eq_of_only n b_w (hScoreW P.parent hXOnWalkP.2 (ancestorEq_refl _))
      (fun D _ _ => hTestW D) hPInTree hPpar hPTest (fun D hD hDpar hDb => ?_)
    by_contra hDP
    obtain ⟨hDp, hbp⟩ := hEligSub P.parent hXOnWalkP.2 (ancestorEq_refl _) D hD hDpar hDP hDb
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

/-- Every block a walk passes through after its start passes the walk's test: for a walk from `A`
over `tree` that ends at `H`, with the test answering `b D` on every block `D`, every block after
`A` up to `H` has `b` answering `true` on it.

Why: such a block `Y` is not the genesis block, and its parent is on the way from `A` to `H`
other than `H`; the walk steps from that parent to a child on the way to `H`
(`ghost_step_of_visited`), which is `Y` (`child_ancestorEq_of_between`, the two having the same
depth), and a step goes only to a block the test accepts (`ghost_step_some`).

The variables:
- `A`: the start; `H`: the end; `tree`, `score`, `eligible`: the walk; `b`: the test's answers. -/
theorem ghost_visited_test_true {A H : Block V} {tree : Finset (Block V)}
    {score : Block V → DRE Nat} {eligible : Block V → DRE Bool} (b : Block V → Bool)
    -- the test answers `b D` on every block `D`
    (hTest : ∀ D : Block V, eligible D = .ok (b D))
    -- the walk from `A` ends at `H`
    (hWalk : ghost A tree score eligible = .ok H) :
    -- then the test answers `true` on every block after `A` up to `H`
    ∀ Y : Block V, A.AncestorEq Y → Y ≠ A → Y.AncestorEq H → b Y = true := by
  intro Y hAY hYA hYH
  have hYg : Y ≠ Block.genesis := by
    rintro rfl
    exact hYA ((ancestorEq_genesis_iff A).1 hAY).symm
  have hYpar := parent?_eq_some_parent hYg
  have hAQ : A.AncestorEq Y.parent := ancestorEq_parent_of_ne hAY (Ne.symm hYA)
  have hQY : Y.parent.AncestorEq Y := ancestorEq_of_parent? hYpar
  have hdY := depth_of_parent? hYpar
  have hQH : Y.parent ≠ H := by
    intro h
    have h2 := depth_le_of_ancestorEq hYH
    rw [← h] at h2
    omega
  obtain ⟨C, hstep, hCpar, hCH⟩ :=
    ghost_step_of_visited hWalk Y.parent hAQ (ancestorEq_trans hQY hYH) hQH
  have hQYne : Y ≠ Y.parent := by
    intro h
    rw [← h] at hdY
    omega
  have hCY : C.AncestorEq Y := child_ancestorEq_of_between hQY hQYne hYH hCpar hCH
  have hCeq : C = Y := eq_of_ancestorEq_of_depth hCY (by
    rw [depth_of_parent? hCpar, hdY])
  obtain ⟨-, -, hCe⟩ := ghost_step_some hstep
  rw [hCeq, hTest Y] at hCe
  exact Except.ok.inj hCe

/-- The second test accepts every block after `X` up to `P`'s parent, when the first walk, from
`A_p`, ends at `P`'s parent and passes `X`, and the two tests agree on every child of a block
from `X` to `P`'s parent.

Why: such a block is a child of a block from `X` to `P`'s parent, so the two tests agree on it,
and the first test accepts it (`ghost_visited_test_true`).

The variables:
- `A_p`, `tree_p`, `score_p`, `eligible_p`: the first walk; `X`: the block it passes; `P`: the
  block after its end; `b_p`, `b_w`: the two tests' answers. -/
theorem path_test_of_test_agree {A_p X P : Block V} {tree_p : Finset (Block V)}
    {score_p : Block V → DRE Nat} {eligible_p : Block V → DRE Bool} (b_p b_w : Block V → Bool)
    -- the first test answers `b_p D` on every block `D`
    (hTestP : ∀ D : Block V, eligible_p D = .ok (b_p D))
    -- the first walk ends at `P`'s parent
    (hWalkP : ghost A_p tree_p score_p eligible_p = .ok P.parent)
    -- `X` is `A_p` or a descendant of it, and `P`'s parent or an ancestor of it
    (hXOnWalkP : A_p.AncestorEq X ∧ X.AncestorEq P.parent)
    -- the two tests agree on every child of a block from `X` to `P`'s parent
    (hTestAgree : ∀ Y : Block V, X.AncestorEq Y → Y.AncestorEq P.parent →
      ∀ D : Block V, D.parent? = some Y → b_w D = b_p D) :
    -- then the second test answers `true` on every block after `X` up to `P`'s parent
    ∀ Y : Block V, X.AncestorEq Y → Y ≠ X → Y.AncestorEq P.parent → b_w Y = true := by
  intro Y hXY hYX hYP
  have hYg : Y ≠ Block.genesis := by
    rintro rfl
    exact hYX ((ancestorEq_genesis_iff X).1 hXY).symm
  have hYpar := parent?_eq_some_parent hYg
  have hXQ : X.AncestorEq Y.parent := ancestorEq_parent_of_ne hXY (Ne.symm hYX)
  have hQP : Y.parent.AncestorEq P.parent := ancestorEq_trans (ancestorEq_of_parent? hYpar) hYP
  have hYA : Y ≠ A_p := by
    intro h
    have hYXa : Y.AncestorEq X := h ▸ hXOnWalkP.1
    exact hYX (ancestorEq_antisymm hXY hYXa).symm
  rw [hTestAgree Y.parent hXQ hQP Y hYpar]
  exact ghost_visited_test_true b_p hTestP hWalkP Y (ancestorEq_trans hXOnWalkP.1 hXY) hYA hYP

end GoldilocksCorrectness.Proofs.Routines
