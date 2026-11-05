module
public import GoldilocksCorrectness.Proofs.Routines.Walk
import all Goldilocks.AC.ForkChoice

@[expose] public section

/-!
# The Goldfish walk read backwards, from its result to its steps

`Walk.lean` reads the walk forwards: from the steps along a path, where the walk ends. This file
adds the converse readings, for the walk `ghost A tree score eligible` with the tree, the score
and the eligibility test taken as parameters. No lemma here reads a state, so each applies to any
`tree`, `score` and `eligible`, for instance to two walks over different trees with the same scores
and tests on shared blocks.

- the step: `ghost_children_eq` (the children `ghost_children` answers, when the test answers),
  `ghost_step_none_of_no_child` (no child in `tree`: no step), `ghost_step_some` (a step is to an
  eligible child in `tree`);
- `argmax?`: `argmax?_eq_some_of_outranks` (the member that outranks every other is picked: a
  higher score, or the same score and every other root before its root in `RootOrder.before`) and
  its converse `outranks_of_argmax?_eq_some`;
- the walk, from its result: `ghost_step_of_visited` (every block the walk passes through, other
  than the last, steps to the next), `visited_mem_tree` (every block it passes through, other than
  the first, is in `tree`), `ghost_walk_cases` and `ghost_step_none_of_ghost_eq` (the block
  `ghost` ends at has no step);
- the walk, from its steps: `ghost_walk_reaches` and `ghost_reaches` (forced steps along a path
  in `tree`, and no step at its end, make `ghost` end there).

A port, renaming only, of
`experiments/correctness/Correctness/Proofs/SpecDraft/GoldfishWalkMerge.lean`, with the tie of
`outranks` read through `RootOrder.before` in place of the order on roots.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks

variable {V : Type} [DecidableEq V]

/-! ## One step -/

/-- The children `ghost_children` answers from `H` are the blocks of `tree` whose parent is `H`
and on which the test answers `true`, when the test answers `b D` on every child `D` of `H` in
`tree`.

Why: the filter's test answers `false` off the children of `H`, and the test's answer on them.

The variables:
- `tree`: the tree; `eligible`: the eligibility test; `H`: the parent;
- `b`: the test's answers. -/
theorem ghost_children_eq {tree : Finset (Block V)} {eligible : Block V → DRE Bool}
    {H : Block V} (b : Block V → Bool)
    -- the test answers `b D` on every child `D` of `H` in `tree`
    (hok : ∀ D ∈ tree, D.parent? = some H → eligible D = .ok (b D)) :
    ghost_children tree eligible H =
      .ok (tree.filter (fun D => D.parent? = some H ∧ b D = true)) := by
  unfold ghost_children
  refine filterM_eq_ok_filter _ _ tree (fun D hD => ?_)
  by_cases hp : D.parent? = some H
  · simp only [hp, if_true, hok D hD hp, true_and]
    cases b D <;> rfl
  · simp only [hp, if_false, false_and, decide_false]
    rfl

variable [RootOrder]

/-- When no block of `tree` is a child of `H`, the step from `H` is `none`, whatever the score
and the test.

Why: the children are then empty, and `argmax?` on the empty set answers `none`.

The variables:
- `tree`: the tree; `score`: the score; `eligible`: the eligibility test; `H`: the block. -/
theorem ghost_step_none_of_no_child {tree : Finset (Block V)} {score : Block V → DRE Nat}
    {eligible : Block V → DRE Bool} {H : Block V}
    -- no block of `tree` is a child of `H`
    (h : ∀ D ∈ tree, D.parent? ≠ some H) :
    ghost_step tree score eligible H = .ok none := by
  have hch : ghost_children tree eligible H = .ok ∅ := by
    unfold ghost_children
    rw [filterM_eq_ok_filter _ (fun _ => False) tree (fun D hD => by
      simp only [h D hD, if_false, decide_false]
      rfl)]
    simp
  unfold ghost_step argmax?
  rw [hch]
  rfl

/-- A step from `H` that answers a block `C` answers a block of `tree` whose parent is `H` and on
which the test answers `true`.

Why: `argmax?` picks a member of the children, and `ghost_children` keeps exactly those.

The variables:
- `tree`: the tree; `score`: the score; `eligible`: the eligibility test;
- `H`: the block stepped from; `C`: the block stepped to. -/
theorem ghost_step_some {tree : Finset (Block V)} {score : Block V → DRE Nat}
    {eligible : Block V → DRE Bool} {H C : Block V}
    -- the step from `H` answers `C`
    (h : ghost_step tree score eligible H = .ok (some C)) :
    C ∈ tree ∧ C.parent? = some H ∧ eligible C = .ok true := by
  simp only [ghost_step, argmax?, bind, Except.bind] at h
  split at h
  · cases h
  rename_i ch hch
  split at h
  · cases h
  rename_i best hbest
  simp only [pure, Except.pure, Except.ok.injEq] at h
  have hcb := (mem_of_pickUnique?_eq_some h).1
  have hcch := ((mem_of_filterM_eq_ok_iff _ _ _ hbest C).1 hcb).1
  unfold ghost_children at hch
  obtain ⟨hct, hcp⟩ := (mem_of_filterM_eq_ok_iff _ _ _ hch C).1 hcch
  split at hcp
  · rename_i hpar
    exact ⟨hct, hpar, hcp⟩
  · simp [pure, Except.pure] at hcp

/-! ## The pick of `argmax?` -/

omit [DecidableEq V] in
/-- `outranks score D' D` answers whether `D'` beats `D`, when the score answers on both: a
higher score, or the same score and `D`'s root before `D'`'s in `RootOrder.before`.

Why: `outranks` compares the two answers, then the roots.

The variables:
- `score`: the score; `n`: its answers; `D`, `D'`: the two blocks. -/
theorem outranks_eq {score : Block V → DRE Nat} (n : Block V → ℕ) {D D' : Block V}
    -- the score answers `n D` on `D`
    (hD : score D = .ok (n D))
    -- the score answers `n D'` on `D'`
    (hD' : score D' = .ok (n D')) :
    outranks score D' D =
      .ok (decide (n D < n D' ∨ (n D = n D' ∧ RootOrder.before D.root D'.root = true))) := by
  simp only [outranks, hD, hD', bind, Except.bind, pure, Except.pure, Bool.decide_or,
    Bool.decide_and, Bool.decide_eq_true]

omit [DecidableEq V] in
/-- No two roots come each before the other.

The variables:
- `r`, `r'`: the two roots. -/
theorem before_asymm {r r' : BlockId} (h : RootOrder.before r r' = true)
    (h' : RootOrder.before r' r = true) : False := by
  have := RootOrder.trans r r' r h h'
  rw [RootOrder.irrefl] at this
  cases this

/-- `argmax? score children` answers the member `C` of `children` when every score on `children`
answers and `C` outranks every other member: a higher score, or the same score and the other's
root before `C`'s.

Why: `C` is then the one member no other outranks, so the one `pickUnique?` finds.

The variables:
- `score`: the score; `children`: the set; `C`: the member that wins; `n`: the scores' answers. -/
theorem argmax?_eq_some_of_outranks {score : Block V → DRE Nat} {children : Finset (Block V)}
    {C : Block V} (hC : C ∈ children) (n : Block V → ℕ)
    -- the score answers `n D` on every member `D` of `children`
    (hok : ∀ D ∈ children, score D = .ok (n D))
    -- every other member of `children` scores less than `C`, or the same with its root before
    -- `C`'s
    (hdom : ∀ D ∈ children, D ≠ C →
      n D < n C ∨ (n D = n C ∧ RootOrder.before D.root C.root = true)) :
    argmax? score children = .ok (some C) := by
  -- `is_best_in score children D` answers whether `D` is `C`
  have hbest : ∀ D ∈ children, is_best_in score children D = .ok (decide (D = C)) := by
    intro D hD
    unfold is_best_in
    rw [filterM_eq_ok_filter _
      (fun D' => n D < n D' ∨ (n D = n D' ∧ RootOrder.before D.root D'.root = true)) children
      (fun D' hD' => outranks_eq n (hok D hD) (hok D' hD'))]
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq]
    by_cases hDC : D = C
    · subst hDC
      have hempty : children.filter
          (fun D' => n D < n D' ∨ (n D = n D' ∧ RootOrder.before D.root D'.root = true)) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun D' hD' hlt => ?_
        by_cases hD'D : D' = D
        · subst hD'D
          rcases hlt with h | ⟨-, h⟩
          · exact lt_irrefl _ h
          · rw [RootOrder.irrefl] at h
            cases h
        · rcases hdom D' hD' hD'D with h | ⟨h, h'⟩ <;> rcases hlt with h'' | ⟨h'', h'''⟩
          · omega
          · omega
          · omega
          · exact before_asymm h' h'''
      simp [hempty]
    · have hne : (children.filter
          (fun D' => n D < n D' ∨ (n D = n D' ∧ RootOrder.before D.root D'.root = true))).Nonempty :=
        ⟨C, Finset.mem_filter.2 ⟨hC, hdom D hD hDC⟩⟩
      simp [hDC, hne.ne_empty]
  unfold argmax?
  rw [filterM_eq_ok_filter _ (fun D => D = C) children hbest]
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq]
  exact pickUnique?_eq_some (Finset.mem_filter.2 ⟨hC, rfl⟩) rfl
    (fun D hD _ => (Finset.mem_filter.1 hD).2)

/-- The member `argmax? score children` answers is in `children` and outranks every other
member, when every score on `children` answers: a higher score, or the same score and the other's
root before its root.

Why: the pick passes `is_best_in`, so no member outranks it; a member with its score and its root
would pass too, and `pickUnique?` answers only when one member passes; of two different roots one
comes before the other (`RootOrder.total`).

The variables:
- `score`: the score; `children`: the set; `n`: the scores' answers; `C`: the member picked. -/
theorem outranks_of_argmax?_eq_some {score : Block V → DRE Nat} {children : Finset (Block V)}
    {C : Block V} (n : Block V → ℕ)
    -- the score answers `n D` on every member `D` of `children`
    (hok : ∀ D ∈ children, score D = .ok (n D))
    -- `argmax?` picks `C`
    (h : argmax? score children = .ok (some C)) :
    C ∈ children ∧ ∀ D ∈ children, D ≠ C →
      n D < n C ∨ (n D = n C ∧ RootOrder.before D.root C.root = true) := by
  -- `is_best_in score children D` answers whether no member outranks `D`
  have hbest : ∀ D ∈ children, is_best_in score children D = .ok (decide
      (children.filter (fun D' => n D < n D' ∨
        (n D = n D' ∧ RootOrder.before D.root D'.root = true)) = ∅)) := by
    intro D hD
    unfold is_best_in
    rw [filterM_eq_ok_filter _
      (fun D' => n D < n D' ∨ (n D = n D' ∧ RootOrder.before D.root D'.root = true)) children
      (fun D' hD' => outranks_eq n (hok D hD) (hok D' hD'))]
    rfl
  unfold argmax? at h
  rw [filterM_eq_ok_filter _ _ children hbest] at h
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
  -- the members no other outranks
  set best := children.filter (fun D => children.filter (fun D' => n D < n D' ∨
    (n D = n D' ∧ RootOrder.before D.root D'.root = true)) = ∅) with hbestdef
  have hCbest := (mem_of_pickUnique?_eq_some h).1
  obtain ⟨hC, hCnone⟩ := Finset.mem_filter.1 hCbest
  refine ⟨hC, fun D hD hDC => ?_⟩
  -- no member outranks `C`
  have hnot : ¬ (n C < n D ∨ (n C = n D ∧ RootOrder.before C.root D.root = true)) := fun hlt =>
    (Finset.filter_eq_empty_iff.1 hCnone) hD hlt
  rcases lt_trichotomy (n D) (n C) with hlt | heq | hgt
  · exact Or.inl hlt
  · by_cases hr : D.root = C.root
    · -- `D` has `C`'s score and root, so it is a best member too, against the unique pick
      exfalso
      have hDbest : D ∈ best := by
        refine Finset.mem_filter.2 ⟨hD, Finset.filter_eq_empty_iff.2 fun D' hD' hlt => ?_⟩
        rw [heq, hr] at hlt
        exact (Finset.filter_eq_empty_iff.1 hCnone) hD' hlt
      unfold pickUnique? at h
      split at h
      · rename_i hu
        obtain ⟨a, -, ha⟩ := hu
        exact hDC ((ha D ⟨hDbest, rfl⟩).trans (ha C ⟨hCbest, rfl⟩).symm)
      · cases h
    · rcases RootOrder.total D.root C.root hr with hb | hb
      · exact Or.inr ⟨heq, hb⟩
      · exact absurd (Or.inr ⟨heq.symm, hb⟩) hnot
  · exact absurd (Or.inl hgt) hnot

/-! ## The walk, from its result to its steps -/

omit [RootOrder] in
/-- A block on the way from `A` to `H` other than `A` is a descendant of, or equal to, the child
of `A` on the way to `H`.

Why: both are ancestors of `H`, so one is an ancestor of the other, and the block is at least
as deep as the child.

The variables:
- `A`: the start; `H`: the end; `Y`: the block on the way; `C`: the child of `A`. -/
theorem child_ancestorEq_of_between {A H Y C : Block V} (hAY : A.AncestorEq Y) (hYA : Y ≠ A)
    (hYH : Y.AncestorEq H) (hC : C.parent? = some A) (hCH : C.AncestorEq H) :
    C.AncestorEq Y := by
  rcases ancestorEq_compatible hCH hYH with h | h
  · exact h
  · have hdY : A.depth < Y.depth := by
      rcases Nat.lt_or_ge A.depth Y.depth with h' | h'
      · exact h'
      · exact absurd (eq_of_ancestorEq_of_depth hAY h').symm hYA
    have hYC := depth_le_of_ancestorEq h
    rw [depth_of_parent? hC] at hYC
    rw [eq_of_ancestorEq_of_depth h (by rw [depth_of_parent? hC]; omega)]
    exact ancestorEq_refl C

/-- From a walk of `n` steps from `A` that answers `H`: either the step from `A` is `none` and
`H` is `A`, or the step is a block `C` and the walk of the remaining steps from `C` answers `H`.

Why: this is one unfolding of `ghost_walk`.

The variables:
- `tree`: the tree; `score`: the score; `eligible`: the eligibility test;
- `n`: the remaining steps; `A`: the start; `H`: the end. -/
theorem ghost_walk_succ_cases {tree : Finset (Block V)} {score : Block V → DRE Nat}
    {eligible : Block V → DRE Bool} {n : ℕ} {A H : Block V}
    -- the walk of `n + 1` steps from `A` answers `H`
    (h : ghost_walk tree score eligible (n + 1) A = .ok H) :
    (ghost_step tree score eligible A = .ok none ∧ H = A) ∨
      ∃ C : Block V, ghost_step tree score eligible A = .ok (some C) ∧
        ghost_walk tree score eligible n C = .ok H := by
  simp only [ghost_walk, bind, Except.bind] at h
  split at h
  · cases h
  rename_i C? hC
  split at h
  · rename_i hne
    obtain ⟨c, rfl⟩ := Option.ne_none_iff_exists'.1 hne
    simp only [Option.value, Option.get_some] at h
    exact Or.inr ⟨c, hC, h⟩
  · rename_i hne
    simp only [ne_eq, Decidable.not_not] at hne
    subst hne
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl ⟨hC, h.symm⟩

/-- Every block the walk passes through, other than the last, steps to the next: for a walk from
`A` that answers `H`, every `Y` on the way from `A` to `H` other than `H` has a step to a child
`C` of `Y` on the way to `H`.

Why: the walk's first step is to a child `C` of `A` on the way to `H`; every later block on the
way is on the way from `C`, so the walk from `C` covers it.

The variables:
- `tree`: the tree; `score`: the score; `eligible`: the eligibility test;
- `n`: the number of steps; `A`: the start; `H`: the end. -/
theorem ghost_step_of_visited {tree : Finset (Block V)} {score : Block V → DRE Nat}
    {eligible : Block V → DRE Bool} {n : ℕ} {A H : Block V}
    -- the walk of `n` steps from `A` answers `H`
    (h : ghost_walk tree score eligible n A = .ok H) :
    ∀ Y : Block V, A.AncestorEq Y → Y.AncestorEq H → Y ≠ H →
      ∃ C : Block V, ghost_step tree score eligible Y = .ok (some C) ∧
        C.parent? = some Y ∧ C.AncestorEq H := by
  induction n generalizing A with
  | zero =>
    intro Y hAY hYH hne
    simp only [ghost_walk, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact absurd (ancestorEq_antisymm hYH hAY) hne
  | succ n ih =>
    intro Y hAY hYH hne
    rcases ghost_walk_succ_cases h with ⟨-, rfl⟩ | ⟨C, hC, hw⟩
    · exact absurd (ancestorEq_antisymm hYH hAY) hne
    · have hCA := (ghost_step_some hC).2.1
      have hCH : C.AncestorEq H := by
        rcases ghost_walk_spec tree score eligible n C H hw with hR | ⟨hR, -⟩
        · rw [hR]
          exact ancestorEq_refl C
        · exact hR
      by_cases hYA : Y = A
      · subst hYA
        exact ⟨C, hC, hCA, hCH⟩
      · exact ih hw Y (child_ancestorEq_of_between hAY hYA hYH hCA hCH) hYH hne

/-- Every block the walk passes through, other than the first, is in `tree`: for a walk from `A`
that answers `H`, every `Y` on the way from `A` to `H` other than `A` is in `tree`.

Why: each step is to a block of `tree`, and the blocks on the way are the walk's steps.

The variables:
- `tree`: the tree; `score`: the score; `eligible`: the eligibility test;
- `n`: the number of steps; `A`: the start; `H`: the end. -/
theorem visited_mem_tree {tree : Finset (Block V)} {score : Block V → DRE Nat}
    {eligible : Block V → DRE Bool} {n : ℕ} {A H : Block V}
    -- the walk of `n` steps from `A` answers `H`
    (h : ghost_walk tree score eligible n A = .ok H) :
    ∀ Y : Block V, A.AncestorEq Y → Y ≠ A → Y.AncestorEq H → Y ∈ tree := by
  induction n generalizing A with
  | zero =>
    intro Y hAY hYA hYH
    simp only [ghost_walk, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact absurd (ancestorEq_antisymm hAY hYH).symm hYA
  | succ n ih =>
    intro Y hAY hYA hYH
    rcases ghost_walk_succ_cases h with ⟨-, rfl⟩ | ⟨C, hC, hw⟩
    · exact absurd (ancestorEq_antisymm hAY hYH).symm hYA
    · obtain ⟨hCt, hCA, -⟩ := ghost_step_some hC
      have hCH : C.AncestorEq H := by
        rcases ghost_walk_spec tree score eligible n C H hw with hR | ⟨hR, -⟩
        · rw [hR]
          exact ancestorEq_refl C
        · exact hR
      have hCY := child_ancestorEq_of_between hAY hYA hYH hCA hCH
      by_cases hYC : Y = C
      · exact hYC ▸ hCt
      · exact ih hw Y hCY hYC hYH

/-- A walk of `n` steps from `A` that answers `H` either stops at `H`, the step from `H` being
`none`, or takes all `n` steps, `H` being `n` deeper than `A`.

Why: every step is to a child, one deeper; the walk returns early only on a `none` step.

The variables:
- `tree`: the tree; `score`: the score; `eligible`: the eligibility test;
- `n`: the number of steps; `A`: the start; `H`: the end. -/
theorem ghost_walk_cases {tree : Finset (Block V)} {score : Block V → DRE Nat}
    {eligible : Block V → DRE Bool} {n : ℕ} {A H : Block V}
    -- the walk of `n` steps from `A` answers `H`
    (h : ghost_walk tree score eligible n A = .ok H) :
    ghost_step tree score eligible H = .ok none ∨ H.depth = A.depth + n := by
  induction n generalizing A with
  | zero =>
    simp only [ghost_walk, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact Or.inr rfl
  | succ n ih =>
    rcases ghost_walk_succ_cases h with ⟨hs, rfl⟩ | ⟨C, hC, hw⟩
    · exact Or.inl hs
    · rcases ih hw with hs | hd
      · exact Or.inl hs
      · rw [depth_of_parent? (ghost_step_some hC).2.1] at hd
        exact Or.inr (by omega)

/-- The step from the block `ghost` ends at is `none`.

Why: when the walk stopped early, its last step was `none`. Otherwise it took `|tree|` steps,
each to a block of `tree`; a child of the end in `tree` would then make a path of `|tree| + 1`
blocks of `tree`, one more than `tree` holds (`path_card`).

The variables:
- `A`: the start; `tree`: the tree; `score`: the score; `eligible`: the eligibility test;
- `H`: the end. -/
theorem ghost_step_none_of_ghost_eq {A : Block V} {tree : Finset (Block V)}
    {score : Block V → DRE Nat} {eligible : Block V → DRE Bool} {H : Block V}
    -- the walk `ghost` from `A` answers `H`
    (h : ghost A tree score eligible = .ok H) :
    ghost_step tree score eligible H = .ok none := by
  unfold ghost at h
  rcases ghost_walk_cases h with hs | hd
  · exact hs
  · refine ghost_step_none_of_no_child fun D hD hDH => ?_
    have hAH : A.AncestorEq H := by
      rcases ghost_walk_spec tree score eligible _ A H h with hR | ⟨hR, -⟩
      · rw [hR]
        exact ancestorEq_refl A
      · exact hR
    have hHD := ancestorEq_of_parent? hDH
    -- every block after `A` on the way to `D` is in `tree`
    have hpath : ∀ P : Block V, A.AncestorEq P → P ≠ A → P.AncestorEq D → P ∈ tree := by
      intro P hAP hPA hPD
      by_cases hPeq : P = D
      · exact hPeq ▸ hD
      · have hPH : P.AncestorEq H := by
          rcases ancestorEq_compatible hPD hHD with h' | h'
          · exact h'
          · -- `H` is an ancestor of `P`: `P` is `H`, or as deep as `D` and so `D`
            have hPD' := depth_le_of_ancestorEq hPD
            rw [depth_of_parent? hDH] at hPD'
            rcases Nat.lt_or_ge H.depth P.depth with hlt | hge
            · exact absurd (eq_of_ancestorEq_of_depth hPD (by
                rw [depth_of_parent? hDH]; omega)) hPeq
            · rw [← eq_of_ancestorEq_of_depth h' hge]
              exact ancestorEq_refl H
        exact visited_mem_tree h P hAP hPA hPH
    have := path_card (ancestorEq_trans hAH hHD) hpath
    rw [depth_of_parent? hDH] at this
    omega

/-! ## The walk, from its steps to its result -/

/-- The walk of `n` steps from a block `H₀` on the way from `A` to `target` answers `target`,
when `n` is at least the depth gap from `H₀` to `target`, from every block on the way from `A` to
`target` other than `target` the step is a block on the way to `target`, and the step from
`target` is `none`.

Why: induction on `n`; each forced step moves one deeper on the way to `target`, and at
`target` the walk stops.

The variables:
- `tree`: the tree; `score`: the score; `eligible`: the eligibility test;
- `A`: the start of the path; `target`: its end; `n`: the number of steps; `H₀`: the block the
  walk starts from. -/
theorem ghost_walk_reaches {tree : Finset (Block V)} {score : Block V → DRE Nat}
    {eligible : Block V → DRE Bool} {A target : Block V}
    -- the step from `target` is `none`
    (hstop : ghost_step tree score eligible target = .ok none)
    -- from every block on the way from `A` to `target` other than `target`, the step is a block
    -- on the way to `target`
    (hstep : ∀ Y : Block V, A.AncestorEq Y → Y.AncestorEq target → Y ≠ target →
      ∃ C : Block V, ghost_step tree score eligible Y = .ok (some C) ∧ C.AncestorEq target) :
    ∀ (n : ℕ) (H₀ : Block V), A.AncestorEq H₀ → H₀.AncestorEq target →
      target.depth ≤ H₀.depth + n → ghost_walk tree score eligible n H₀ = .ok target := by
  intro n
  induction n with
  | zero =>
    intro H₀ _ hH₀t hd
    simp only [ghost_walk, pure, Except.pure, Except.ok.injEq]
    exact eq_of_ancestorEq_of_depth hH₀t (by omega)
  | succ n ih =>
    intro H₀ hAH₀ hH₀t hd
    by_cases hH₀ : H₀ = target
    · subst hH₀
      simp only [ghost_walk, bind, Except.bind, hstop, ne_eq, not_true_eq_false, ↓reduceDIte, pure,
        Except.pure]
    · obtain ⟨C, hCs, hCt⟩ := hstep H₀ hAH₀ hH₀t hH₀
      have hCH₀ := (ghost_step_some hCs).2.1
      simp only [ghost_walk, bind, Except.bind, hCs, ne_eq, reduceCtorEq, not_false_eq_true,
        Option.value, Option.get_some]
      exact ih C (ancestorEq_trans hAH₀ (ancestorEq_of_parent? hCH₀)) hCt
        (by rw [depth_of_parent? hCH₀]; omega)

/-- The descent lemma: the walk `ghost` from `A` answers `target`, when `A` is an ancestor of
`target` or `target`, every block after `A` on the way to `target` is in `tree`, from every block
on the way other than `target` the step is a block on the way to `target`, and the step from
`target` is `none`.

Why: the path is at most `|tree|` blocks deep (`path_card`), so `|tree|` steps reach `target`
(`ghost_walk_reaches`).

The variables:
- `A`: the start; `target`: the end; `tree`: the tree; `score`: the score;
- `eligible`: the eligibility test. -/
theorem ghost_reaches {A target : Block V} {tree : Finset (Block V)}
    {score : Block V → DRE Nat} {eligible : Block V → DRE Bool}
    -- `A` is an ancestor of `target`, or `target` itself
    (hpre : A.AncestorEq target)
    -- every block after `A` on the way to `target`, `target` included, is in `tree`
    (hpath : ∀ C : Block V, A.AncestorEq C → C ≠ A → C.AncestorEq target → C ∈ tree)
    -- the step from `target` is `none`
    (hstop : ghost_step tree score eligible target = .ok none)
    -- from every block on the way from `A` to `target` other than `target`, the step is a block
    -- on the way to `target`
    (hstep : ∀ Y : Block V, A.AncestorEq Y → Y.AncestorEq target → Y ≠ target →
      ∃ C : Block V, ghost_step tree score eligible Y = .ok (some C) ∧ C.AncestorEq target) :
    ghost A tree score eligible = .ok target :=
  ghost_walk_reaches hstop hstep tree.card A (ancestorEq_refl A) hpre (path_card hpre hpath)

end GoldilocksCorrectness.Proofs.Routines
