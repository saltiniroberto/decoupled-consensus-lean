module
public import GoldilocksCorrectness.Proofs.Routines.Blocks
public import GoldilocksCorrectness.Proofs.Routines.Kit
import all Goldilocks.AC.ForkChoice

@[expose] public section

/-!
# The Goldfish walk along a path

The walk `ghost A tree score eligible`, with the score and the eligibility test taken as
parameters: no lemma of this file reads a state.

- `ghost_walk_spec`, `ghost_spec`: the walk ends at its start, or at an eligible descendant of it;
- `argmax?_eq_some_of_dominates`: `argmax?` picks the member that strictly outscores every other;
- `ghost_walk_passes`, `ghost_passes`: when from every block on the way from `A` to `B` other
  than `B` the step is a child on the way to `B`, the walk from `A` ends at `B` or a descendant
  of `B`;
- `ghost_step_towards`: the step from `H₀` is the child `C` when `C` is eligible and strictly
  outscores every other child of `H₀` in `tree`;
- `conflicts_of_sibling_towards`: a child of `H₀` other than the one on the way to `R` conflicts
  with `R`.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks

variable {V : Type} [DecidableEq V]

/-! ## Siblings -/

/-- A child of `H₀` other than the child `C` on the way to `R` conflicts with `R`, when `H₀` is a
strict ancestor of `R`.

The variables:
- `H₀`: the parent; `C`: the child on the way to `R`; `D`: the other child; `R`: the block. -/
theorem conflicts_of_sibling_towards {H₀ C D R : Block V} (hC : C.parent? = some H₀)
    (hD : D.parent? = some H₀) (hCR : C.AncestorEq R) (hH₀R : H₀.AncestorEq R) (hne : H₀ ≠ R)
    (hDC : D ≠ C) : D.conflicts R = true := by
  rw [conflicts_iff, compatible_iff]
  rintro (hDR | hRD)
  · exact hDC (child_towards_unique hC hD hCR hDR)
  · have hdH : H₀.depth < R.depth := by
      rcases Nat.lt_or_ge H₀.depth R.depth with h' | h'
      · exact h'
      · exact absurd (eq_of_ancestorEq_of_depth hH₀R h') hne
    have hRD' : R = D := eq_of_ancestorEq_of_depth hRD (by
      have := depth_le_of_ancestorEq hRD
      rw [depth_of_parent? hD] at this ⊢
      omega)
    exact hDC (child_towards_unique hC hD hCR (hRD' ▸ ancestorEq_refl R))

variable [RootOrder]

/-! ## The walk's end -/

/-- The block `ghost_walk` reaches from `H₀` is `H₀`, or a descendant of `H₀` that passes the
eligibility test: every step moves to an eligible child.

The variables:
- `tree`: the tree walked; `score`: the score; `eligible`: the eligibility test;
- `n`: the number of steps; `H₀`: the block the walk starts from; `R`: the block it reaches. -/
theorem ghost_walk_spec (tree : Finset (Block V)) (score : Block V → DRE Nat)
    (eligible : Block V → DRE Bool) :
    ∀ (n : ℕ) (H₀ R : Block V), ghost_walk tree score eligible n H₀ = .ok R →
      R = H₀ ∨ (H₀.AncestorEq R ∧ eligible R = .ok true) := by
  intro n
  induction n with
  | zero =>
    intro H₀ R h
    simp only [ghost_walk, pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl h.symm
  | succ n ih =>
    intro H₀ R h
    simp only [ghost_walk, bind, Except.bind] at h
    split at h
    · cases h
    rename_i C? hC
    split at h
    · rename_i hne
      obtain ⟨c, rfl⟩ := Option.ne_none_iff_exists'.1 hne
      simp only [Option.value, Option.get_some] at h
      -- `c` is an eligible child of `H₀`
      simp only [ghost_step, argmax?, bind, Except.bind] at hC
      split at hC
      · cases hC
      rename_i ch hch
      split at hC
      · cases hC
      rename_i best hbest
      simp only [pure, Except.pure, Except.ok.injEq] at hC
      have hcb := (mem_of_pickUnique?_eq_some hC).1
      have hcch := ((mem_of_filterM_eq_ok_iff _ _ _ hbest c).1 hcb).1
      unfold ghost_children at hch
      have hcp := ((mem_of_filterM_eq_ok_iff _ _ _ hch c).1 hcch).2
      split at hcp
      · rename_i hpar
        have hHc : H₀.AncestorEq c := ancestorEq_of_parent? hpar
        rcases ih c R h with hR | ⟨hcR, hR⟩
        · subst hR
          exact Or.inr ⟨hHc, hcp⟩
        · exact Or.inr ⟨ancestorEq_trans hHc hcR, hR⟩
      · simp [pure, Except.pure] at hcp
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm

/-- The block `ghost` reaches from `A` is `A`, or a descendant of `A` that passes the
eligibility test.

The variables:
- `A`: the block the walk starts from; `tree`: the tree walked; `score`: the score;
- `eligible`: the eligibility test; `H`: the block reached. -/
theorem ghost_spec {A : Block V} {tree : Finset (Block V)} {score : Block V → DRE Nat}
    {eligible : Block V → DRE Bool} {H : Block V} (h : ghost A tree score eligible = .ok H) :
    H = A ∨ (A.AncestorEq H ∧ eligible H = .ok true) :=
  ghost_walk_spec tree score eligible _ A H h

/-! ## The walk along a path -/

/-- `argmax? score children` answers the member `C` of `children` when every score on `children`
answers and `C`'s strictly exceeds every other member's.

The variables:
- `score`: the score; `children`: the set; `C`: the member that wins; `n`: the scores' answers. -/
theorem argmax?_eq_some_of_dominates {score : Block V → DRE Nat} {children : Finset (Block V)}
    {C : Block V} (hC : C ∈ children) (n : Block V → ℕ)
    -- the score answers `n D` on every member `D` of `children`
    (hok : ∀ D ∈ children, score D = .ok (n D))
    -- every other member of `children` scores less than `C`
    (hdom : ∀ D ∈ children, D ≠ C → n D < n C) :
    argmax? score children = .ok (some C) := by
  -- `outranks score D' D` answers whether `D'` beats `D`
  have hout : ∀ D ∈ children, ∀ D' ∈ children, outranks score D' D =
      .ok (decide (n D < n D' ∨ (n D = n D' ∧ RootOrder.before D.root D'.root = true))) := by
    intro D hD D' hD'
    simp only [outranks, hok D hD, hok D' hD', bind, Except.bind, pure, Except.pure,
      Bool.decide_or, Bool.decide_and, Bool.decide_eq_true]
  -- `is_best_in score children D` answers whether `D` is `C`
  have hbest : ∀ D ∈ children, is_best_in score children D = .ok (decide (D = C)) := by
    intro D hD
    unfold is_best_in
    rw [filterM_eq_ok_filter _
      (fun D' => n D < n D' ∨ (n D = n D' ∧ RootOrder.before D.root D'.root = true)) children
      (fun D' hD' => hout D hD D' hD')]
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
        · have := hdom D' hD' hD'D
          omega
      simp [hempty]
    · have hne : (children.filter
          (fun D' => n D < n D' ∨ (n D = n D' ∧ RootOrder.before D.root D'.root = true))).Nonempty :=
        ⟨C, Finset.mem_filter.2 ⟨hC, Or.inl (hdom D hD hDC)⟩⟩
      simp [hDC, hne.ne_empty]
  unfold argmax?
  rw [filterM_eq_ok_filter _ (fun D => D = C) children hbest]
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq]
  exact pickUnique?_eq_some (Finset.mem_filter.2 ⟨hC, rfl⟩) rfl
    (fun D hD _ => (Finset.mem_filter.1 hD).2)

/-- The walk from `H₀` with `n` steps, `n` at least the depth gap from `H₀` to `B`, ends at `B`
or a descendant of `B`, when `H₀` is on the way from `A` to `B` and from every block on that way
other than `B` the step is a child on the way to `B`.

The variables:
- `tree`: the tree walked; `score`: the score; `eligible`: the eligibility test;
- `A`: the block the path starts from; `B`: the block it ends at;
- `n`: the number of steps; `H₀`: the block the walk starts from; `R`: the block it reaches. -/
theorem ghost_walk_passes {tree : Finset (Block V)} {score : Block V → DRE Nat}
    {eligible : Block V → DRE Bool} {A B : Block V}
    -- from every block on the way from `A` to `B` other than `B`, the step is a child on the way
    -- to `B`
    (hstep : ∀ H₀ : Block V, A.AncestorEq H₀ → H₀.AncestorEq B → H₀ ≠ B →
      ∀ r : Option (Block V), ghost_step tree score eligible H₀ = .ok r →
        ∃ C : Block V, r = some C ∧ C.parent? = some H₀ ∧ C.AncestorEq B) :
    ∀ (n : ℕ) (H₀ R : Block V), A.AncestorEq H₀ → H₀.AncestorEq B →
      B.depth ≤ H₀.depth + n → ghost_walk tree score eligible n H₀ = .ok R → B.AncestorEq R := by
  intro n
  induction n with
  | zero =>
    intro H₀ R _ hH₀B hdepth h
    simp only [ghost_walk, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [eq_of_ancestorEq_of_depth hH₀B (by omega)]
    exact ancestorEq_refl _
  | succ n ih =>
    intro H₀ R hAH₀ hH₀B hdepth h
    by_cases hH₀ : H₀ = B
    · subst hH₀
      rcases ghost_walk_spec tree score eligible (n + 1) H₀ R h with hR | ⟨hR, -⟩
      · rw [hR]
        exact ancestorEq_refl _
      · exact hR
    · simp only [ghost_walk, bind, Except.bind] at h
      split at h
      · cases h
      rename_i r hr
      obtain ⟨C, rfl, hC, hCB⟩ := hstep H₀ hAH₀ hH₀B hH₀ r hr
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, Option.value, Option.get_some] at h
      exact ih C R (ancestorEq_trans hAH₀ (ancestorEq_of_parent? hC)) hCB
        (by rw [depth_of_parent? hC]; omega) h

/-- The walk `ghost` from `A` ends at `B` or a descendant of `B`, when every block after `A` on
the way to `B` is in `tree` and from every block on that way other than `B` the step is a child on
the way to `B`.

The variables:
- `A`: the block the walk starts from; `B`: the block the path ends at; `tree`: the tree walked;
- `score`: the score; `eligible`: the eligibility test; `H`: the block reached. -/
theorem ghost_passes {A B : Block V} {tree : Finset (Block V)} {score : Block V → DRE Nat}
    {eligible : Block V → DRE Bool}
    -- `A` is an ancestor of `B`, or `B` itself
    (hAB : A.AncestorEq B)
    -- every block after `A` on the way to `B`, `B` included, is in `tree`
    (hpath : ∀ P : Block V, A.AncestorEq P → P ≠ A → P.AncestorEq B → P ∈ tree)
    -- from every block on the way from `A` to `B` other than `B`, the step is a child on the way
    -- to `B`
    (hstep : ∀ H₀ : Block V, A.AncestorEq H₀ → H₀.AncestorEq B → H₀ ≠ B →
      ∀ r : Option (Block V), ghost_step tree score eligible H₀ = .ok r →
        ∃ C : Block V, r = some C ∧ C.parent? = some H₀ ∧ C.AncestorEq B)
    {H : Block V}
    -- the walk from `A` reaches `H`
    (h : ghost A tree score eligible = .ok H) :
    B.AncestorEq H :=
  ghost_walk_passes hstep tree.card A H (ancestorEq_refl A) hAB (path_card hAB hpath) h

/-! ## The step towards a block -/

/-- The walk's step from `H₀` is the child `C` of `H₀`, when `C` is in `tree` and eligible, the
score answers `n D` and the test answers on every block, and every other child of `H₀` in `tree`
scores less than `C`.

The variables:
- `tree`: the tree walked; `score`: the score; `eligible`: the eligibility test;
- `H₀`: the block the step starts from; `C`: its child; `n`: the scores' answers. -/
theorem ghost_step_towards {tree : Finset (Block V)} {score : Block V → DRE Nat}
    {eligible : Block V → DRE Bool} {H₀ C : Block V} (n : Block V → ℕ)
    (hC : C.parent? = some H₀) (hCtree : C ∈ tree) (hCel : eligible C = .ok true)
    -- the score answers `n D` on every block `D`
    (hScore : ∀ D : Block V, score D = .ok (n D))
    -- the test answers on every block
    (hEl : ∀ D : Block V, ∃ b : Bool, eligible D = .ok b)
    -- every other child of `H₀` in `tree` scores less than `C`
    (hdom : ∀ D ∈ tree, D.parent? = some H₀ → D ≠ C → n D < n C) :
    ghost_step tree score eligible H₀ = .ok (some C) := by
  -- the children test answers on every block
  have htot : ∀ D ∈ tree, ∃ b : Bool,
      (fun D : Block V => (do if D.parent? = some H₀ then eligible D else return false :
        DRE Bool)) D = .ok b := by
    intro D _
    by_cases hD : D.parent? = some H₀
    · obtain ⟨b, hb⟩ := hEl D
      exact ⟨b, by simp only [hD, if_true, hb]⟩
    · exact ⟨false, by simp only [hD, if_false]; rfl⟩
  obtain ⟨R, hR⟩ := filterM_eq_ok_of_total _ tree htot
  have hch : ghost_children tree eligible H₀ = .ok R := hR
  have hmem := mem_of_filterM_eq_ok_iff _ tree R hR
  have hCR : C ∈ R := (hmem C).2 ⟨hCtree, by simp only [hC, if_true, hCel]⟩
  -- every candidate other than `C` scores less than `C`
  have hdomR : ∀ D ∈ R, D ≠ C → n D < n C := by
    intro D hD hDC
    obtain ⟨hDtree, hp⟩ := (hmem D).1 hD
    have hDpar : D.parent? = some H₀ := by
      by_contra hDp
      simp only [hDp, if_false] at hp
      cases hp
    exact hdom D hDtree hDpar hDC
  have harg : argmax? score R = .ok (some C) :=
    argmax?_eq_some_of_dominates hCR n (fun D _ => hScore D) hdomR
  unfold ghost_step
  rw [hch]
  exact harg

end GoldilocksCorrectness.Proofs.Routines
