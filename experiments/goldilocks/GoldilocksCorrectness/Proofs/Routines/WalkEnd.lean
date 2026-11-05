module
public import GoldilocksCorrectness.Proofs.Routines.Walk
import all Goldilocks.AC.ForkChoice

@[expose] public section

/-!
# Where the Goldfish walk ends: its start, or a block of the tree

The walk `ghost A tree score eligible`, with the score and the eligibility test taken as
parameters: no lemma of this file reads a state.

- `ghost_walk_mem_tree_or_eq`, `ghost_mem_tree_or_eq`: the walk ends at its start, or at a block
  of the tree it walks, since every step moves to a child of the current block taken from the
  tree (`ghost_children` is a `filterM` of `tree`).
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks

variable {V : Type} [DecidableEq V] [RootOrder]

/-- The block `ghost_walk` reaches from `H₀` is `H₀`, or a block of `tree`: every step moves to a
child taken from `tree`.

The variables:
- `tree`: the tree walked; `score`: the score; `eligible`: the eligibility test;
- `n`: the number of steps; `H₀`: the block the walk starts from; `R`: the block it reaches. -/
theorem ghost_walk_mem_tree_or_eq (tree : Finset (Block V)) (score : Block V → DRE Nat)
    (eligible : Block V → DRE Bool) :
    ∀ (n : ℕ) (H₀ R : Block V), ghost_walk tree score eligible n H₀ = .ok R →
      R = H₀ ∨ R ∈ tree := by
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
      -- `c` is a child of `H₀` taken from `tree`
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
      have hct : c ∈ tree := ((mem_of_filterM_eq_ok_iff _ _ _ hch c).1 hcch).1
      rcases ih c R h with hR | hR
      · subst hR
        exact Or.inr hct
      · exact Or.inr hR
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm

/-- The block `ghost` reaches from `A` is `A`, or a block of `tree`.

The variables:
- `A`: the block the walk starts from; `tree`: the tree walked; `score`: the score;
- `eligible`: the eligibility test; `H`: the block reached. -/
theorem ghost_mem_tree_or_eq {A : Block V} {tree : Finset (Block V)} {score : Block V → DRE Nat}
    {eligible : Block V → DRE Bool} {H : Block V} (h : ghost A tree score eligible = .ok H) :
    H = A ∨ H ∈ tree :=
  ghost_walk_mem_tree_or_eq tree score eligible _ A H h

end GoldilocksCorrectness.Proofs.Routines
