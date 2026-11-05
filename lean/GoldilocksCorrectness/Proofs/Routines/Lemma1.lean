module
public import GoldilocksCorrectness.Proofs.Routines.Score
public import GoldilocksCorrectness.Proofs.Routines.Walk

@[expose] public section

/-!
# Lemma 1: the walk from a start towards `R` ends at `R` or a descendant of `R`

The proof of `lem1_walk_extends_majority_block`, stated in
`GoldilocksCorrectness/Statements/Routines/WalkStatements.lean`.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 1, the walk extends a majority block.** The walk `ghost` from `A` through `tree`,
scoring with `goldfish_score` and stepping onto blocks the test `eligible` accepts, ends at `R` or
a descendant of `R`, when `A` starts towards `R` in `tree`, each member of `Sup` has one vote and
it supports `R`'s chain, the voters are fewer than twice `Sup`, and the test accepts every block
after `A` up to `R` whose score `n` has `N < 2n`, with `N` less than twice `Sup`.

Why: from a block on the way to `R`, the child towards `R` is supported by all of `Sup`, so the
test accepts it; any other child conflicts with `R`, so its supporters, `Sup` and the equivocators
are disjoint sets of voters, and it scores less than `Sup`'s size.



The variables:
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes the score counts;
- `s`: the slot of the votes; `eligible`: the eligibility test; `N`: the test's threshold;
- `A`: the block the walk starts from; `R`: the majority block; `H`: the block the walk ends at;
- `tree`: the tree walked; `Sup`: the validators voting for `R`'s chain. -/
theorem lem1_walk_extends_majority_block (Φ : Frame V)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (eligible : Block V → DRE Bool)
    (N : ℕ) (A R H : Block V) (tree : Finset (Block V)) (Sup : Finset V)
    (hStart : StartsTowards A R tree)
    (hRoots : RootsNameBlocksIn Φ.tree)
    -- every support vote is among the votes
    (hSupport : support_votes ⊆ votes)
    -- each member of `Sup` has one vote in `votes`, a slot-`s` support vote for `R`'s chain
    (hSup : ∀ v ∈ Sup, VotesOnceFor Φ votes support_votes s R v)
    -- the validators with a vote in `votes` are fewer than twice `Sup`
    (hVoters : voters_count votes < 2 * Sup.card)
    -- the threshold is less than twice `Sup`
    (hThreshold : N < 2 * Sup.card)
    -- the test answers on every block
    (hEligibleAnswers : ∀ D : Block V, ∃ b : Bool, eligible D = .ok b)
    -- the test accepts every block after `A` up to `R` whose score `n` has `N < 2n`
    (hEligibleTrue : ∀ D : Block V, A.AncestorEq D → D ≠ A → D.AncestorEq R → ∀ n : ℕ,
      goldfish_score Φ votes support_votes s D = .ok n → N < 2 * n → eligible D = .ok true)
    -- the walk from `A` ends at `H`
    (hWalk : ghost A tree (goldfish_score Φ votes support_votes s) eligible = .ok H) :
    -- then `H` is `R` or a descendant of `R`
    R.AncestorEq H := by
  rcases hStart with hRA | ⟨hAR, hPath⟩
  · rcases ghost_spec hWalk with hH | ⟨hAH, -⟩
    · rw [hH]
      exact hRA
    · exact ancestorEq_trans hRA hAH
  · have hScore := goldfish_score_eq_ok hRoots votes support_votes s
    refine ghost_passes hAR hPath ?_ hWalk
    intro H₀ hAH₀ hH₀R hne r hr
    obtain ⟨C, hC, hCR⟩ := exists_child_towards hH₀R hne
    have hAC : A.AncestorEq C := ancestorEq_trans hAH₀ (ancestorEq_of_parent? hC)
    have hCA : C ≠ A := fun hCA => by
      have := depth_le_of_ancestorEq hAH₀
      rw [← hCA, depth_of_parent? hC] at this
      omega
    have hCtree : C ∈ tree := hPath C hAC hCA hCR
    -- every member of `Sup` supports `C`, so the test accepts `C`
    have hSupC : Sup ⊆ supportersOf Φ votes support_votes s C :=
      fun v hv => mem_supportersOf_of_votesOnceFor (hSup v hv) hCR
    have hcardC := Finset.card_le_card hSupC
    have hCel : eligible C = .ok true := hEligibleTrue C hAC hCA hCR _ (hScore C) (by omega)
    -- every other child of `H₀` conflicts with `R`, so it scores less than `C`
    have hdom : ∀ D ∈ tree, D.parent? = some H₀ → D ≠ C →
        (equivocators votes).card + (supportersOf Φ votes support_votes s D).card <
          (equivocators votes).card + (supportersOf Φ votes support_votes s C).card := by
      intro D _ hD hDC
      have hcount := card_add_le_voters hRoots hSupport hSup
        (conflicts_of_sibling_towards hC hD hCR hH₀R hne hDC)
      omega
    have hstep := ghost_step_towards
      (fun D => (equivocators votes).card + (supportersOf Φ votes support_votes s D).card)
      hC hCtree hCel hScore hEligibleAnswers hdom
    rw [hstep] at hr
    cases hr
    exact ⟨C, rfl, hC, hCR⟩

end GoldilocksCorrectness.Proofs.Routines
