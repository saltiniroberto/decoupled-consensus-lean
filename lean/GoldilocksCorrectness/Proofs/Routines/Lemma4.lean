module
public import GoldilocksCorrectness.Proofs.Routines.Lemma1

@[expose] public section

/-!
# Lemma 4: the walk ends exactly at a block every supporter names

The proof of `lem4_walk_ends_at_unanimous_block`, stated in
`GoldilocksCorrectness/Statements/Routines/WalkStatements.lean`.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 4, the walk ends at a block every supporter names.** The walk from `A`, an ancestor of
`R` or `R`, with every block after `A` up to `R` in `tree`, stepping onto a block exactly when `N`
is less than twice its score, ends exactly at `R`, when each member of `Sup` has one vote and its
head is `R`'s root, `R` is in `Φ.tree`, the voters are at most `N`, and `N` is less than twice
`Sup`.

Why: Lemma 1 gives that the walk ends at `R` or a descendant of `R`. A strict descendant of `R` is
supported by no member of `Sup`, so its doubled score is at most twice the voters minus twice
`Sup`, which is at most `N`: the test refuses it.



The variables:
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes the score counts;
- `s`: the slot of the votes; `N`: the test's threshold;
- `A`: the block the walk starts from; `R`: the block every supporter names; `H`: the block the
  walk ends at;
- `tree`: the tree walked; `Sup`: the validators naming `R`. -/
theorem lem4_walk_ends_at_unanimous_block (Φ : Frame V)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (N : ℕ) (A R H : Block V)
    (tree : Finset (Block V)) (Sup : Finset V)
    -- `A` is an ancestor of `R`, or `R`
    (hAR : A.AncestorEq R)
    -- every block after `A` up to `R`, `R` included, is in `tree`
    (hPath : ∀ P : Block V, A.AncestorEq P → P ≠ A → P.AncestorEq R → P ∈ tree)
    (hRoots : RootsNameBlocksIn Φ.tree)
    -- every support vote is among the votes
    (hSupport : support_votes ⊆ votes)
    -- each member of `Sup` has one vote in `votes`, a slot-`s` support vote whose head is `R`'s
    -- root
    (hSup : ∀ v ∈ Sup, ∃ vote ∈ support_votes, vote.val_index = v ∧ vote.slot = s ∧
      vote.head = R.root ∧ ∀ vote' ∈ votes, vote'.val_index = v → vote' = vote)
    -- `R` is a block of `Φ.tree`
    (hR : R ∈ Φ.tree)
    -- the validators with a vote in `votes` are at most the threshold
    (hVotersLe : voters_count votes ≤ N)
    -- the threshold is less than twice `Sup`
    (hThreshold : N < 2 * Sup.card)
    -- the walk from `A`, stepping onto a block when `N` is less than twice its score, ends at `H`
    (hWalk : ghost A tree (goldfish_score Φ votes support_votes s)
      (fun D => do return N < 2 * (← goldfish_score Φ votes support_votes s D)) = .ok H) :
    -- then `H` is `R`
    H = R := by
  -- the validators with a vote in `votes` are fewer than twice `Sup`
  have hVoters : voters_count votes < 2 * Sup.card := lt_of_le_of_lt hVotersLe hThreshold
  -- each member of `Sup` votes once for `R`'s chain
  have hSup' : ∀ v ∈ Sup, VotesOnceFor Φ votes support_votes s R v := by
    intro v hv
    obtain ⟨vote, hvote, hval, hs, hhead, hu⟩ := hSup v hv
    exact ⟨vote, hvote, hval, hs, ⟨R, hR, hhead.symm, ancestorEq_refl R⟩, hu⟩
  have hScore := goldfish_score_eq_ok hRoots votes support_votes s
  -- the test answers whether `N` is less than twice the score
  have hTest : ∀ D : Block V,
      (do return N < 2 * (← goldfish_score Φ votes support_votes s D) : DRE Bool) =
        .ok (decide (N < 2 *
          ((equivocators votes).card + (supportersOf Φ votes support_votes s D).card))) := by
    intro D
    simp only [hScore D, dre_bind_ok]
    rfl
  have hRH : R.AncestorEq H := lem1_walk_extends_majority_block Φ votes support_votes s
    (fun D => do return N < 2 * (← goldfish_score Φ votes support_votes s D)) N A R H tree Sup
    (Or.inr ⟨hAR, hPath⟩) hRoots hSupport hSup' hVoters hThreshold
    (fun D => ⟨_, hTest D⟩)
    (fun D _ _ _ n hn hlt => by
      simp only [hn, dre_bind_ok]
      show Except.ok _ = Except.ok _
      simp [hlt])
    hWalk
  by_contra hHR
  rcases ghost_spec hWalk with hHA | ⟨-, hel⟩
  · rw [hHA] at hRH hHR
    exact hHR (ancestorEq_antisymm hAR hRH)
  · rw [hTest H] at hel
    have hlt : N < 2 *
        ((equivocators votes).card + (supportersOf Φ votes support_votes s H).card) := by
      simpa using hel
    -- no member of `Sup` supports `H`, a strict descendant of `R`
    have hdisj : Disjoint (supportersOf Φ votes support_votes s H) Sup := by
      rw [Finset.disjoint_right]
      intro v hv hmem
      obtain ⟨vote, -, -, -, hhead, hu⟩ := hSup v hv
      obtain ⟨vote', hvote', hval', -, -, H', hH', hr', hHH'⟩ :=
        (mem_supportersOf_iff _ _ _ _ _ _).1 hmem
      have hvv : vote' = vote := hu vote' (hSupport hvote') hval'
      rw [hvv] at hr'
      have hH'R : H' = R := hRoots H' hH' R hR (hr'.trans hhead)
      rw [hH'R] at hHH'
      exact hHR (ancestorEq_antisymm hHH' hRH)
    have hcount := card_add_le_voters_of_disjoint hSupport (sup_subset_participants hSupport hSup')
      (Finset.disjoint_left.2 fun v hv => not_mem_equivocators_of_votesOnceFor (hSup' v hv)) hdisj
    omega

end GoldilocksCorrectness.Proofs.Routines
