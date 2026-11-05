module
public import GoldilocksCorrectness.Proofs.Routines.Lemma2
import all Goldilocks.AC.ForkChoice
import all Goldilocks.AC.State

@[expose] public section

/-!
# Lemma 3: the Goldfish fork choice extends a block a committee majority votes for

The proof of `lem3_goldfish_fork_choice_extends_committee_majority_block`, stated in
`GoldilocksCorrectness/Statements/Routines/WalkStatements.lean`.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 3, the Goldfish fork choice extends a block a committee majority votes for.** The
Goldfish fork choice from `A` through `tree` ends at `R` or a descendant of `R`, when `A` starts
towards `R` in `tree`, each member of `Hs` has one vote and it supports `R`'s chain, every voter
is a member of the slot-`s` committee, and `Hs` outnumbers the rest of the committee.

Why: Lemma 2 with `Sup := Hs`; the voters are members of the committee, so they number at most the
committee, which is less than twice `Hs`.

The variables:
- `C`: the configuration; `P`: the provisional parameters, with the committees;
- `Φ`: the frame; `t`: the time of the walk;
- `votes`, `support_votes`: the votes and the support votes the score counts; `s`: their slot;
- `A`: the block the walk starts from; `R`: the majority block; `H`: the block the walk ends at;
- `tree`: the tree walked; `Hs`: the members of the committee voting for `R`'s chain. -/
theorem lem3_goldfish_fork_choice_extends_committee_majority_block (C : Config)
    (P : Provisional V) (Φ : Frame V) (t : Time) (votes support_votes : Finset (GoldfishVote V))
    (s : Slot) (A R H : Block V) (tree : Finset (Block V)) (Hs : Finset V)
    (hStart : StartsTowards A R tree)
    (hRoots : RootsNameBlocksIn Φ.tree)
    -- every support vote is among the votes
    (hSupport : support_votes ⊆ votes)
    -- each member of `Hs` has one vote in `votes`, a slot-`s` support vote for `R`'s chain
    (hHs : ∀ v ∈ Hs, VotesOnceFor Φ votes support_votes s R v)
    -- every vote of `votes` is from a member of the slot-`s` committee
    (hCommittee : ∀ vote ∈ votes, vote.val_index ∈ P.committee s)
    -- the members of the committee outside `Hs` are fewer than `Hs`
    (hMajority : (P.committee s \ Hs).card < Hs.card)
    -- the Goldfish fork choice from `A` ends at `H`
    (hWalk : goldfish_fork_choice C Φ t A tree votes support_votes s = .ok H) :
    -- then `H` is `R` or a descendant of `R`
    R.AncestorEq H := by
  have hP : participants votes ⊆ P.committee s := fun v hv => by
    obtain ⟨vote, hvote, rfl⟩ := (mem_participants_iff votes v).1 hv
    exact hCommittee vote hvote
  have h1 := Finset.card_le_card hP
  have h2 := Finset.card_le_card_sdiff_add_card (s := P.committee s) (t := Hs)
  have hVoters : voters_count votes < 2 * Hs.card := by
    unfold voters_count
    omega
  exact lem2_goldfish_fork_choice_extends_majority_block C Φ t votes support_votes s A R H tree Hs
    hStart hRoots hSupport hHs hVoters hWalk

end GoldilocksCorrectness.Proofs.Routines
