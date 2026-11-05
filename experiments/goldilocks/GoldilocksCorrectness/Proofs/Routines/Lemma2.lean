module
public import GoldilocksCorrectness.Proofs.Routines.Lemma1
import all Goldilocks.AC.ForkChoice
import all Goldilocks.AC.State

@[expose] public section

/-!
# Lemma 2: the Goldfish fork choice extends a majority block

The proof of `lem2_goldfish_fork_choice_extends_majority_block`, stated in
`GoldilocksCorrectness/Statements/Routines/WalkStatements.lean`, with the two facts on the test
`goldfish_eligible` it reads: the test answers on every block (`goldfish_eligible_answers`), and
accepts every block whose doubled score exceeds the number of voters (`goldfish_eligible_of_score`).
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [RootOrder] in
/-- When no two blocks of `Φ.tree` share a root, the Goldfish eligibility test answers on every
block.

The variables:
- `C`: the configuration; `Φ`: the frame; `t`: the time;
- `votes`, `support_votes`: the votes and the support votes the score counts; `s`: their slot;
- `D`: the block tested. -/
theorem goldfish_eligible_answers (C : Config) {Φ : Frame V} (hRoots : RootsNameBlocksIn Φ.tree)
    (t : Time) (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (D : Block V) :
    ∃ b : Bool, goldfish_eligible C Φ t votes support_votes s D = .ok b := by
  simp only [goldfish_eligible, goldfish_score_eq_ok hRoots, dre_bind_ok]
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

omit [RootOrder] in
/-- The Goldfish eligibility test accepts every block whose score `n` has `voters_count votes <
2n`.

The variables:
- `C`: the configuration; `Φ`: the frame; `t`: the time;
- `votes`, `support_votes`: the votes and the support votes the score counts; `s`: their slot;
- `D`: the block tested; `n`: its score. -/
theorem goldfish_eligible_of_score (C : Config) (Φ : Frame V) (t : Time)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (D : Block V) (n : ℕ)
    (hn : goldfish_score Φ votes support_votes s D = .ok n) (hlt : voters_count votes < 2 * n) :
    goldfish_eligible C Φ t votes support_votes s D = .ok true := by
  simp only [goldfish_eligible, hn, dre_bind_ok]
  split
  · rfl
  · split
    · rfl
    · show Except.ok _ = Except.ok _
      simp [hlt]

/-- **Lemma 2, the Goldfish fork choice extends a majority block.** The Goldfish fork choice from
`A` through `tree` ends at `R` or a descendant of `R`, when `A` starts towards `R` in `tree`, each
member of `Sup` has one vote and it supports `R`'s chain, and the voters are fewer than twice
`Sup`.

Why: Lemma 1 with the fork choice's own test and the number of voters as the threshold: the test
accepts every block whose doubled score exceeds the number of voters.

The variables:
- `C`: the configuration; `Φ`: the frame; `t`: the time of the walk;
- `votes`, `support_votes`: the votes and the support votes the score counts; `s`: their slot;
- `A`: the block the walk starts from; `R`: the majority block; `H`: the block the walk ends at;
- `tree`: the tree walked; `Sup`: the validators voting for `R`'s chain. -/
theorem lem2_goldfish_fork_choice_extends_majority_block (C : Config) (Φ : Frame V) (t : Time)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (A R H : Block V)
    (tree : Finset (Block V)) (Sup : Finset V)
    (hStart : StartsTowards A R tree)
    (hRoots : RootsNameBlocksIn Φ.tree)
    -- every support vote is among the votes
    (hSupport : support_votes ⊆ votes)
    -- each member of `Sup` has one vote in `votes`, a slot-`s` support vote for `R`'s chain
    (hSup : ∀ v ∈ Sup, VotesOnceFor Φ votes support_votes s R v)
    -- the validators with a vote in `votes` are fewer than twice `Sup`
    (hVoters : voters_count votes < 2 * Sup.card)
    -- the Goldfish fork choice from `A` ends at `H`
    (hWalk : goldfish_fork_choice C Φ t A tree votes support_votes s = .ok H) :
    -- then `H` is `R` or a descendant of `R`
    R.AncestorEq H :=
  lem1_walk_extends_majority_block Φ votes support_votes s
    (goldfish_eligible C Φ t votes support_votes s) (voters_count votes) A R H tree Sup hStart
    hRoots hSupport hSup hVoters hVoters
    (goldfish_eligible_answers C hRoots t votes support_votes s)
    (fun D _ _ _ => goldfish_eligible_of_score C Φ t votes support_votes s D) hWalk

end GoldilocksCorrectness.Proofs.Routines
