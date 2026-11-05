module
public import GoldilocksCorrectness.Proofs.Routines.WalkEndLemmas
public import GoldilocksCorrectness.Statements.Routines.WalkStatements
public import GoldilocksCorrectness.Proofs.Routines.WalkEndMerge
public import GoldilocksCorrectness.Statements.Routines.WalkLeStatements
public import GoldilocksCorrectness.Statements.Routines.FrameStatements

@[expose] public section

/-!
# The statements about the walk predicate

The single-walk statements with the walk given by the predicate
`WalkEnd tree score eligible anchor H` (`Statements/Routines/WalkEndDefs.lean`) under any
tie-break (`TieBreak V`), each proved in `Proofs/Routines/WalkEndLemmas.lean` or
`Proofs/Routines/WalkEndMerge.lean`, and after each the
landed statement it replaces, recovered from it at the Goldilocks tie-break
(`goldilocksTieBreak`) through the bridge `walkEnd_of_ghost_eq_ok`
(`Proofs/Routines/WalkEndBridge.lean`):

- Lemma 1, `lem1_walkEnd_extends_majority_block`;
- Lemma 2, `lem2_goldfish_walkEnd_extends_majority_block`;
- Lemma 3, `lem3_goldfish_walkEnd_extends_committee_majority_block`;
- Lemma 4, `lem4_walkEnd_ends_at_unanimous_block`;
- Lemma 9, `lem9_walkEnd_ends_at_proposal_of_shared_block`, and Lemma 9 with the score
  argument, `lem9le_walkEnd_ends_at_proposal_of_shared_block`, proved by the merge lemmas of
  `Proofs/Routines/WalkEndMerge.lean`;
- Lemma 10, `lem10_walkEnd_ends_at_proposal_of_majority`;
- `walkEnd_viable_of_below` and `walkEnd_extends`, the forms of `walk_end_viable_of_below` and
  `walk_end_extends` (`Proofs/Routines/ForkChoiceFacts.lean`);
- Lemma 58, `lem58_walkEnd_is_viable_head`.

The bridge needs that no two blocks of the tree walked share a root. The landed statements of
Lemmas 1 to 4 assume it of `Φ.tree` only, and Lemma 10 of `tree_p` and `Φ.tree` only: their
recoveries (`…_recovered_of_rootsNameBlocksIn`) take it of the tree walked (of `tree_w` for
Lemma 10) as one more hypothesis. So do the recoveries of Lemmas 9 and 9le, whose landed
statements assume it of `tree_p` only. Lemma 58 is recovered exactly: its tree is the viable tree
of `Φ.tree`, a subset of `Φ.tree`. The two facts on the viable tree are recovered exactly
(`…_recovered`): their viable tree is a subset of `Φ.tree`.

Lemmas 6 and 7 (`lem6_get_anchor_compatible`, `lem7_startsTowards_of_compatible`) and
`walk_end_mem_T` name no walk and are unchanged; `walkEnd_mem_tree_or_eq`
(`Proofs/Routines/WalkEndLemmas.lean`) gives `walk_end_mem_T`'s hypothesis `hEnd` from a walk
predicate.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

open Goldilocks

variable {V : Type} [DecidableEq V]

/-- **Lemma 1 over the walk predicate.** The walk from `A` through `tree`, scoring with
`goldfish_score` and stepping onto blocks the test `eligible` accepts, under any tie-break, ends
at `R` or a descendant of `R`, when `A` starts towards `R` in `tree`, each member of `Sup` has one
vote and it supports `R`'s chain, the voters are fewer than twice `Sup`, and the test accepts
every block after `A` up to `R` whose score `n` has `N < 2n`, with `N` less than twice `Sup`.

Why: from a block on the way to `R`, the child towards `R` is supported by all of `Sup`, so the
test accepts it; any other child conflicts with `R`, so it scores less; so the walk steps to the
child towards `R` whatever the tie-break.

The variables:
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes the score counts;
- `s`: the slot of the votes; `eligible`: the eligibility test; `N`: the test's threshold;
- `A`: the block the walk starts from; `R`: the majority block; `H`: the block the walk ends at;
- `tree`: the tree walked; `Sup`: the validators voting for `R`'s chain.

Read aloud: whatever the tie-break, the walk from a start towards a majority block ends at that
block or a descendant of it. -/
theorem lem1_walkEnd_extends_majority_block [Fintype V] [TieBreak V] (Φ : Frame V)
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
    (hWalk : WalkEnd tree (goldfish_score Φ votes support_votes s) eligible A H) :
    -- then `H` is `R` or a descendant of `R`
    R.AncestorEq H :=
  GoldilocksCorrectness.Proofs.Routines.lem1_walkEnd_extends_majority_block Φ votes
    support_votes s eligible N A R H tree Sup hStart hRoots hSupport hSup hVoters hThreshold
    hEligibleAnswers hEligibleTrue hWalk

/-- The landed `lem1_walk_extends_majority_block`, recovered from Lemma 1 over the walk predicate
at the Goldilocks tie-break, when no two blocks of the tree walked share a root (a hypothesis the
landed statement does not have: it assumes it of `Φ.tree` only).

Why: the spec's walk ending at `H` gives the walk predicate ending at `H`
(`walkEnd_of_ghost_eq_ok`), which needs that no two blocks of `tree` share a root.

Read aloud: when no two blocks of the tree walked share a root, the landed Lemma 1 follows from
Lemma 1 over the walk predicate. -/
theorem lem1_walk_extends_majority_block_recovered_of_rootsNameBlocksIn [Fintype V] [RootOrder] :
    ∀ (Φ : Frame V) (votes support_votes : Finset (GoldfishVote V)) (s : Slot)
      (eligible : Block V → DRE Bool) (N : ℕ) (A R H : Block V) (tree : Finset (Block V))
      (Sup : Finset V),
      -- no two blocks of the tree walked share a root
      RootsNameBlocksIn tree →
      type_of% (@lem1_walk_extends_majority_block V _ _ _ Φ votes support_votes s eligible N A
        R H tree Sup) := by
  intro Φ votes support_votes s eligible N A R H tree Sup hTree hStart hRoots hSupport hSup
    hVoters hThreshold hEligibleAnswers hEligibleTrue hWalk
  letI : TieBreak V := GoldilocksCorrectness.Proofs.Routines.goldilocksTieBreak
  exact lem1_walkEnd_extends_majority_block Φ votes support_votes s eligible N A R H tree Sup
    hStart hRoots hSupport hSup hVoters hThreshold hEligibleAnswers hEligibleTrue
    (GoldilocksCorrectness.Proofs.Routines.walkEnd_of_ghost_eq_ok hTree hWalk)

/-- **Lemma 2 over the walk predicate.** The walk from `A` through `tree` with the Goldfish score
and the Goldfish eligibility test, under any tie-break, ends at `R` or a descendant of `R`, when
`A` starts towards `R` in `tree`, each member of `Sup` has one vote and it supports `R`'s chain,
and the voters are fewer than twice `Sup`.

Why: Lemma 1 over the walk predicate with the Goldfish test and the number of voters as the
threshold.

The variables:
- `C`: the configuration; `Φ`: the frame; `t`: the time of the walk;
- `votes`, `support_votes`: the votes and the support votes the score counts; `s`: their slot;
- `A`: the block the walk starts from; `R`: the majority block; `H`: the block the walk ends at;
- `tree`: the tree walked; `Sup`: the validators voting for `R`'s chain.

Read aloud: whatever the tie-break, the Goldfish walk from a start towards a majority block ends
at that block or a descendant of it. -/
theorem lem2_goldfish_walkEnd_extends_majority_block [Fintype V] [TieBreak V] (C : Config)
    (Φ : Frame V) (t : Time) (votes support_votes : Finset (GoldfishVote V)) (s : Slot)
    (A R H : Block V) (tree : Finset (Block V)) (Sup : Finset V)
    (hStart : StartsTowards A R tree)
    (hRoots : RootsNameBlocksIn Φ.tree)
    -- every support vote is among the votes
    (hSupport : support_votes ⊆ votes)
    -- each member of `Sup` has one vote in `votes`, a slot-`s` support vote for `R`'s chain
    (hSup : ∀ v ∈ Sup, VotesOnceFor Φ votes support_votes s R v)
    -- the validators with a vote in `votes` are fewer than twice `Sup`
    (hVoters : voters_count votes < 2 * Sup.card)
    -- the walk from `A` with the Goldfish score and test ends at `H`
    (hWalk : WalkEnd tree (goldfish_score Φ votes support_votes s)
      (goldfish_eligible C Φ t votes support_votes s) A H) :
    -- then `H` is `R` or a descendant of `R`
    R.AncestorEq H :=
  GoldilocksCorrectness.Proofs.Routines.lem2_goldfish_walkEnd_extends_majority_block C Φ t votes
    support_votes s A R H tree Sup hStart hRoots hSupport hSup hVoters hWalk

/-- The landed `lem2_goldfish_fork_choice_extends_majority_block`, recovered from Lemma 2 over the
walk predicate at the Goldilocks tie-break, when no two blocks of the tree walked share a root (a
hypothesis the landed statement does not have).

Why: `goldfish_fork_choice_eq_ok_iff_walkEnd`, which needs that no two blocks of `tree` share a
root.

Read aloud: when no two blocks of the tree walked share a root, the landed Lemma 2 follows from
Lemma 2 over the walk predicate. -/
theorem lem2_goldfish_fork_choice_extends_majority_block_recovered_of_rootsNameBlocksIn
    [Fintype V] [RootOrder] :
    ∀ (C : Config) (Φ : Frame V) (t : Time) (votes support_votes : Finset (GoldfishVote V))
      (s : Slot) (A R H : Block V) (tree : Finset (Block V)) (Sup : Finset V),
      -- no two blocks of the tree walked share a root
      RootsNameBlocksIn tree →
      type_of% (@lem2_goldfish_fork_choice_extends_majority_block V _ _ _ C Φ t votes
        support_votes s A R H tree Sup) := by
  intro C Φ t votes support_votes s A R H tree Sup hTree hStart hRoots hSupport hSup hVoters hWalk
  letI : TieBreak V := GoldilocksCorrectness.Proofs.Routines.goldilocksTieBreak
  exact lem2_goldfish_walkEnd_extends_majority_block C Φ t votes support_votes s A R H tree Sup
    hStart hRoots hSupport hSup hVoters
    ((GoldilocksCorrectness.Proofs.Routines.goldfish_fork_choice_eq_ok_iff_walkEnd C Φ t A tree
      votes support_votes s hTree).1 hWalk)

/-- **Lemma 3 over the walk predicate.** The walk from `A` through `tree` with the Goldfish score
and the Goldfish eligibility test, under any tie-break, ends at `R` or a descendant of `R`, when
`A` starts towards `R` in `tree`, each member of `Hs` has one vote and it supports `R`'s chain,
every voter is a member of the slot-`s` committee, and `Hs` outnumbers the rest of the
committee.

Why: Lemma 2 over the walk predicate with `Sup := Hs`; the voters are members of the committee,
so they number at most the committee, which is less than twice `Hs`.

The variables:
- `C`: the configuration; `P`: the provisional parameters, with the committees;
- `Φ`: the frame; `t`: the time of the walk;
- `votes`, `support_votes`: the votes and the support votes the score counts; `s`: their slot;
- `A`: the block the walk starts from; `R`: the majority block; `H`: the block the walk ends at;
- `tree`: the tree walked; `Hs`: the members of the committee voting for `R`'s chain.

Read aloud: whatever the tie-break, the Goldfish walk from a start towards a block a committee
majority votes for ends at that block or a descendant of it. -/
theorem lem3_goldfish_walkEnd_extends_committee_majority_block [Fintype V] [TieBreak V]
    (C : Config) (P : Provisional V) (Φ : Frame V) (t : Time)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (A R H : Block V)
    (tree : Finset (Block V)) (Hs : Finset V)
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
    -- the walk from `A` with the Goldfish score and test ends at `H`
    (hWalk : WalkEnd tree (goldfish_score Φ votes support_votes s)
      (goldfish_eligible C Φ t votes support_votes s) A H) :
    -- then `H` is `R` or a descendant of `R`
    R.AncestorEq H :=
  GoldilocksCorrectness.Proofs.Routines.lem3_goldfish_walkEnd_extends_committee_majority_block
    C P Φ t votes support_votes s A R H tree Hs hStart hRoots hSupport hHs hCommittee hMajority
    hWalk

/-- The landed `lem3_goldfish_fork_choice_extends_committee_majority_block`, recovered from
Lemma 3 over the walk predicate at the Goldilocks tie-break, when no two blocks of the tree walked
share a root (a hypothesis the landed statement does not have).

Why: `goldfish_fork_choice_eq_ok_iff_walkEnd`, which needs that no two blocks of `tree` share a
root.

Read aloud: when no two blocks of the tree walked share a root, the landed Lemma 3 follows from
Lemma 3 over the walk predicate. -/
theorem lem3_goldfish_fork_choice_extends_committee_majority_block_recovered_of_rootsNameBlocksIn
    [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (Φ : Frame V) (t : Time)
      (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (A R H : Block V)
      (tree : Finset (Block V)) (Hs : Finset V),
      -- no two blocks of the tree walked share a root
      RootsNameBlocksIn tree →
      type_of% (@lem3_goldfish_fork_choice_extends_committee_majority_block V _ _ _ C P Φ t
        votes support_votes s A R H tree Hs) := by
  intro C P Φ t votes support_votes s A R H tree Hs hTree hStart hRoots hSupport hHs hCommittee
    hMajority hWalk
  letI : TieBreak V := GoldilocksCorrectness.Proofs.Routines.goldilocksTieBreak
  exact lem3_goldfish_walkEnd_extends_committee_majority_block C P Φ t votes support_votes s A R
    H tree Hs hStart hRoots hSupport hHs hCommittee hMajority
    ((GoldilocksCorrectness.Proofs.Routines.goldfish_fork_choice_eq_ok_iff_walkEnd C Φ t A tree
      votes support_votes s hTree).1 hWalk)

/-- **Lemma 4 over the walk predicate.** The walk from `A`, an ancestor of `R` or `R`, with every
block after `A` up to `R` in `tree`, stepping onto a block exactly when `N` is less than twice its
score, under any tie-break, ends exactly at `R`, when each member of `Sup` has one vote and its
head is `R`'s root, `R` is in `Φ.tree`, the voters are at most `N`, and `N` is less than twice
`Sup`.

Why: Lemma 1 over the walk predicate gives that the walk ends at `R` or a descendant of `R`; a
strict descendant of `R` is supported by no member of `Sup`, so the test refuses it.

The variables:
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes the score counts;
- `s`: the slot of the votes; `N`: the test's threshold;
- `A`: the block the walk starts from; `R`: the block every supporter names; `H`: the block the
  walk ends at;
- `tree`: the tree walked; `Sup`: the validators naming `R`.

Read aloud: whatever the tie-break, the walk ends exactly at a block every supporter names. -/
theorem lem4_walkEnd_ends_at_unanimous_block [Fintype V] [TieBreak V] (Φ : Frame V)
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
    (hWalk : WalkEnd tree (goldfish_score Φ votes support_votes s)
      (fun D => do return N < 2 * (← goldfish_score Φ votes support_votes s D)) A H) :
    -- then `H` is `R`
    H = R :=
  GoldilocksCorrectness.Proofs.Routines.lem4_walkEnd_ends_at_unanimous_block Φ votes
    support_votes s N A R H tree Sup hAR hPath hRoots hSupport hSup hR hVotersLe hThreshold hWalk

/-- The landed `lem4_walk_ends_at_unanimous_block`, recovered from Lemma 4 over the walk
predicate at the Goldilocks tie-break, when no two blocks of the tree walked share a root (a
hypothesis the landed statement does not have).

Why: `walkEnd_of_ghost_eq_ok`, which needs that no two blocks of `tree` share a root.

Read aloud: when no two blocks of the tree walked share a root, the landed Lemma 4 follows from
Lemma 4 over the walk predicate. -/
theorem lem4_walk_ends_at_unanimous_block_recovered_of_rootsNameBlocksIn [Fintype V] [RootOrder] :
    ∀ (Φ : Frame V) (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (N : ℕ)
      (A R H : Block V) (tree : Finset (Block V)) (Sup : Finset V),
      -- no two blocks of the tree walked share a root
      RootsNameBlocksIn tree →
      type_of% (@lem4_walk_ends_at_unanimous_block V _ _ _ Φ votes support_votes s N A R H tree
        Sup) := by
  intro Φ votes support_votes s N A R H tree Sup hTree hAR hPath hRoots hSupport hSup hR
    hVotersLe hThreshold hWalk
  letI : TieBreak V := GoldilocksCorrectness.Proofs.Routines.goldilocksTieBreak
  exact lem4_walkEnd_ends_at_unanimous_block Φ votes support_votes s N A R H tree Sup hAR hPath
    hRoots hSupport hSup hR hVotersLe hThreshold
    (GoldilocksCorrectness.Proofs.Routines.walkEnd_of_ghost_eq_ok hTree hWalk)

/-- **Lemma 9 over the walk predicate.** Two walks under the same tie-break: the first, from
`A_p` over `tree_p`, ends at `P`'s parent; the second, from `A_w` over `tree_w`, ends at `H_w`.
If the two scores answer the same number on every child of a block from `X` to `P`'s parent, the
first walk passes `X`, the second starts at `X` or an ancestor of `X` and passes `X`, the blocks
of the first walk after `X` and `P` are in `tree_w`, `P` is eligible in the second walk and has
no child in `tree_w`, the second test accepts every block after `X` up to `P`'s parent, and every
child in `tree_w` of a block from `X` to `P`'s parent, other than `P`, that the second test
accepts is in `tree_p` and accepted by the first test, then the second walk ends at `P`.

Why: from `X` on, before `P`'s parent, the second walk takes the first walk's steps, since the
tie-break keeps its pick when the candidates it did not pick are removed; at `P`'s parent `P` is
the second walk's only eligible child, since the first walk ends there; at `P` no step leaves.
No hypothesis on the roots of `tree_p` is needed.

The variables:
- `A_p`, `tree_p`, `score_p`, `eligible_p`: the first walk; `A_w`, `tree_w`, `score_w`,
  `eligible_w`: the second; `H_w`: where the second ends;
- `X`: the block both pass; `P`: the block after the first walk's end;
- `n`: the scores' answers; `b_p`, `b_w`: the two tests' answers.

Read aloud: under one tie-break, a walk that agrees with another from a shared block on ends at
the proposal that extends the other's end. -/
theorem lem9_walkEnd_ends_at_proposal_of_shared_block [TieBreak V] {A_p A_w X P H_w : Block V}
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
    -- `P` is a child of its parent: `P` is not the genesis block
    (hPpar : P.parent? = some P.parent)
    -- the first walk ends at `P`'s parent
    (hWalkP : WalkEnd tree_p score_p eligible_p A_p P.parent)
    -- the second walk ends at `H_w`
    (hWalkW : WalkEnd tree_w score_w eligible_w A_w H_w)
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
  GoldilocksCorrectness.Proofs.Routines.lem9_walkEnd_ends_at_proposal_of_shared_block n b_p b_w
    hScoreP hScoreW hTestP hTestW hPpar hWalkP hWalkW hXOnWalkP hRootWX hXW hPathInTreeW hPInTree
    hPTest hNoChildP hPathTest hEligSub

/-- The landed `lem9_walk_ends_at_proposal_of_shared_block`, recovered from Lemma 9 over the walk
predicate at the Goldilocks tie-break, when no two blocks of `tree_w` share a root (a hypothesis
the landed statement does not have; it has the same of `tree_p`, `hRootsP`).

Why: `walkEnd_of_ghost_eq_ok` at each walk, which needs that no two blocks of the tree walked
share a root: `hRootsP` for the first, the added hypothesis for the second.

Read aloud: when no two blocks of the second tree share a root, the landed Lemma 9 follows from
Lemma 9 over the walk predicate. -/
theorem lem9_walk_ends_at_proposal_of_shared_block_recovered_of_rootsNameBlocksIn [RootOrder] :
    ∀ {A_p A_w X P H_w : Block V} {tree_p tree_w : Finset (Block V)}
      {score_p score_w : Block V → DRE Nat} {eligible_p eligible_w : Block V → DRE Bool},
      -- no two blocks of `tree_w` share a root
      RootsNameBlocksIn tree_w →
      type_of% (@lem9_walk_ends_at_proposal_of_shared_block V _ _ A_p A_w X P H_w tree_p tree_w
        score_p score_w eligible_p eligible_w) := by
  intro A_p A_w X P H_w tree_p tree_w score_p score_w eligible_p eligible_w hTreeW n b_p b_w
    hScoreP hScoreW hTestP hTestW hRootsP hPpar hWalkP hWalkW hXOnWalkP hRootWX hXW hPathInTreeW
    hPInTree hPTest hNoChildP hPathTest hEligSub
  letI : TieBreak V := GoldilocksCorrectness.Proofs.Routines.goldilocksTieBreak
  exact lem9_walkEnd_ends_at_proposal_of_shared_block n b_p b_w hScoreP hScoreW hTestP hTestW hPpar
    (GoldilocksCorrectness.Proofs.Routines.walkEnd_of_ghost_eq_ok hRootsP hWalkP)
    (GoldilocksCorrectness.Proofs.Routines.walkEnd_of_ghost_eq_ok hTreeW hWalkW)
    hXOnWalkP hRootWX hXW hPathInTreeW hPInTree hPTest hNoChildP hPathTest hEligSub

/-- **Lemma 10 over the walk predicate.** Two walks under the same tie-break score the same
slot-`s` votes with `goldfish_score`: the first, from `A_p` over `tree_p`, ends at `P`'s parent;
the second, from `A_w` over `tree_w`, ends at `H_w`. The second ends at `P`, when each member of
a set `Sup` has one vote and it supports `X`'s chain, the voters are fewer than twice `Sup`, both
tests answer on every block, each test accepts every block after its walk's start up to `X` whose
score `n` has `N < 2n`, with `N` less than twice `Sup`, both walks start at `X` or an ancestor of
`X` with every block after their start up to `X` in their tree, the blocks after `X` up to `P`'s
parent and `P` are in `tree_w`, the second test accepts `P`, no block of `tree_w` is a child of
`P`, the second test accepts every block after `X` up to `P`'s parent, and every child in
`tree_w` of a block from `X` to `P`'s parent, other than `P`, that the second test accepts is in
`tree_p` and accepted by the first test.

Why: Lemma 1 over the walk predicate at each walk gives that it passes `X`; then Lemma 9 over the
walk predicate (`GoldilocksCorrectness.Proofs.Routines.lem9_walkEnd_ends_at_proposal_of_shared_block`).

The variables:
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes both scores count;
- `s`: the slot of the votes; `eligible_p`, `eligible_w`: the two tests; `N`: their threshold;
- `A_p`, `A_w`: the starts of the two walks; `X`: the block both pass; `P`: the block after the
  first walk's end; `H_w`: where the second walk ends; `tree_p`, `tree_w`: the two trees;
- `Sup`: the validators voting for `X`'s chain; `b_p`, `b_w`: the two tests' answers.

Read aloud: under one tie-break, when a majority votes for a block both walks pass, the second
walk ends at the proposal extending the first walk's end. -/
theorem lem10_walkEnd_ends_at_proposal_of_majority [Fintype V] [TieBreak V] (Φ : Frame V)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot)
    (eligible_p eligible_w : Block V → DRE Bool) (N : ℕ) (A_p A_w X P H_w : Block V)
    (tree_p tree_w : Finset (Block V)) (Sup : Finset V) (b_p b_w : Block V → Bool)
    -- no two blocks of `Φ.tree` share a root
    (hRoots : RootsNameBlocksIn Φ.tree)
    -- every support vote is among the votes
    (hSupport : support_votes ⊆ votes)
    -- each member of `Sup` has one vote in `votes`, a slot-`s` support vote for `X`'s chain
    (hSup : ∀ v ∈ Sup, VotesOnceFor Φ votes support_votes s X v)
    -- the validators with a vote in `votes` are fewer than twice `Sup`
    (hVoters : voters_count votes < 2 * Sup.card)
    -- the threshold is less than twice `Sup`
    (hThreshold : N < 2 * Sup.card)
    -- the first test answers `b_p D` on every block `D`
    (hTestP : ∀ D : Block V, eligible_p D = .ok (b_p D))
    -- the second test answers `b_w D` on every block `D`
    (hTestW : ∀ D : Block V, eligible_w D = .ok (b_w D))
    -- the first test accepts every block after `A_p` up to `X` whose score `n` has `N < 2n`
    (hTrueP : ∀ D : Block V, A_p.AncestorEq D → D ≠ A_p → D.AncestorEq X → ∀ n : ℕ,
      goldfish_score Φ votes support_votes s D = .ok n → N < 2 * n → b_p D = true)
    -- the second test accepts every block after `A_w` up to `X` whose score `n` has `N < 2n`
    (hTrueW : ∀ D : Block V, A_w.AncestorEq D → D ≠ A_w → D.AncestorEq X → ∀ n : ℕ,
      goldfish_score Φ votes support_votes s D = .ok n → N < 2 * n → b_w D = true)
    -- `P` is a child of its parent: `P` is not the genesis block
    (hPpar : P.parent? = some P.parent)
    -- `A_p` is `X` or an ancestor of `X`
    (hApX : A_p.AncestorEq X)
    -- every block after `A_p` up to `X` is in `tree_p`
    (hPathP : ∀ Y : Block V, A_p.AncestorEq Y → Y ≠ A_p → Y.AncestorEq X → Y ∈ tree_p)
    -- `A_w` is `X` or an ancestor of `X`
    (hAwX : A_w.AncestorEq X)
    -- every block after `A_w` up to `X` is in `tree_w`
    (hPathW : ∀ Y : Block V, A_w.AncestorEq Y → Y ≠ A_w → Y.AncestorEq X → Y ∈ tree_w)
    -- the first walk ends at `P`'s parent
    (hWalkP : WalkEnd tree_p (goldfish_score Φ votes support_votes s) eligible_p A_p P.parent)
    -- the second walk ends at `H_w`
    (hWalkW : WalkEnd tree_w (goldfish_score Φ votes support_votes s) eligible_w A_w H_w)
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
  GoldilocksCorrectness.Proofs.Routines.lem10_walkEnd_ends_at_proposal_of_majority Φ votes
    support_votes s eligible_p eligible_w N A_p A_w X P H_w tree_p tree_w Sup b_p b_w hRoots
    hSupport hSup hVoters hThreshold hTestP hTestW hTrueP hTrueW hPpar hApX hPathP hAwX
    hPathW hWalkP hWalkW hPathInTreeW hPInTree hPTest hNoChildP hPathTest hEligSub

/-- The landed `lem10_walk_ends_at_proposal_of_majority`, recovered from Lemma 10 over the walk
predicate at the Goldilocks tie-break, when no two blocks of `tree_w` share a root (a hypothesis
the landed statement does not have; it has the same of `tree_p`, `hRootsP`).

Why: `walkEnd_of_ghost_eq_ok` at each walk, which needs that no two blocks of the tree walked
share a root: `hRootsP` for the first, the added hypothesis for the second.

Read aloud: when no two blocks of the second tree share a root, the landed Lemma 10 follows from
Lemma 10 over the walk predicate. -/
theorem lem10_walk_ends_at_proposal_of_majority_recovered_of_rootsNameBlocksIn [Fintype V]
    [RootOrder] :
    ∀ (Φ : Frame V) (votes support_votes : Finset (GoldfishVote V)) (s : Slot)
      (eligible_p eligible_w : Block V → DRE Bool) (N : ℕ) (A_p A_w X P H_w : Block V)
      (tree_p tree_w : Finset (Block V)) (Sup : Finset V) (b_p b_w : Block V → Bool),
      -- no two blocks of `tree_w` share a root
      RootsNameBlocksIn tree_w →
      type_of% (@lem10_walk_ends_at_proposal_of_majority V _ _ _ Φ votes support_votes s
        eligible_p eligible_w N A_p A_w X P H_w tree_p tree_w Sup b_p b_w) := by
  intro Φ votes support_votes s eligible_p eligible_w N A_p A_w X P H_w tree_p tree_w Sup b_p b_w
    hTreeW hRoots hSupport hSup hVoters hThreshold hTestP hTestW hTrueP hTrueW hRootsP hPpar hApX
    hPathP hAwX hPathW hWalkP hWalkW hPathInTreeW hPInTree hPTest hNoChildP hPathTest hEligSub
  letI : TieBreak V := GoldilocksCorrectness.Proofs.Routines.goldilocksTieBreak
  exact lem10_walkEnd_ends_at_proposal_of_majority Φ votes support_votes s eligible_p eligible_w N
    A_p A_w X P H_w tree_p tree_w Sup b_p b_w hRoots hSupport hSup hVoters hThreshold hTestP
    hTestW hTrueP hTrueW hPpar hApX hPathP hAwX hPathW
    (GoldilocksCorrectness.Proofs.Routines.walkEnd_of_ghost_eq_ok hRootsP hWalkP)
    (GoldilocksCorrectness.Proofs.Routines.walkEnd_of_ghost_eq_ok hTreeW hWalkW)
    hPathInTreeW hPInTree hPTest hNoChildP hPathTest hEligSub

/-- **Lemma 9 with the score argument, over the walk predicate.** Two walks under the same
tie-break: the first, from `A_p` over `tree_p`, ends at `P`'s parent; the second, from `A_w` over
`tree_w`, ends at `H_w`. If the two scores answer the same number on every child of a block from
`X` to `P`'s parent, the first walk passes `X`, the second starts at `X` or an ancestor of `X` and
passes `X`, the blocks of the first walk after `X` and `P` are in `tree_w`, `P` is eligible in the
second walk and has no child in `tree_w`, the second test accepts every block after `X` up to
`P`'s parent; every child in `tree_w` of a block from `X` to `P`'s parent, other than that parent,
that the second test accepts, is in `tree_p` and accepted by the first test, or has a score less
than that of every child of that block in `tree_p` that is `P`'s parent or an ancestor of it and
that the first test accepts; and every child of `P`'s parent in `tree_w`, other than `P`, that the
second test accepts, is in `tree_p` and accepted by the first test — then the second walk ends at
`P`.

Why: at a block of the path before `P`'s parent the first walk steps to the child `C` on the path,
which it accepts and holds; every child the second test accepts is one the first walk could step
to or scores less than `C`, so the second walk steps to `C` too, the tie-break keeping its pick;
at `P`'s parent `P` is the only eligible child of the second walk; at `P` the second walk stops
(`walkEnd_merge_le`). No hypothesis on the roots of `tree_p` is needed.

The variables:
- `A_p`, `tree_p`, `score_p`, `eligible_p`: the first walk; `A_w`, `tree_w`, `score_w`,
  `eligible_w`: the second; `H_w`: where the second ends;
- `X`: the block both pass; `P`: the block after the first walk's end;
- `n`: the scores' answers; `b_p`, `b_w`: the two tests' answers.

Read aloud: under one tie-break, when, along the path, each child the second walk could step to
is one the first walk could step to or loses to every child of the path the first walk accepts,
and at the first walk's end only `P` is left to the second, the second walk ends at `P`. -/
theorem lem9le_walkEnd_ends_at_proposal_of_shared_block [TieBreak V] {A_p A_w X P H_w : Block V}
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
    -- `P` is a child of its parent: `P` is not the genesis block
    (hPpar : P.parent? = some P.parent)
    -- the first walk ends at `P`'s parent
    (hWalkP : WalkEnd tree_p score_p eligible_p A_p P.parent)
    -- the second walk ends at `H_w`
    (hWalkW : WalkEnd tree_w score_w eligible_w A_w H_w)
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
    H_w = P :=
  GoldilocksCorrectness.Proofs.Routines.walkEnd_merge_le n b_p b_w hScoreP hScoreW hTestP hTestW
    hPpar hWalkP hWalkW hXOnWalkP hRootWX hXW hPathInTreeW hPInTree hPTest hNoChildP hPathTest
    hEligSubLe hEligSubEnd

/-- The landed `lem9le_walk_ends_at_proposal_of_shared_block`, recovered from Lemma 9 with the
score argument over the walk predicate at the Goldilocks tie-break, when no two blocks of `tree_w`
share a root (a hypothesis the landed statement does not have; it has the same of `tree_p`,
`hRootsP`).

Why: `walkEnd_of_ghost_eq_ok` at each walk: `hRootsP` for the first, the added hypothesis for the
second.

Read aloud: when no two blocks of the second tree share a root, the landed Lemma 9 with the score
argument follows from its form over the walk predicate. -/
theorem lem9le_walk_ends_at_proposal_of_shared_block_recovered_of_rootsNameBlocksIn [RootOrder] :
    ∀ {A_p A_w X P H_w : Block V} {tree_p tree_w : Finset (Block V)}
      {score_p score_w : Block V → DRE Nat} {eligible_p eligible_w : Block V → DRE Bool},
      -- no two blocks of `tree_w` share a root
      RootsNameBlocksIn tree_w →
      type_of% (@lem9le_walk_ends_at_proposal_of_shared_block V _ _ A_p A_w X P H_w tree_p tree_w
        score_p score_w eligible_p eligible_w) := by
  intro A_p A_w X P H_w tree_p tree_w score_p score_w eligible_p eligible_w hTreeW n b_p b_w
    hScoreP hScoreW hTestP hTestW hRootsP hPpar hWalkP hWalkW hXOnWalkP hRootWX hXW hPathInTreeW
    hPInTree hPTest hNoChildP hPathTest hEligSubLe hEligSubEnd
  letI : TieBreak V := GoldilocksCorrectness.Proofs.Routines.goldilocksTieBreak
  exact lem9le_walkEnd_ends_at_proposal_of_shared_block n b_p b_w hScoreP hScoreW hTestP hTestW
    hPpar (GoldilocksCorrectness.Proofs.Routines.walkEnd_of_ghost_eq_ok hRootsP hWalkP)
    (GoldilocksCorrectness.Proofs.Routines.walkEnd_of_ghost_eq_ok hTreeW hWalkW)
    hXOnWalkP hRootWX hXW hPathInTreeW hPInTree hPTest hNoChildP hPathTest hEligSubLe hEligSubEnd

/-- The end `H` of the walk from `A` through the viable tree of `VT`, with the Goldfish score and
the Goldfish eligibility test, under any tie-break, is a viable head, when `H` is on the chain of
the frame's fork-choice root, `H` is a strict ancestor of a viable head `Z ∈ VT`, and `VT` holds
every block from the root to a block of `VT`.

Why: the child of `H` towards `Z` is in the viable tree of `VT`, and when `H` is not a viable head
the Goldfish test accepts it, while at the walk's end the test accepts no child of `H`.

The variables:
- `C`: the parameters; `Φ`: the frame; `t`: the time; `A`: the start; `VT`: the tree;
- `votes`, `sv`: the counted votes; `s`: their slot; `H`: the walk's end; `Z`: the viable head.

Read aloud: whatever the tie-break, when the Goldfish walk through a viable tree ends at a strict
ancestor of a viable head of the tree, the end is itself a viable head. -/
theorem walkEnd_viable_of_below [Fintype V] [TieBreak V] (C : Config) (Φ : Frame V) (t : Time)
    (A : Block V) (VT : Finset (Block V)) (votes sv : Finset (GoldfishVote V)) (s : Slot)
    (H Z : Block V)
    (hClosed : ∀ Z' ∈ VT, ∀ c : Block V, Φ.fc_root.AncestorEq c → c.AncestorEq Z' → c ∈ VT)
    (hWalk : WalkEnd (viable_tree Φ VT) (goldfish_score Φ votes sv s)
      (goldfish_eligible C Φ t votes sv s) A H)
    (hρH : Φ.fc_root.AncestorEq H) (hZ : Z ∈ VT) (hZv : Z ∈ Φ.viable_heads)
    (hHZ : H.AncestorEq Z) (hne : H ≠ Z) :
    H ∈ Φ.viable_heads :=
  GoldilocksCorrectness.Proofs.Routines.walkEnd_viable_of_below C Φ t A VT votes sv s H Z hClosed
    hWalk hρH hZ hZv hHZ hne

/-- The landed `walk_end_viable_of_below`, recovered from `walkEnd_viable_of_below` at the
Goldilocks tie-break.

Why: the viable tree of `VT` is a subset of `VT`, so of `Φ.tree`, and no two of its blocks share
a root; then `goldfish_fork_choice_eq_ok_iff_walkEnd`.

Read aloud: the landed fact on where the Goldfish fork choice through a viable tree ends follows
from its form over the walk predicate. -/
theorem walk_end_viable_of_below_recovered [Fintype V] [RootOrder] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.walk_end_viable_of_below V _ _ _) := by
  intro C Φ t A VT votes sv s H Z hRoots hVT hClosed hWalk hρH hZ hZv hHZ hne
  letI : TieBreak V := GoldilocksCorrectness.Proofs.Routines.goldilocksTieBreak
  have hsub : viable_tree Φ VT ⊆ Φ.tree := fun B hB =>
    hVT ((GoldilocksCorrectness.Proofs.Routines.mem_viable_tree_iff Φ VT B).1 hB).1
  exact walkEnd_viable_of_below C Φ t A VT votes sv s H Z hClosed
    ((GoldilocksCorrectness.Proofs.Routines.goldfish_fork_choice_eq_ok_iff_walkEnd C Φ t A
      (viable_tree Φ VT) votes sv s
      (GoldilocksCorrectness.Proofs.Routines.rootsNameBlocksIn_mono hsub hRoots)).1 hWalk)
    hρH hZ hZv hHZ hne

/-- **The end of the Goldfish walk extends a block every viable head extends**, under any
tie-break. When the walk from the anchor `A` (the fork-choice root, or a block of the viable tree
of the frame's tree) through the viable tree of `VT`, with the Goldfish score and the Goldfish
eligibility test, ends at `H`; `VT` holds a viable head `Y` and every block from the root to a
block of `VT`; every viable head is `F'` or a descendant of `F'`; and no strict ancestor of `F'`
is a viable head — then `H` is `F'` or a descendant of `F'`.

Why: the end is the anchor or a block of the viable tree of `VT`; a block on `F'`'s chain that is
a strict ancestor of `F'` is not a viable head, and the walk does not end there
(`walkEnd_viable_of_below`).

The variables:
- `C`: the parameters; `Φ`: the frame; `t`: the time; `A`: the anchor; `VT`: the tree;
- `votes`, `sv`: the counted votes; `s`: their slot; `H`: the walk's end; `F'`: the block;
  `Y`: a viable head of `VT`.

Read aloud: whatever the tie-break, the Goldfish walk through a viable tree ends at `F'` or a
descendant of it, when every viable head descends from `F'` and no strict ancestor of `F'` is a
viable head. -/
theorem walkEnd_extends [Fintype V] [TieBreak V] (C : Config) (Φ : Frame V) (t : Time)
    (A : Block V) (VT : Finset (Block V)) (votes sv : Finset (GoldfishVote V)) (s : Slot)
    (H F' Y : Block V)
    (hClosed : ∀ Z' ∈ VT, ∀ c : Block V, Φ.fc_root.AncestorEq c → c.AncestorEq Z' → c ∈ VT)
    (hA : A = Φ.fc_root ∨ A ∈ viable_tree Φ Φ.tree)
    (hWalk : WalkEnd (viable_tree Φ VT) (goldfish_score Φ votes sv s)
      (goldfish_eligible C Φ t votes sv s) A H)
    (hρV : ∀ W ∈ Φ.viable_heads, Φ.fc_root.AncestorEq W)
    (hYVT : Y ∈ VT) (hY : Y ∈ Φ.viable_heads)
    (hP : ∀ W ∈ Φ.viable_heads, F'.AncestorEq W)
    (hQ : ∀ B : Block V, B.AncestorEq F' → B ≠ F' → B ∉ Φ.viable_heads) :
    F'.AncestorEq H :=
  GoldilocksCorrectness.Proofs.Routines.walkEnd_extends C Φ t A VT votes sv s H F' Y hClosed
    hA hWalk hρV hYVT hY hP hQ

/-- The landed `walk_end_extends`, recovered from `walkEnd_extends` at the Goldilocks tie-break.

Why: as for `walk_end_viable_of_below_recovered`: no two blocks of the viable tree of `VT` share
a root, and `goldfish_fork_choice_eq_ok_iff_walkEnd`.

Read aloud: the landed fact that the Goldfish fork choice through a viable tree extends a block
every viable head extends follows from its form over the walk predicate. -/
theorem walk_end_extends_recovered [Fintype V] [RootOrder] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.walk_end_extends V _ _ _) := by
  intro C Φ t A VT votes sv s H F' Y hRoots hVT hClosed hA hWalk hρV hYVT hY hP hQ
  letI : TieBreak V := GoldilocksCorrectness.Proofs.Routines.goldilocksTieBreak
  have hsub : viable_tree Φ VT ⊆ Φ.tree := fun B hB =>
    hVT ((GoldilocksCorrectness.Proofs.Routines.mem_viable_tree_iff Φ VT B).1 hB).1
  exact walkEnd_extends C Φ t A VT votes sv s H F' Y hClosed hA
    ((GoldilocksCorrectness.Proofs.Routines.goldfish_fork_choice_eq_ok_iff_walkEnd C Φ t A
      (viable_tree Φ VT) votes sv s
      (GoldilocksCorrectness.Proofs.Routines.rootsNameBlocksIn_mono hsub hRoots)).1 hWalk)
    hρV hYVT hY hP hQ

/-- **Lemma 58 over the walk predicate, the walk's end in the viable tree is a viable head.** When
the walk from `anchor` through the viable tree of `Φ.tree`, with the Goldfish score and the
Goldfish eligibility test, under any tie-break, ends at `H`, `H` is in the viable tree of
`Φ.tree`, and every block between two blocks of `Φ.tree` is in `Φ.tree`, then `H` is a viable
head of `Φ`.

Why: if `H` were not a viable head, the child of `H` towards a viable head that `H` is an ancestor
of would be in the viable tree and pass the eligibility test by its first case (its parent `H` is
not a viable head), while at the walk's end the test accepts no child of `H`. No hypothesis on the
roots of `Φ.tree` is needed, and the anchor is any block.

The variables:
- `C`: the parameters; `Φ`: the frame; `t`: the time;
- `votes`, `support_votes`: the votes and the support votes counted; `s`: their slot;
- `anchor`: the block the walk starts from; `H`: the walk's end.

Read aloud: whatever the tie-break, the walk through the viable tree stops at a viable head
whenever it stops inside the viable tree. -/
theorem lem58_walkEnd_is_viable_head [Fintype V] [TieBreak V] (C : Config) (Φ : Frame V)
    (t : Time) (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (anchor H : Block V)
    -- every block between two blocks of `Φ.tree` (an ancestor-or-self of the second that the
    -- first is an ancestor-or-self of) is in `Φ.tree`
    (hBetween : ∀ X ∈ Φ.tree, ∀ Y ∈ Φ.tree, ∀ Z : Block V, X.AncestorEq Z → Z.AncestorEq Y →
      Z ∈ Φ.tree)
    -- the walk from `anchor` through the viable tree of `Φ.tree` ends at `H`
    (hWalk : WalkEnd (viable_tree Φ Φ.tree) (goldfish_score Φ votes support_votes s)
      (goldfish_eligible C Φ t votes support_votes s) anchor H)
    -- `H` is in the viable tree of `Φ.tree`
    (hIn : H ∈ viable_tree Φ Φ.tree) :
    -- then `H` is a viable head of `Φ`
    H ∈ Φ.viable_heads :=
  GoldilocksCorrectness.Proofs.Routines.lem58_walkEnd_is_viable_head C Φ t votes support_votes s
    anchor H hBetween hWalk hIn

/-- The landed `lem58_walk_end_is_viable_head`, recovered from Lemma 58 over the walk predicate at
the Goldilocks tie-break, with the anchor `get_anchor A Φ t`.

Why: the head is the Goldfish fork choice from that anchor through the viable tree of `Φ.tree`
(`get_head_eq`); the viable tree is a subset of `Φ.tree`, so no two of its blocks share a root;
then `goldfish_fork_choice_eq_ok_iff_walkEnd`.

Read aloud: the landed Lemma 58 follows from Lemma 58 over the walk predicate. -/
theorem lem58_walk_end_is_viable_head_recovered [Fintype V] [RootOrder] :
    type_of% (@lem58_walk_end_is_viable_head V _ _ _) := by
  intro C A Φ t votes support_votes s H hRoots hBetween hHead hIn
  letI : TieBreak V := GoldilocksCorrectness.Proofs.Routines.goldilocksTieBreak
  have hsub : viable_tree Φ Φ.tree ⊆ Φ.tree := fun B hB =>
    ((GoldilocksCorrectness.Proofs.Routines.mem_viable_tree_iff Φ Φ.tree B).1 hB).1
  rw [GoldilocksCorrectness.Proofs.Routines.get_head_eq] at hHead
  exact lem58_walkEnd_is_viable_head C Φ t votes support_votes s (get_anchor A Φ t) H hBetween
    ((GoldilocksCorrectness.Proofs.Routines.goldfish_fork_choice_eq_ok_iff_walkEnd C Φ t
      (get_anchor A Φ t) (viable_tree Φ Φ.tree) votes support_votes s
      (GoldilocksCorrectness.Proofs.Routines.rootsNameBlocksIn_mono hsub hRoots)).1 hHead) hIn

end GoldilocksCorrectness.Statements.Routines
