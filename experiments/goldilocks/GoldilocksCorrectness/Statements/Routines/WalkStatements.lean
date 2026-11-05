module
public import GoldilocksCorrectness.Proofs.Routines.Lemma1
public import GoldilocksCorrectness.Proofs.Routines.Lemma2
public import GoldilocksCorrectness.Proofs.Routines.Lemma3
public import GoldilocksCorrectness.Proofs.Routines.Lemma4
public import GoldilocksCorrectness.Proofs.Routines.Lemma9
public import GoldilocksCorrectness.Proofs.Routines.Lemma10

@[expose] public section

/-!
# The statements about the Goldfish walk

The audited statements about the walk `ghost` and the Goldfish fork choice from an arbitrary start,
each proved in its own file under `GoldilocksCorrectness/Proofs/Routines/`.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

open Goldilocks

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
    R.AncestorEq H :=
  GoldilocksCorrectness.Proofs.Routines.lem1_walk_extends_majority_block Φ votes support_votes s
    eligible N A R H tree Sup hStart hRoots hSupport hSup hVoters hThreshold hEligibleAnswers
    hEligibleTrue hWalk

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
  GoldilocksCorrectness.Proofs.Routines.lem2_goldfish_fork_choice_extends_majority_block C Φ t
    votes support_votes s A R H tree Sup hStart hRoots hSupport hSup hVoters hWalk

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
    R.AncestorEq H :=
  GoldilocksCorrectness.Proofs.Routines.lem3_goldfish_fork_choice_extends_committee_majority_block
    C P Φ t votes support_votes s A R H tree Hs hStart hRoots hSupport hHs hCommittee hMajority
    hWalk

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
    H = R :=
  GoldilocksCorrectness.Proofs.Routines.lem4_walk_ends_at_unanimous_block Φ votes support_votes s N
    A R H tree Sup hAR hPath hRoots hSupport hSup hR hVotersLe hThreshold hWalk

omit [Fintype V] in
/-- **Lemma 9, the walk ends at the proposal of a shared block.** Two walks: the first, from `A_p`
over `tree_p`, ends at `P`'s parent; the second, from `A_w` over `tree_w`, ends at `H_w`. If the
two scores answer the same number on every child of a block from `X` to `P`'s parent, the first
walk passes `X`, the second starts at `X` or an ancestor of `X` and passes `X`, the blocks of the
first walk after `X` and `P` are in `tree_w`, `P` is eligible in the second walk and has no child
in `tree_w`, the second test accepts every block after `X` up to `P`'s parent, and every child in
`tree_w` of a block from `X` to `P`'s parent, other than `P`, that the second test accepts is in
`tree_p` and accepted by the first test, then the second walk ends at `P`.

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
theorem lem9_walk_ends_at_proposal_of_shared_block {A_p A_w X P H_w : Block V}
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
    H_w = P :=
  GoldilocksCorrectness.Proofs.Routines.lem9_walk_ends_at_proposal_of_shared_block n b_p b_w
    hScoreP hScoreW hTestP hTestW hRootsP hPpar hWalkP hWalkW hXOnWalkP hRootWX hXW hPathInTreeW
    hPInTree hPTest hNoChildP hPathTest hEligSub

/-- **Lemma 10, the walk ends at the proposal when a majority votes for a shared block.** Two
walks score the same slot-`s` votes with `goldfish_score`: the first, from `A_p` over `tree_p`,
ends at `P`'s parent; the second, from `A_w` over `tree_w`, ends at `H_w`. The second ends at
`P`, when each member of a set `Sup` has one vote and it supports `X`'s chain, the voters are
fewer than twice `Sup`, both tests answer on every block, each test accepts every block after its
walk's start up to `X` whose score `n` has `N < 2n`, with `N` less than twice `Sup`, both walks
start at `X` or an ancestor of `X` with every block after their start up to `X` in their tree,
and the conditions of Lemma 9 hold from `X`
on: the blocks after `X` up to `P`'s parent and `P` are in `tree_w`, the second test accepts `P`,
no block of `tree_w` is a child of `P`, the second test accepts every block after `X` up to `P`'s
parent, and every child in `tree_w` of a block from `X` to `P`'s parent, other than `P`, that the
second test accepts is in `tree_p` and accepted by the first test.

Why: Lemma 1 at each walk gives that it passes `X`: `X` is an ancestor of `P`'s parent, or that
parent, and of `H_w`, or `H_w`. Then Lemma 9, with the scores' answers of `goldfish_score_eq_ok`.

  `A_w`) up to `X`, the only blocks Lemma 1 reads them on.

The variables:
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes both scores count;
- `s`: the slot of the votes; `eligible_p`, `eligible_w`: the two tests; `N`: their threshold;
- `A_p`, `A_w`: the starts of the two walks; `X`: the block both pass; `P`: the block after the
  first walk's end; `H_w`: where the second walk ends; `tree_p`, `tree_w`: the two trees;
- `Sup`: the validators voting for `X`'s chain; `b_p`, `b_w`: the two tests' answers. -/
theorem lem10_walk_ends_at_proposal_of_majority (Φ : Frame V)
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
    -- no two blocks of `tree_p` share a root
    (hRootsP : RootsNameBlocksIn tree_p)
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
    (hWalkP : ghost A_p tree_p (goldfish_score Φ votes support_votes s) eligible_p = .ok P.parent)
    -- the second walk ends at `H_w`
    (hWalkW : ghost A_w tree_w (goldfish_score Φ votes support_votes s) eligible_w = .ok H_w)
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
  GoldilocksCorrectness.Proofs.Routines.lem10_walk_ends_at_proposal_of_majority Φ votes
    support_votes s eligible_p eligible_w N A_p A_w X P H_w tree_p tree_w Sup b_p b_w hRoots
    hSupport hSup hVoters hThreshold hTestP hTestW hTrueP hTrueW hRootsP hPpar hApX hPathP hAwX
    hPathW hWalkP hWalkW hPathInTreeW hPInTree hPTest hNoChildP hPathTest hEligSub

end GoldilocksCorrectness.Statements.Routines
