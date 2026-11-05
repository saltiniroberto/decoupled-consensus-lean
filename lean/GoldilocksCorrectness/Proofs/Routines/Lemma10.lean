module
public import GoldilocksCorrectness.Proofs.Routines.Lemma1
public import GoldilocksCorrectness.Proofs.Routines.Lemma9

@[expose] public section

/-!
# Lemma 10: the walk ends at the proposal when a majority votes for a shared block

The proof of `lem10_walk_ends_at_proposal_of_majority`, stated in
`GoldilocksCorrectness/Statements/Routines/WalkStatements.lean`.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

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
    H_w = P := by
  -- the first walk passes `X`
  have hXP : X.AncestorEq P.parent :=
    lem1_walk_extends_majority_block Φ votes support_votes s eligible_p N A_p X P.parent tree_p
      Sup (Or.inr ⟨hApX, hPathP⟩) hRoots hSupport hSup hVoters hThreshold
      (fun D => ⟨b_p D, hTestP D⟩)
      (fun D h₁ h₂ h₃ n hn hlt => by rw [hTestP D, hTrueP D h₁ h₂ h₃ n hn hlt])
      hWalkP
  -- the second walk passes `X`
  have hXW : X.AncestorEq H_w :=
    lem1_walk_extends_majority_block Φ votes support_votes s eligible_w N A_w X H_w tree_w
      Sup (Or.inr ⟨hAwX, hPathW⟩) hRoots hSupport hSup hVoters hThreshold
      (fun D => ⟨b_w D, hTestW D⟩)
      (fun D h₁ h₂ h₃ n hn hlt => by rw [hTestW D, hTrueW D h₁ h₂ h₃ n hn hlt])
      hWalkW
  exact lem9_walk_ends_at_proposal_of_shared_block
    (fun D => (equivocators votes).card + (supportersOf Φ votes support_votes s D).card) b_p b_w
    (fun _ _ _ D _ => goldfish_score_eq_ok hRoots votes support_votes s D)
    (fun _ _ _ D _ => goldfish_score_eq_ok hRoots votes support_votes s D) hTestP hTestW hRootsP
    hPpar hWalkP hWalkW ⟨hApX, hXP⟩ hAwX hXW hPathInTreeW hPInTree hPTest hNoChildP hPathTest
    hEligSub

end GoldilocksCorrectness.Proofs.Routines
