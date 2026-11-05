module
public import Goldilocks.AC.Confirmation

@[expose] public section

/-!
# The vocabulary of the walk statements

The conditions the statements about the Goldfish walk, the revocation and the confirmation update
read, as definitions over the routines' own types: where a walk starts (`StartsTowards`), that the
roots of a tree name its blocks (`RootsNameBlocksIn`), and what it is for a validator to have one
vote for a block's chain in a set of votes (`VotesOnceFor`), in an AC state's pool
(`VotesOnceInPoolFor`), or one early vote for a block (`EarlyVoteOnceFor`; `EarlyVoteOnceAt` with
the cutoff a parameter, the two agreeing by `earlyVoteOnceFor_iff`).
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

open Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `StartsTowards A R tree`: `R` is `A` or an ancestor of `A`; or `A` is an ancestor of `R` and
every block after `A` up to `R`, `R` included, is in `tree`.

The variables:
- `A`: the block a walk starts from;
- `R`: the block the walk is to reach;
- `tree`: the tree walked. -/
def StartsTowards (A R : Block V) (tree : Finset (Block V)) : Prop :=
  R.AncestorEq A ∨
    (A.AncestorEq R ∧ ∀ P : Block V, A.AncestorEq P → P ≠ A → P.AncestorEq R → P ∈ tree)

/-- `RootsNameBlocksIn tree`: no two blocks of `tree` share a root.

The variables:
- `tree`: the set of blocks. -/
def RootsNameBlocksIn (tree : Finset (Block V)) : Prop :=
  ∀ B ∈ tree, ∀ B' ∈ tree, B.root = B'.root → B = B'

/-- `VotesOnceFor Φ votes support_votes s R v`: `v` has a slot-`s` vote in `support_votes` whose
head is the root of a block of `Φ.tree` that is `R` or a descendant of `R`, and that vote is `v`'s
only vote in `votes`.

The variables:
- `Φ`: the frame whose tree names the vote's head;
- `votes`: the votes counted; `support_votes`: the support votes counted;
- `s`: the slot of the vote;
- `R`: the block whose chain the vote supports;
- `v`: the validator. -/
def VotesOnceFor (Φ : Frame V) (votes support_votes : Finset (GoldfishVote V)) (s : Slot)
    (R : Block V) (v : V) : Prop :=
  ∃ vote ∈ support_votes, vote.val_index = v ∧ vote.slot = s ∧
    (∃ H ∈ Φ.tree, H.root = vote.head ∧ R.AncestorEq H) ∧
    ∀ vote' ∈ votes, vote'.val_index = v → vote' = vote

/-- `VotesOnceInPoolFor A Φ s' R v`: `v` has exactly one slot-`s'` vote in `A`'s pool; it resolves
(`A.tau` answers a time), and its head is the root of a block of `Φ.tree` that is `R` or a
descendant of `R`.

The variables:
- `A`: the AC state; `Φ`: the frame;
- `s'`: the slot of the vote;
- `R`: the block whose chain the vote supports;
- `v`: the validator. -/
def VotesOnceInPoolFor (A : ACState V) (Φ : Frame V) (s' : Slot) (R : Block V) (v : V) : Prop :=
  ∃ vote ∈ A.pool s', vote.val_index = v ∧ (∃ x : Stamp, A.tau Φ vote = .ok (some x)) ∧
    (∃ H ∈ Φ.tree, H.root = vote.head ∧ R.AncestorEq H) ∧
    ∀ vote' ∈ A.pool s', vote'.val_index = v → vote' = vote

/-- `EarlyVoteOnceAt A Φ t s' B v`: `v` has exactly one slot-`s'` vote in `A`'s pool, its head is
`B`'s root, and it resolves strictly before the time `t`. This is `EarlyVoteOnceFor` with the
cutoff a parameter.

The variables:
- `A`: the AC state; `Φ`: the frame; `t`: the cutoff;
- `s'`: the slot of the vote;
- `B`: the block the vote names;
- `v`: the validator. -/
def EarlyVoteOnceAt (A : ACState V) (Φ : Frame V) (t : Time) (s' : Slot) (B : Block V)
    (v : V) : Prop :=
  ∃ vote ∈ A.pool s', vote.val_index = v ∧ vote.head = B.root ∧
    (∃ x : Stamp, A.tau Φ vote = .ok (some x) ∧ occurrenceBefore (some x) t = true) ∧
    ∀ vote' ∈ A.pool s', vote'.val_index = v → vote' = vote

/-- `EarlyVoteOnceFor C A Φ s' B v`: `v` has exactly one slot-`s'` vote in `A`'s pool, its head is
`B`'s root, and it resolves strictly before `C.t_ s' + 2 * C.Δ`.

The variables:
- `C`: the configuration; `A`: the AC state; `Φ`: the frame;
- `s'`: the slot of the vote;
- `B`: the block the vote names;
- `v`: the validator. -/
def EarlyVoteOnceFor (C : Config) (A : ACState V) (Φ : Frame V) (s' : Slot) (B : Block V)
    (v : V) : Prop :=
  ∃ vote ∈ A.pool s', vote.val_index = v ∧ vote.head = B.root ∧
    (∃ x : Stamp, A.tau Φ vote = .ok (some x) ∧
      occurrenceBefore (some x) (C.t_ s' + 2 * C.Δ) = true) ∧
    ∀ vote' ∈ A.pool s', vote'.val_index = v → vote' = vote

omit [Fintype V] [RootOrder] in
/-- `EarlyVoteOnceFor` is `EarlyVoteOnceAt` at the cutoff `C.t_ s' + 2 · C.Δ`.

The variables:
- `C`: the configuration; `A`: the AC state; `Φ`: the frame;
- `s'`: the slot of the vote; `B`: the block the vote names; `v`: the validator.

Read aloud: `v` has one early vote for `B` exactly when it has one with the cutoff
`C.t_ s' + 2 · C.Δ`. -/
theorem earlyVoteOnceFor_iff (C : Config) (A : ACState V) (Φ : Frame V) (s' : Slot) (B : Block V)
    (v : V) : EarlyVoteOnceFor C A Φ s' B v ↔ EarlyVoteOnceAt A Φ (C.t_ s' + 2 * C.Δ) s' B v :=
  Iff.rfl

end GoldilocksCorrectness.Statements.Routines
