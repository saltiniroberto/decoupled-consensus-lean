module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.WalkDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.SupporterDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ProposalDefs
public import GoldilocksCorrectness.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Proofs.Routines.TickFrame

@[expose] public section

/-!
# The resolution time and the counted votes at the spec's model

At the spec's model `Model.goldilocks`, the record's definitions over a node state `n` that read
the resolution time of a Goldfish vote are the landed definitions applied to the node's AC state
`n.A` and to `fg_to_ac n.S`, when no two blocks of the tree of `fg_to_ac n.S` share a root:
`goldilocks_resolvesAt` (a vote resolves at `y` exactly when the spec's `tau` answers `y`),
`goldilocks_countedVotesAt` and `goldilocks_countedVotes` (the two sets of votes a Goldfish vote
counts), `goldilocks_votesOnceInPoolFor`, `goldilocks_earlyVoteOnceAt`,
`goldilocks_earlyVoteOnceFor`, `goldilocks_earlySupporterOf` and
`goldilocks_proposalCountedVotes`. Membership in the voter's tree reads no resolution time, and
`goldilocks_voterTreeAt` holds by definition.

The resolution time is read through the landed theorems on the spec's `tau`
(`tau_eq_ok_some`, `tau_head_of_eq_some`, `tau_eq_some_stamp`, `tau_eq_some_blockStamp`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn)
open GoldilocksCorrectness.Proofs.Routines (tau_eq_ok_some tau_head_of_eq_some tau_eq_some_stamp
  tau_eq_some_blockStamp)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- At the spec's model, a Goldfish vote resolves at `y` in the node state `n` exactly when the
spec's `tau`, read on `n.A` and `fg_to_ac n.S`, answers `y`, when no two blocks of the tree of
`fg_to_ac n.S` share a root.

The variables:
- `n`: the node state; `vote`: the vote; `y`: the stamp;
- `hRoots`: no two blocks of the tree of `fg_to_ac n.S` share a root.

Read aloud: at the spec's model, a vote resolves at `y` exactly when the spec's `tau` answers `y`,
when the roots of the tree name its blocks. -/
theorem goldilocks_resolvesAt (n : NodeState V) (vote : GoldfishVote V) (y : Stamp)
    (hRoots : RootsNameBlocksIn (fg_to_ac n.S).tree) :
    n.A.tau (fg_to_ac n.S) vote = .ok (some y) ↔
      ResolvesAt (Model.goldilocks (V := V)) n vote y := by
  constructor
  · intro h
    obtain ⟨H, hH, hr, hs⟩ := tau_head_of_eq_some hRoots h
    obtain ⟨τv, hτv, -⟩ := tau_eq_some_stamp h
    obtain ⟨τH, hτH, -⟩ := tau_eq_some_blockStamp hRoots hH hr h
    have h2 := tau_eq_ok_some (A := n.A) hRoots hH hr hs hτv hτH
    rw [h] at h2
    simp only [Except.ok.injEq, Option.some.injEq] at h2
    exact ⟨τv, τH, H, hτv, hH, hr, hs, hτH, h2⟩
  · rintro ⟨τv, τH, H, hτv, hH, hr, hs, hτH, rfl⟩
    exact tau_eq_ok_some hRoots hH hr hs hτv hτH

/-- At the spec's model, membership in the voter's tree with the view freeze `t` is the landed
`VoterTreeAt`, read on `n.A` and `fg_to_ac n.S`.

The variables:
- `n`: the node state; `t`: the view freeze; `s'`: the slot of the vote; `B`: the block.

Read aloud: at the spec's model, the record's voter's tree is the landed one. -/
theorem goldilocks_voterTreeAt (n : NodeState V) (t : Time) (s' : Slot) (B : Block V) :
    GoldilocksCorrectness.Statements.Routines.VoterTreeAt n.A (fg_to_ac n.S) t s' B ↔
      VoterTreeAt (Model.goldilocks (V := V)) n t s' B :=
  Iff.rfl

/-- At the spec's model, the two sets of votes counted with the view freeze `t` are the landed
`CountedVotesAt`, read on `n.A` and `fg_to_ac n.S`, when no two blocks of the tree of
`fg_to_ac n.S` share a root.

The variables:
- `n`: the node state; `t`: the view freeze; `s'`: the slot of the vote;
- `votes`, `support_votes`: the two sets;
- `hRoots`: no two blocks of the tree of `fg_to_ac n.S` share a root.

Read aloud: at the spec's model, the record's counted sets with a view freeze are the landed ones,
when the roots of the tree name its blocks. -/
theorem goldilocks_countedVotesAt (n : NodeState V) (t : Time) (s' : Slot)
    (votes support_votes : Finset (GoldfishVote V))
    (hRoots : RootsNameBlocksIn (fg_to_ac n.S).tree) :
    GoldilocksCorrectness.Statements.Routines.CountedVotesAt n.A (fg_to_ac n.S) t s' votes
        support_votes ↔
      CountedVotesAt (Model.goldilocks (V := V)) n t s' votes support_votes := by
  have hR := fun vote y => goldilocks_resolvesAt (V := V) n vote y hRoots
  unfold GoldilocksCorrectness.Statements.Routines.CountedVotesAt CountedVotesAt
  simp only [hR]
  exact Iff.rfl

/-- At the spec's model, the two sets of votes the Goldfish vote of slot `s'` counts are the landed
`CountedVotes`, read on `n.A` and `fg_to_ac n.S`, when no two blocks of the tree of
`fg_to_ac n.S` share a root.

The variables:
- `C`: the configuration; `n`: the node state; `s'`: the slot of the vote;
- `votes`, `support_votes`: the two sets;
- `hRoots`: no two blocks of the tree of `fg_to_ac n.S` share a root.

Read aloud: at the spec's model, the record's counted sets are the landed ones, when the roots of
the tree name its blocks. -/
theorem goldilocks_countedVotes (C : Config) (n : NodeState V) (s' : Slot)
    (votes support_votes : Finset (GoldfishVote V))
    (hRoots : RootsNameBlocksIn (fg_to_ac n.S).tree) :
    GoldilocksCorrectness.Statements.Routines.CountedVotes C n.A (fg_to_ac n.S) s' votes
        support_votes ↔
      CountedVotes (Model.goldilocks (V := V)) C n s' votes support_votes :=
  goldilocks_countedVotesAt n (C.t_ (s' - 1) + 3 * C.Δ) s' votes support_votes hRoots

/-- At the spec's model, one resolving vote of `v` for `R`'s chain among the node's slot-`s'` votes
is the landed `VotesOnceInPoolFor`, read on `n.A` and `fg_to_ac n.S`, when no two blocks of the
tree of `fg_to_ac n.S` share a root.

The variables:
- `n`: the node state; `s'`: the slot; `R`: the block; `v`: the validator;
- `hRoots`: no two blocks of the tree of `fg_to_ac n.S` share a root.

Read aloud: at the spec's model, the record's `VotesOnceInPoolFor` is the landed one, when the roots
of the tree name its blocks. -/
theorem goldilocks_votesOnceInPoolFor (n : NodeState V) (s' : Slot) (R : Block V) (v : V)
    (hRoots : RootsNameBlocksIn (fg_to_ac n.S).tree) :
    GoldilocksCorrectness.Statements.Routines.VotesOnceInPoolFor n.A (fg_to_ac n.S) s' R v ↔
      VotesOnceInPoolFor (Model.goldilocks (V := V)) n s' R v := by
  have hR := fun vote y => goldilocks_resolvesAt (V := V) n vote y hRoots
  unfold GoldilocksCorrectness.Statements.Routines.VotesOnceInPoolFor VotesOnceInPoolFor
  simp only [hR]
  exact Iff.rfl

/-- At the spec's model, one early vote of `v` for `B` among the node's slot-`s'` votes, with the
cutoff `t`, is the landed `EarlyVoteOnceAt`, read on `n.A` and `fg_to_ac n.S`, when no two blocks
of the tree of `fg_to_ac n.S` share a root.

The variables:
- `n`: the node state; `t`: the cutoff; `s'`: the slot; `B`: the block; `v`: the validator;
- `hRoots`: no two blocks of the tree of `fg_to_ac n.S` share a root.

Read aloud: at the spec's model, the record's `EarlyVoteOnceAt` is the landed one, when the roots
of the tree name its blocks. -/
theorem goldilocks_earlyVoteOnceAt (n : NodeState V) (t : Time) (s' : Slot) (B : Block V) (v : V)
    (hRoots : RootsNameBlocksIn (fg_to_ac n.S).tree) :
    GoldilocksCorrectness.Statements.Routines.EarlyVoteOnceAt n.A (fg_to_ac n.S) t s' B v ↔
      EarlyVoteOnceAt (Model.goldilocks (V := V)) n t s' B v := by
  have hR := fun vote y => goldilocks_resolvesAt (V := V) n vote y hRoots
  unfold GoldilocksCorrectness.Statements.Routines.EarlyVoteOnceAt EarlyVoteOnceAt
  simp only [hR]
  exact Iff.rfl

/-- At the spec's model, one early vote of `v` for `B` among the node's slot-`s'` votes is the
landed `EarlyVoteOnceFor`, read on `n.A` and `fg_to_ac n.S`, when no two blocks of the tree of
`fg_to_ac n.S` share a root.

The variables:
- `C`: the configuration; `n`: the node state; `s'`: the slot; `B`: the block;
  `v`: the validator;
- `hRoots`: no two blocks of the tree of `fg_to_ac n.S` share a root.

Read aloud: at the spec's model, the record's `EarlyVoteOnceFor` is the landed one, when the roots
of the tree name its blocks. -/
theorem goldilocks_earlyVoteOnceFor (C : Config) (n : NodeState V) (s' : Slot) (B : Block V)
    (v : V) (hRoots : RootsNameBlocksIn (fg_to_ac n.S).tree) :
    GoldilocksCorrectness.Statements.Routines.EarlyVoteOnceFor C n.A (fg_to_ac n.S) s' B v ↔
      EarlyVoteOnceFor (Model.goldilocks (V := V)) C n s' B v :=
  goldilocks_earlyVoteOnceAt n (C.t_ s' + 2 * C.Δ) s' B v hRoots

/-- At the spec's model, an early supporter of `B` among the node's slot-`s` votes is the landed
`EarlySupporterOf`, read on `n.A` and `fg_to_ac n.S`, when no two blocks of the tree of
`fg_to_ac n.S` share a root.

The variables:
- `C`: the configuration; `n`: the node state; `s`: the slot; `B`: the block;
  `u`: the validator;
- `hRoots`: no two blocks of the tree of `fg_to_ac n.S` share a root.

Read aloud: at the spec's model, the record's `EarlySupporterOf` is the landed one, when the roots
of the tree name its blocks. -/
theorem goldilocks_earlySupporterOf (C : Config) (n : NodeState V) (s : Slot) (B : Block V)
    (u : V) (hRoots : RootsNameBlocksIn (fg_to_ac n.S).tree) :
    GoldilocksCorrectness.Statements.Routines.EarlySupporterOf C n.A (fg_to_ac n.S) s B u ↔
      EarlySupporterOf (Model.goldilocks (V := V)) C n s B u := by
  have hR := fun vote y => goldilocks_resolvesAt (V := V) n vote y hRoots
  unfold GoldilocksCorrectness.Statements.Routines.EarlySupporterOf EarlySupporterOf
  simp only [hR]
  exact Iff.rfl

/-- At the spec's model, the two sets of votes the proposal counts are the landed
`ProposalCountedVotes`, read on `n.A` and `fg_to_ac n.S`, when no two blocks of the tree of
`fg_to_ac n.S` share a root.

The variables:
- `n`: the node state; `s`: the slot; `votes`, `support_votes`: the two sets;
- `hRoots`: no two blocks of the tree of `fg_to_ac n.S` share a root.

Read aloud: at the spec's model, the record's `ProposalCountedVotes` is the landed one, when the
roots of the tree name its blocks. -/
theorem goldilocks_proposalCountedVotes (n : NodeState V) (s : Slot)
    (votes support_votes : Finset (GoldfishVote V))
    (hRoots : RootsNameBlocksIn (fg_to_ac n.S).tree) :
    GoldilocksCorrectness.Statements.Routines.ProposalCountedVotes n.A (fg_to_ac n.S) s votes
        support_votes ↔
      ProposalCountedVotes (Model.goldilocks (V := V)) n s votes support_votes := by
  have hR := fun vote y => goldilocks_resolvesAt (V := V) n vote y hRoots
  unfold GoldilocksCorrectness.Statements.Routines.ProposalCountedVotes ProposalCountedVotes
  simp only [hR]
  exact Iff.rfl

end GoldilocksCorrectness.Record.Statements.Routines
