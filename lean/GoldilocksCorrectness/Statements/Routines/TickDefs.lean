module
public import Goldilocks.AC.Confirmation
public import Goldilocks.Node

@[expose] public section

/-!
# The vocabulary of the tick statements

The definitions the statements about the node's tick read (`TickStatements.lean`):

- `expireLocks A t`, the AC state the tick of the available chain (`ac_on_tick`) writes first:
  `A` with every lock entry whose deadline is at most `t` deleted;
- `CountedVotes C A Φ s' votes support_votes`, the sets of votes the Goldfish vote of slot `s'`
  counts, written as membership conditions on `A`'s pool, `A`'s stamps and resolution times, and
  the votes included in the slot-`s'` blocks of `Φ.tree`; `CountedVotesAt` is the same with the
  view freeze a parameter, the two agreeing by `countedVotes_iff`;
- `VoterTreeAt A Φ t s' B`, membership in the voter's tree of slot `s'` with the view freeze a
  parameter.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

open Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `expireLocks A t`: the AC state `A` with every lock entry whose deadline is at most `t`
deleted, the other fields unchanged. It is the first write of the tick of the available chain at
the time `t` (`ac_on_tick`, step 1).

The variables:
- `A`: the AC state; `t`: the time of the tick.

Read aloud: `A` with every lock entry whose deadline is at most `t` deleted. -/
def expireLocks (A : ACState V) (t : Time) : ACState V :=
  { A with lock_entries := {e ∈ A.lock_entries | t < e.d} }

/-- `CountedVotesAt A Φ t s' votes support_votes`: `votes` and `support_votes` are the two sets
of votes the Goldfish vote of slot `s'` counts with the view freeze the time `t`. A vote is in
`votes` exactly when it is a vote of `A.pool (s' - 1)` stamped strictly before `t`, or a vote
included in a slot-`s'` block of `Φ.tree` (`included_votes`). A vote is in `support_votes` exactly
when it is a vote of `A.pool (s' - 1)` stamped strictly before `t` whose resolution time
(`A.tau`) is strictly before `t`, or a support vote included in a slot-`s'` block of `Φ.tree`
(`included_support_votes`) whose head is resolved in `Φ.tree` (`resolved`). This is
`CountedVotes` with the view freeze a parameter.

The variables:
- `A`: the AC state; `Φ`: the frame; `t`: the view freeze;
- `s'`: the slot of the vote; `votes`, `support_votes`: the two sets.

Read aloud: a vote is counted exactly when it is a slot-`(s' − 1)` pool vote stamped strictly
before `t`, or a vote included in a slot-`s'` block of the frame's tree; it is a support vote
exactly when it is a counted pool vote that also resolves strictly before `t`, or an included
support vote whose head is resolved in the frame's tree. -/
def CountedVotesAt (A : ACState V) (Φ : Frame V) (t : Time) (s' : Slot)
    (votes support_votes : Finset (GoldfishVote V)) : Prop :=
  (∀ vote : GoldfishVote V, vote ∈ votes ↔
      (vote ∈ A.pool (s' - 1) ∧ ∃ τ : Stamp, A.timestamp_vote vote = some τ ∧ τ < (t : Stamp)) ∨
      vote ∈ included_votes Φ s') ∧
  (∀ vote : GoldfishVote V, vote ∈ support_votes ↔
      (vote ∈ A.pool (s' - 1) ∧
        (∃ τ : Stamp, A.timestamp_vote vote = some τ ∧ τ < (t : Stamp)) ∧
        ∃ y : Stamp, A.tau Φ vote = .ok (some y) ∧ y < (t : Stamp)) ∨
      (vote ∈ included_support_votes Φ s' ∧ resolved Φ.tree vote = .ok true))

/-- `CountedVotes C A Φ s' votes support_votes`: `votes` and `support_votes` are the two sets of
votes the Goldfish vote of slot `s'` counts, read off the AC state `A` and the frame `Φ`. Write
`freeze` for the view freeze of slot `s' − 1`, `C.t_ (s' - 1) + 3 * C.Δ`. A vote is in `votes`
exactly when it is a vote of `A.pool (s' - 1)` stamped strictly before `freeze`, or a vote
included in a slot-`s'` block of `Φ.tree` (`included_votes`). A vote is in `support_votes` exactly
when it is a vote of `A.pool (s' - 1)` stamped strictly before `freeze` whose resolution time
(`A.tau`) is strictly before `freeze`, or a support vote included in a slot-`s'` block of
`Φ.tree` (`included_support_votes`) whose head is resolved in `Φ.tree` (`resolved`). At `s' = 0`
the slot `s' − 1` reads as slot `0`.

The variables:
- `C`: the configuration; `A`: the AC state; `Φ`: the frame;
- `s'`: the slot of the vote; `votes`, `support_votes`: the two sets.

Read aloud: a vote is counted exactly when it is a slot-`(s' − 1)` pool vote stamped strictly
before the freeze, or a vote included in a slot-`s'` block of the frame's tree; it is a support
vote exactly when it is a counted pool vote that also resolves strictly before the freeze, or an
included support vote whose head is resolved in the frame's tree. -/
def CountedVotes (C : Config) (A : ACState V) (Φ : Frame V) (s' : Slot)
    (votes support_votes : Finset (GoldfishVote V)) : Prop :=
  (∀ vote : GoldfishVote V, vote ∈ votes ↔
      (vote ∈ A.pool (s' - 1) ∧ ∃ τ : Stamp, A.timestamp_vote vote = some τ ∧
        τ < ((C.t_ (s' - 1) + 3 * C.Δ : Time) : Stamp)) ∨
      vote ∈ included_votes Φ s') ∧
  (∀ vote : GoldfishVote V, vote ∈ support_votes ↔
      (vote ∈ A.pool (s' - 1) ∧
        (∃ τ : Stamp, A.timestamp_vote vote = some τ ∧
          τ < ((C.t_ (s' - 1) + 3 * C.Δ : Time) : Stamp)) ∧
        ∃ y : Stamp, A.tau Φ vote = .ok (some y) ∧
          y < ((C.t_ (s' - 1) + 3 * C.Δ : Time) : Stamp)) ∨
      (vote ∈ included_support_votes Φ s' ∧ resolved Φ.tree vote = .ok true))

omit [Fintype V] [RootOrder] in
/-- `CountedVotes` is `CountedVotesAt` at the view freeze `C.t_ (s' − 1) + 3 · C.Δ`.

The variables:
- `C`: the configuration; `A`: the AC state; `Φ`: the frame;
- `s'`: the slot of the vote; `votes`, `support_votes`: the two sets.

Read aloud: the two sets are the ones the Goldfish vote of slot `s'` counts exactly when they are
the ones counted with the view freeze `C.t_ (s' − 1) + 3 · C.Δ`. -/
theorem countedVotes_iff (C : Config) (A : ACState V) (Φ : Frame V) (s' : Slot)
    (votes support_votes : Finset (GoldfishVote V)) :
    CountedVotes C A Φ s' votes support_votes ↔
      CountedVotesAt A Φ (C.t_ (s' - 1) + 3 * C.Δ) s' votes support_votes :=
  Iff.rfl

/-- `VoterTreeAt A Φ t s' B`: `B` is a block of `Φ.tree` with a stamp in `A`, and the stamp is
strictly before the time `t`, or `B` is a slot-`s'` block of `Φ.tree` or an ancestor of one. It is
membership in the voter's tree of slot `s'` (`voter_block_tree`) with the view freeze a parameter.

The variables:
- `A`: the AC state; `Φ`: the frame; `t`: the view freeze; `s'`: the slot of the vote;
- `B`: the block.

Read aloud: `B` is a stamped block of the frame's tree that is early (stamped strictly before `t`)
or leads to a slot-`s'` block. -/
def VoterTreeAt (A : ACState V) (Φ : Frame V) (t : Time) (s' : Slot) (B : Block V) : Prop :=
  B ∈ Φ.tree ∧ ∃ τ : Stamp, A.timestamp_block B = some τ ∧
    (τ < (t : Stamp) ∨ ∃ B' ∈ Φ.tree, B'.slot = s' ∧ B.AncestorEq B')

end GoldilocksCorrectness.Statements.Routines
