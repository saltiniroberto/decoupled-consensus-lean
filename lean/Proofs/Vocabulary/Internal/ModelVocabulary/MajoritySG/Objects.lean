module
public import Model.Vocabulary.Protocol.ForkChoice.Goldfish

@[expose] public section

/-!
# SG votes and vote sets

The resolution of an SG vote, its resolution time, and the tests on a round's set of SG votes that
the store handler and the majority fork choice read.
-/

namespace DecoupledConsensusModel
namespace Protocol

section Resolved

variable {V : Type} [DecidableEq V]

/-- An SG vote is resolved when the tree holds its confirmed block; a vote with an empty confirmed
    block is resolved. -/
def sg_resolved (T : Finset (Block V)) (vote : SGVote V) : Bool :=
  match vote.confirmed with
  | none => true
  | some root => (Block.find? T root).isSome

end Resolved

section Vocabulary

variable {V : Type} [DecidableEq V]

/-! ## Vote-set vocabulary -/

/-- The votes of `votes` cast by `v`. -/
def sg_votes_by (votes : Finset (SGVote V)) (v : V) : Finset (SGVote V) :=
  votes.filter (fun vote => vote.val_index = v)

/-- The resolution time of an SG vote: the later of its timestamp and its confirmed block's
    timestamp, or its own timestamp when its confirmed block is empty. -/
def sg_resolution_time (T : Finset (Block V)) (tb : TimestampMap (Block V))
    (ts : TimestampMap (SGVote V)) : TimestampMap (SGVote V) :=
  fun vote =>
    match vote.confirmed with
    | none => ts vote
    | some root =>
      match Block.find? T root with
      | none => none
      | some C => occurrenceMax (ts vote) (tb C)

/-- `votes` holds a vote by `v` resolved in `T`. -/
def holds_resolved_vote_by (T : Finset (Block V)) (votes : Finset (SGVote V))
    (v : V) : Bool :=
  decide (0 < ((sg_votes_by votes v).filter (fun u => sg_resolved T u = true)).card)

/-- `votes` holds a vote by `v`, resolved or not. -/
def holds_vote_by (votes : Finset (SGVote V)) (v : V) : Bool :=
  decide (0 < (sg_votes_by votes v).card)

/-- The unique vote by `v` in `votes`, or `none` when `v` has no vote there or more than one. -/
def sole_vote? (votes : Finset (SGVote V)) (v : V) : Option (SGVote V) :=
  pickUnique? votes (fun vote => decide (vote.val_index = v))

end Vocabulary

end Protocol
end DecoupledConsensusModel

end
