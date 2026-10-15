module
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.Ring
public import Model.Vocabulary.Objects.Time
public import Model.Vocabulary.Objects.Identifiers
public import Model.Vocabulary.Objects.Parameters
public import Model.Vocabulary.Objects.Blocks
public import Model.Vocabulary.Objects.Weights

@[expose] public section

/-!
# Slot schedule and nodes

The per-slot times, the fixed data of a node, the vote-set tests `votes_by`, `equivocates` and
`participates`, and the wire constraints on votes and blocks.
-/

namespace DecoupledConsensusModel
namespace Protocol

/-- The fixed data of a node: its validator, the root of the block it proposes in each slot, and
    whether it attests in each round. -/
structure Node (V : Type) where
  /-- The validator running the node. -/
  val_index : V
  /-- The nominal root of the block this node proposes in a given slot. -/
  new_root : Slot → BlockId
  /-- Whether the node performs the attestation duty of each round; the other duties run regardless. -/
  awake : Round → Bool

section Vocabulary

variable {V : Type} [DecidableEq V]

/-! ## Vote-set vocabulary -/

/-- The votes of `votes` cast by `v`. -/
def votes_by (votes : Finset (GoldfishVote V)) (v : V) : Finset (GoldfishVote V) :=
  votes.filter (fun vote => vote.val_index = v)

/-- `v` equivocates in `votes`: they hold at least two distinct votes of `v`, of any slots. -/
def equivocates (votes : Finset (GoldfishVote V)) (v : V) : Bool :=
  decide (2 ≤ (votes_by votes v).card)

/-- `v` participates in `votes`: they hold at least one vote of `v`. -/
def participates (votes : Finset (GoldfishVote V)) (v : V) : Bool :=
  decide (0 < (votes_by votes v).card)

end Vocabulary

section Schedule

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `t_s`, the proposal time of slot `s`. -/
def proposal_time (E : Env V) (s : Slot) : Time :=
  E.t s

/-- `t_s + Δ`, the Goldfish vote time of slot `s`. -/
def vote_time (E : Env V) (s : Slot) : Time :=
  E.t s + E.Δ

/-- `t_s + 2Δ`, the support cutoff of slot `s`. -/
def support_cutoff (E : Env V) (s : Slot) : Time :=
  E.t s + 2 * E.Δ

/-- `t_s + 3Δ`, the view freeze of slot `s`. -/
def view_freeze (E : Env V) (s : Slot) : Time :=
  E.t s + 3 * E.Δ

/-- `t_s + 6Δ`, the confirmation time of slot `s`. -/
def confirmation_time (E : Env V) (s : Slot) : Time :=
  E.t s + 6 * E.Δ

/-- A Goldfish vote is well formed when its voter is in its slot's committee. -/
def vote_well_formed (E : Env V) (vote : GoldfishVote V) : Bool :=
  decide (vote.val_index ∈ E.committee vote.slot)

end Schedule

/-- Every Goldfish vote a block includes is of the slot before the block's:
    `vote.slot + 1 = B.slot`. -/
def carried_votes_well_formed {V : Type} (B : Block V) : Bool :=
  B.gf_votes.all (fun vote => decide (vote.slot + 1 = B.slot))

/-- Every support vote of a block is among the Goldfish votes it includes. -/
def carried_support_well_formed {V : Type} [DecidableEq V] (B : Block V) : Bool :=
  B.gf_support_votes.all (fun vote => decide (vote ∈ B.gf_votes))

end Protocol
end DecoupledConsensusModel

end
