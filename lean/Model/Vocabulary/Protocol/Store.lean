module
public import Model.Vocabulary.Protocol.Duties.Inputs

@[expose] public section

/-!
# The node store

The store `Σ` with its fields, the SG vote of an attestation, the vote reads, and the projection
`toHealing` through which the grade and fork-choice layers read the store.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (ChainState)
open Protocol (SGVote)

/-- The SG vote of a combined attestation: its `(validator, round, confirmed)` projection. -/
def sgVote {V : Type} (a : CombinedAttestation V) : SGVote V :=
  ⟨a.val_index, a.round, a.confirmed⟩

/-- The node store `Σ`. -/
structure Store (V : Type) where
  /-- `Σ.t`: the current time. -/
  t : Time
  /-- `Σ.s`: the current slot. -/
  s : Slot
  /-- `Σ.T`: the processed block tree. -/
  T : Finset (Block V)
  /-- Receipt times of blocks. -/
  timestamp_block : TimestampMap (Block V)
  /-- Receipt times of Goldfish votes. -/
  timestamp_vote : TimestampMap (GoldfishVote V)
  /-- Receipt times of attestations, keyed by their SG vote. -/
  timestamp_sg_vote : TimestampMap (SGVote V)
  /-- `Σ.σ[B]`: the chain state after `B`, with `ChainState.initial` as the default. -/
  σ : Block V → ChainState V
  /-- `Σ.gf_votes[k]`: the processed slot-`k` Goldfish votes. -/
  gf_votes : Slot → List (GoldfishVote V)
  /-- `Σ.sg_votes[r]`: the processed round-`r` combined attestations. -/
  sg_votes : Round → List (CombinedAttestation V)
  /-- `Σ.F`: the finalized block. -/
  F : Block V
  /-- `Σ.J`: the justified block. -/
  J : Block V
  /-- `Σ.h_j`: the height of `Σ.J`. -/
  h_j : Height
  /-- `Σ.h_max`: the running maximum chain-state height. -/
  h_max : Height
  /-- The confirmation used by voting: the confirmation walk's result when it passes the majority
      test, `get_fg_root` otherwise. -/
  live_confirmed : Block V
  /-- The client-facing confirmation record. -/
  latest_confirmed : Block V
  /-- The client-facing stable record. -/
  latest_stable : Block V

namespace Store

variable {V : Type} [DecidableEq V]

/-- The initial store: time and slot `0`, the tree holding only genesis, stamped `−∞`, `h_max = 1`,
    `h_j = 0`, the block fields at genesis, and no votes. -/
def init : Store V where
  t := 0
  s := 0
  T := {Block.genesis}
  timestamp_block := fun B => if B = Block.genesis then some genesisStamp else none
  timestamp_vote := fun _ => none
  timestamp_sg_vote := fun _ => none
  σ := fun _ => ChainState.initial
  gf_votes := fun _ => []
  sg_votes := fun _ => []
  F := Block.genesis
  J := Block.genesis
  h_j := 0
  h_max := 1
  live_confirmed := Block.genesis
  latest_confirmed := Block.genesis
  latest_stable := Block.genesis

/-- The slot-`k` Goldfish votes as a set. -/
def pool (st : Store V) (k : Slot) : Finset (GoldfishVote V) :=
  (st.gf_votes k).toFinset

/-- The round-`r` attestations as a set. -/
def sg_pool (st : Store V) (r : Round) : Finset (CombinedAttestation V) :=
  (st.sg_votes r).toFinset

/-- `τ(·)`, the resolution time of the store's Goldfish votes. -/
def tau (st : Store V) : TimestampMap (GoldfishVote V) :=
  Protocol.resolution_time st.T st.timestamp_block st.timestamp_vote

/-- The store read as a healing store, each stored attestation read as its SG vote. -/
def toHealing (st : Store V) : Protocol.HealingStore V where
  t := st.t
  s := st.s
  T := st.T
  timestamp_block := st.timestamp_block
  timestamp_vote := st.timestamp_vote
  gf_votes := st.gf_votes
  live_confirmed := st.live_confirmed
  latest_confirmed := st.latest_confirmed
  sg_votes := fun r => (st.sg_pool r).image sgVote
  timestamp_sg_vote := st.timestamp_sg_vote
  σ := st.σ
  F := st.F
  J := st.J
  h_j := st.h_j
  h_max := st.h_max

end Store

end Protocol
end DecoupledConsensusModel

end
