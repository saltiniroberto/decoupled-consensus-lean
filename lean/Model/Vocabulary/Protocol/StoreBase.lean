module
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Lattice.Fold
public import Model.Vocabulary.Protocol.Schedule

@[expose] public section

/-!
# The Goldfish store

The Goldfish store, the base of the store layers, with vote resolution and the resolution time `τ`.
-/

namespace DecoupledConsensusModel
namespace Protocol

/-- The Goldfish store `Σ = (t, s, T, timestamp[·], gf_votes[·], live_confirmed, latest_confirmed)`. -/
structure GoldfishStore (V : Type) where
  /-- `Σ.t`: the current time. -/
  t : Time
  /-- `Σ.s`: the current slot. -/
  s : Slot
  /-- `Σ.T`: the tree of processed blocks. -/
  T : Finset (Block V)
  /-- Receipt times of blocks. -/
  timestamp_block : TimestampMap (Block V)
  /-- Receipt times of Goldfish votes. -/
  timestamp_vote : TimestampMap (GoldfishVote V)
  /-- `Σ.gf_votes[k]`: the processed slot-`k` votes. -/
  gf_votes : Slot → List (GoldfishVote V)
  /-- `Σ.live_confirmed`: the block the last evaluated slot confirmed. -/
  live_confirmed : Block V
  /-- `Σ.latest_confirmed`: the confirmation record the node exposes. -/
  latest_confirmed : Block V

section Resolution

variable {V : Type} [DecidableEq V]

/-! ## Resolution -/

/-- Whether `vote` resolves in `T`: its root names a unique block of `T` whose slot is at most the
    vote's slot. -/
def resolved (T : Finset (Block V)) (vote : GoldfishVote V) : Bool :=
  match Block.find? T vote.head with
  | some B => decide (B.slot ≤ vote.slot)
  | none => false

/-- The resolution time `τ(vote) = max{timestamp(vote), timestamp(H)}` of a vote naming `H`, `+∞`
    while `H` is missing. -/
def resolution_time (T : Finset (Block V)) (tb : TimestampMap (Block V))
    (tv : TimestampMap (GoldfishVote V)) : TimestampMap (GoldfishVote V) :=
  fun vote =>
    match Block.find? T vote.head with
    | none => none
    | some H => if H.slot ≤ vote.slot then occurrenceMax (tv vote) (tb H) else none

end Resolution

namespace GoldfishStore

variable {V : Type} [DecidableEq V]

/-- The slot-`k` votes as a set. -/
def pool (st : GoldfishStore V) (k : Slot) : Finset (GoldfishVote V) :=
  (st.gf_votes k).toFinset

/-- `τ(·)` of the store. -/
def tau (st : GoldfishStore V) : TimestampMap (GoldfishVote V) :=
  resolution_time st.T st.timestamp_block st.timestamp_vote

end GoldfishStore

end Protocol
end DecoupledConsensusModel

end
