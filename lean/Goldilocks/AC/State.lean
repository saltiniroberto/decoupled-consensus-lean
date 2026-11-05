module
public import Goldilocks.Config
public import Goldilocks.Objects
public import Spec2.Defs.Notation
public import Spec2.Defs.Raise

@[expose] public section

/-!
# The AC state and the admission of a Goldfish vote

The AC state `A` is what the available chain keeps: the Goldfish votes it has admitted, slot by
slot; the time at which it admitted each vote and each block; the confirmation each slot's update
computed; the lock entries, each a block with a deadline; the blocks the latest confirmation
update locked by its fast test; and the record of the confirmed tip. Every routine that needs the
blocks the finality gadget has accepted reads them from the frame `Φ`.

This file declares, in the namespace `Goldilocks`:

- `ac_valid_payload`: whether the Goldfish votes a block includes are well placed;
- `LockEntry V`, a lock entry, and `ACState V`, the AC state, with its initial value
  `ACState.initial`;
- the readers `ACState.pool`, the votes of a slot as a set, and `ACState.tau`, the resolution time
  of a vote; `included_votes` and `included_support_votes`, the votes the blocks of a slot include;
- the lock tests `is_live`, `is_locked` and `live_lock_vetoes`;
- on a set of Goldfish votes: `votes_by` (the votes of one validator), `equivocates` (two distinct
  votes of one validator), `participates` (at least one vote), `no_second_vote_in` (no second vote
  of a vote's validator), and the sets `equivocators` and `participants` with the count
  `voters_count`;
- `on_goldfish_vote`: the admission of a Goldfish vote.

The committee of slot `s` is `P.committee s`, a field of the provisional values `P`.

This file holds definitions only.
-/

open scoped DC

open DC (DRE)

namespace Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The payload of a block -/

/-- `ac_valid_payload P B`: whether every Goldfish vote of `B.votes` has the slot `B.slot − 1`, and
every vote of `B.support_votes` is one of `B.votes`. The validator of every vote of `B.votes` is in
the committee `P.committee (B.slot − 1)`. -/
@[no_expose] def ac_valid_payload (P : Provisional V) (B : Block V) : Bool :=
  (∀ vote ∈ B.votes, vote.slot = B.slot - 1) ∧ (∀ vote ∈ B.support_votes, vote ∈ B.votes) ∧
    ∀ vote ∈ B.votes, vote.val_index ∈ P.committee (B.slot - 1)

/-! ## The AC state -/

/-- A lock entry: a block and a deadline. -/
structure LockEntry (V : Type) where
  /-- The locked block. -/
  B : Block V
  /-- The deadline: the entry is live strictly before it. -/
  d : Time
deriving DecidableEq

/-- What the available chain keeps. -/
structure ACState (V : Type) where
  /-- `gf_votes s`: the admitted Goldfish votes of slot `s`, at most two distinct votes per
  validator, in the order of admission; empty for a slot never written. -/
  gf_votes : (s : Slot) → List (GoldfishVote V)
  /-- `timestamp_vote vote`: the time at which the Goldfish vote `vote` was admitted, or `none`
  when it was not. -/
  timestamp_vote : (vote : GoldfishVote V) → Option Stamp
  /-- `timestamp_block B`: the time at which the block `B` was admitted, or `none` when it was
  not. -/
  timestamp_block : (B : Block V) → Option Stamp
  /-- `saved_confirmation s`: the confirmation the update of slot `s` computed, or `none` when it
  computed none or has not run. -/
  saved_confirmation : (s : Slot) → Option (Block V)
  /-- The lock entries. -/
  lock_entries : Finset (LockEntry V)
  /-- The blocks the latest confirmation update locked by its fast test. -/
  fast_blocks : Finset (Block V)
  /-- The record of the confirmed tip. -/
  latest_confirmed : Block V

/-- The initial AC state: no vote; the genesis block stamped `genesisStamp`, earlier than every
time, and nothing else stamped; no saved confirmation; no lock entry and no fast block; the
genesis block as the confirmed tip. -/
@[no_expose] def ACState.initial : ACState V where
  gf_votes := fun _ => []
  timestamp_vote := fun _ => none
  timestamp_block := fun B => if B = Block.genesis then some genesisStamp else none
  saved_confirmation := fun _ => none
  lock_entries := ∅
  fast_blocks := ∅
  latest_confirmed := Block.genesis

/-! ## The readers -/

/-- `A.pool s`: the admitted Goldfish votes of slot `s`, as a set. -/
@[no_expose] def ACState.pool (A : ACState V) (s : Slot) : Finset (GoldfishVote V) :=
  A.gf_votes[s].toFinset

/-- `A.tau Φ vote`: the resolution time of the Goldfish vote `vote`, read over the frame's tree
`Φ.tree` and `A`'s stamps (`resolution_time`); `none` when the vote never resolves.

Raises when `resolution_time` does: when two blocks of `Φ.tree` have the vote's head root, or when
the vote or its head block has no stamp. -/
@[no_expose] def ACState.tau (A : ACState V) (Φ : Frame V) (vote : GoldfishVote V) : DRE Occurrence :=
  resolution_time Φ.tree A.timestamp_block A.timestamp_vote vote

/-- `included_votes Φ s`: the slot-`(s − 1)` Goldfish votes included in the slot-`s` blocks of
`Φ.tree`. -/
@[no_expose] def included_votes (Φ : Frame V) (s : Slot) : Finset (GoldfishVote V) :=
  {B ∈ Φ.tree | B.slot = s}.biUnion fun B => {vote ∈ B.votes.toFinset | vote.slot = s - 1}

/-- `included_support_votes Φ s`: the slot-`(s − 1)` support votes included in the slot-`s` blocks
of `Φ.tree`. -/
@[no_expose] def included_support_votes (Φ : Frame V) (s : Slot) : Finset (GoldfishVote V) :=
  {B ∈ Φ.tree | B.slot = s}.biUnion fun B =>
    {vote ∈ B.support_votes.toFinset | vote.slot = s - 1}

/-! ## The locks -/

/-- `is_live Φ t e`: whether the lock entry `e` is live at the time `t`: `t` is strictly before
its deadline and its block is in `Φ.tree`. -/
@[no_expose] def is_live (Φ : Frame V) (t : Time) (e : LockEntry V) : Bool :=
  t < e.d && e.B ∈ Φ.tree

/-- `is_locked A Φ t B'`: whether the block `B'` is locked at the time `t`: some live entry of
`A.lock_entries` has a block of which `B'` is an ancestor, or which is `B'`. -/
@[no_expose] def is_locked (A : ACState V) (Φ : Frame V) (t : Time) (B' : Block V) : Bool :=
  ∃ e ∈ A.lock_entries, is_live Φ t e ∧ B'.ancestorEq e.B

/-- `live_lock_vetoes A Φ t C`: whether some live entry of `A.lock_entries` at the time `t` has a
block that conflicts with `C`. -/
@[no_expose] def live_lock_vetoes (A : ACState V) (Φ : Frame V) (t : Time) (C : Block V) : Bool :=
  ∃ e ∈ A.lock_entries, is_live Φ t e ∧ e.B.conflicts C

/-! ## Sets of Goldfish votes -/

/-- `votes_by votes v`: the votes of `votes` whose validator is `v`. -/
@[no_expose] def votes_by (votes : Finset (GoldfishVote V)) (v : V) : Finset (GoldfishVote V) :=
  {vote ∈ votes | vote.val_index = v}

/-- `equivocates votes v`: whether `votes` holds two distinct votes of the validator `v`. -/
@[no_expose] def equivocates (votes : Finset (GoldfishVote V)) (v : V) : Bool :=
  2 ≤ |votes_by votes v|

/-- `participates votes v`: whether `votes` holds a vote of the validator `v`. -/
@[no_expose] def participates (votes : Finset (GoldfishVote V)) (v : V) : Bool :=
  0 < |votes_by votes v|

/-- `no_second_vote_in late vote`: whether every vote of `late` is `vote` itself or a vote of
another validator than `vote`'s. -/
@[no_expose] def no_second_vote_in (late : Finset (GoldfishVote V)) (vote : GoldfishVote V) : Bool :=
  ∀ u ∈ late, u = vote ∨ u.val_index ≠ vote.val_index

/-- `equivocators votes`: the validators that hold two distinct votes in `votes`. -/
@[no_expose] def equivocators (votes : Finset (GoldfishVote V)) : Finset V :=
  {v ∈ Finset.univ | equivocates votes v}

/-- `participants votes`: the validators with a vote in `votes`. -/
@[no_expose] def participants (votes : Finset (GoldfishVote V)) : Finset V :=
  {v ∈ Finset.univ | participates votes v}

/-- `voters_count votes`: the number of validators with a vote in `votes`. -/
@[no_expose] def voters_count (votes : Finset (GoldfishVote V)) : Nat :=
  |participants votes|

/-! ## The admission of a Goldfish vote -/

/-- The AC state `A` with the Goldfish vote `vote` admitted at the time `t`, in the slot
`s := C.slot t`.

The vote is rejected, and `A` returned unchanged, when its slot is earlier than `s − 1` or later
than `s`, when its validator is not in the committee `P.committee vote.slot`, when `A` already
holds it, or when `A`'s votes of its slot already hold two distinct votes of its validator
(`equivocates`). Otherwise it is appended to `A.gf_votes[vote.slot]` and stamped with `t`. -/
@[no_expose] def on_goldfish_vote (C : Config) (P : Provisional V) (A : ACState V) (t : Time)
    (vote : GoldfishVote V) : ACState V := Id.run do
  let mut A := A
  let s := C.slot t
  if vote.slot < s - 1 || s < vote.slot || vote.val_index ∉ P.committee vote.slot ||
      vote ∈ A.gf_votes[vote.slot] then
    return A
  if equivocates (A.pool vote.slot) vote.val_index then
    return A
  A.gf_votes[vote.slot] ← A.gf_votes[vote.slot] ++ [vote]
  A.timestamp_vote[vote] ← t
  return A

end Goldilocks
