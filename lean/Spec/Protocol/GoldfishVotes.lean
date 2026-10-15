import Spec.Protocol.ForkChoice.Views
import Spec.Protocol.ForkChoice.Head
import Spec.Protocol.Grades
import Spec.Broadcast
import Spec.Defs.Notation

/-!
# The Goldfish votes, over the flat store

This file is about one kind of object: the Goldfish vote. It holds the vote's admission into the
store, the duty that sends a vote, and the confirmation duty that reads the votes the store holds.
What a node does on receiving a vote, `receive_goldfish_vote`, is in
`lean/Spec/Node.lean`, with every other routine the wiring calls. The routines here read the
flat store `Store V` of `lean/Spec/Store.lean`, and sit in the namespace
`Spec.Protocol`.

The admission:

- `on_goldfish_vote`, `on_goldfish_vote_checked`: accept a Goldfish vote, the second only from a
  member of the vote's slot committee.

The sending duty:

- `voter_filtered_block_tree`, `goldfish_vote`: the tree the voter walks in, and the Goldfish
  vote duty.

The confirmation duty:

- `update_confirmation`: the confirmation duty.

`goldfish_vote` runs in the monad `DREB` of `lean/Spec/Broadcast.lean`: it broadcasts
the vote it sends and returns what it changes.

The confirmation duty calls two functions on blocks, declared here before it:
`advance_confirmed`, which moves a record to a candidate block, and `floor_on_stable`, which
keeps the confirmation record a descendant of the stable record, or the stable record itself.

**Arguments.** `on_goldfish_vote_checked` and `goldfish_vote` take the values
`P : Provisional V`, for the committees. The two duties and `voter_filtered_block_tree` take the
parameters `C : Config` of `lean/Spec/Config.lean`.

**Raising.** `on_goldfish_vote` and `on_goldfish_vote_checked` are total.
`update_confirmation`, `voter_filtered_block_tree` and `goldfish_vote` raise when a vote or a
block they read has no stamp, when two blocks of the store's tree share a root, or when a grade
result they read is pending; each docstring says which. They call `beforeCutoff` and
`occurrenceBefore` of `lean/Spec/Objects.lean`, and `equivocates`, `no_second_vote_in`,
the count of voters `raw_voters_count`, the Goldfish score `raw_goldfish_score` and the walk
`ghost` of `lean/Spec/Protocol/ForkChoice/Goldfish.lean`.

This file holds definitions only.
-/

open scoped DC

open DC (DRE)

namespace Spec.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable (C : Config) (P : Provisional V)

/-! ## The admission -/

/-- Admit the Goldfish vote `vote` into the store `st`.

The vote is rejected, and `st` returned unchanged, when its slot `vote.slot` is earlier than
`st.s − 1` or later than the store's slot `st.s`, when the store already holds it, or when the
store's slot-`vote.slot` votes `st.pool vote.slot` already show the vote's sender `vote.val_index`
voting twice (`equivocates`). Otherwise the vote is appended to the store's slot-`vote.slot` votes
and stamped with the store's time `st.t`. A rejected vote is never stamped. -/
def on_goldfish_vote (st : Store V) (vote : GoldfishVote V) : Store V := Id.run do
  let mut st := st
  if vote.slot < st.s - 1 || st.s < vote.slot || vote ∈ st.gf_votes[vote.slot] then
    return st
  if equivocates (st.pool vote.slot) vote.val_index then
    return st
  st.gf_votes[vote.slot] ← st.gf_votes[vote.slot] ++ [vote]
  st.timestamp_vote[vote] ← st.t
  return st

/-- Admit the Goldfish vote `vote` into the store `st` with `on_goldfish_vote`, when its sender
`vote.val_index` is in the committee of the vote's slot; otherwise return `st` unchanged. -/
def on_goldfish_vote_checked (st : Store V) (vote : GoldfishVote V) : Store V := Id.run do
  if vote.val_index ∉ P.committee vote.slot then
    return st
  return on_goldfish_vote st vote

/-! ## The Goldfish vote duty -/

/-- The block tree the slot-`s` voter walks in: the voter's processed-block view
`voter_processed_block_tree` of the store `st`, filtered by `get_filtered_block_tree_from`
inside that view. The viability test and the fork-choice root filter are computed with every
witness taken from the view, so a block outside the view never makes a block of the view
viable.

Raises when `voter_processed_block_tree` does: when a block of the store's tree has no stamp. -/
def voter_filtered_block_tree (st : Store V) (s : Slot) : DRE (Finset (Block V)) := do
  let blocks ← voter_processed_block_tree C st s
  return get_filtered_block_tree_from st blocks

/-- The Goldfish vote duty of the validator `v` at the store `st`, in the store's slot `s`.

The head `H` is the block `get_head_in_tree_with_layer` returns from the voter's view
`voter_view` of the votes, its support view `voter_support_view`, and the block tree
`voter_filtered_block_tree` the voter walks in, for slot `s − 1`. If `v` is in the slot-`s`
committee, its vote for `H`'s root is broadcast (`broadcast`, `lean/Spec/Broadcast.lean`),
and the store is returned with the vote admitted by `on_goldfish_vote_checked`; otherwise nothing
is broadcast and the store is returned unchanged. The saved grades `st.saved_grades` are not
written.

Raises when one of the four reads does: when a vote of `st.pool (s − 1)` or a block of
`st.T` has no stamp, when two blocks of `st.T` share a root, or when the `g1` result of the
store's round is pending. -/
def goldfish_vote (v : V) (st : Store V) : DREB V (Store V) := do
  let s := st.s
  let votes ← voter_view C st s
  let support_votes ← voter_support_view C st s
  let tree ← voter_filtered_block_tree C st s
  let H ← get_head_in_tree_with_layer C st tree votes support_votes (s - 1)
  if v ∈ P.committee s then
    let vote := GoldfishVote.mk (val_index := v) (slot := s) (head := H.root)
    broadcast (NamedObject.gfVote vote)
    return on_goldfish_vote_checked P st vote
  return st

/-! ## The Goldfish confirmation -/

/-- The record `old` moved to the block `candidate`: `old` when `candidate` is an ancestor of
`old` (or `old` itself), and `candidate` otherwise, including when the two are not compatible. -/
def advance_confirmed (old candidate : Block V) : Block V := Id.run do
  if candidate.ancestorEq old then
    return old
  return candidate

/-- The confirmation record that follows the stable record `stable`, from the candidate
`candidate` and the record `old` as it was: `candidate` when `stable` is an ancestor of it (or it
itself); otherwise `old` when `stable` is an ancestor of `old` (or `old` itself); otherwise
`stable`. In each case `stable` is an ancestor of the result, or the result itself. -/
def floor_on_stable (stable candidate old : Block V) : Block V := Id.run do
  if stable.ancestorEq candidate then
    return candidate
  if stable.ancestorEq old then
    return old
  return stable

/-- The confirmation duty for slot `s` at the store `st`.

The reads, all of the store as it is when the duty starts:

- `early_votes`: the slot-`s` Goldfish votes whose resolution time `st.tau` is before the
  Goldfish confirmation time of slot `s`; `late_votes`: those whose stamp is before the
  confirmation time of slot `s`;
- `support_votes`: the early votes whose sender has no second vote among the late votes;
- `count`: the number of senders of late votes; `score B`: the Goldfish score of `B` counted
  over the support votes; a block `B` is `eligible` when `count < 2 * score B`;
- `tree`: the filtered block tree; `root`: the fork-choice root; `A`: the strong-gadget root of
  the store's round (`get_sg_root_with`);
- `H`: the block the Goldfish walk `ghost` reaches from `A` in `tree`, and whether it is
  eligible;
- `G`: the stable-record root of the store's round (`round_stable_root`), a block;
- `S?`: the block the confirmation candidate `confirmation_candidate` offers, possibly absent.

The three writes, in order: `st.live_confirmed` becomes `H` if `H` is eligible and `root`
otherwise; `st.latest_stable` becomes `advance_confirmed st.latest_stable G`; the candidate is
`advance_confirmed st.latest_confirmed H` if `H` is eligible, otherwise
`advance_confirmed st.latest_confirmed S` if `S?` holds a block `S`, otherwise
`st.latest_confirmed`, and `st.latest_confirmed` becomes `floor_on_stable` of the stable record
just written, the candidate, and the confirmation record as it was. The saved grades
`st.saved_grades` are not written.

Raises when a raising read does: when a slot-`s` vote of the store has no stamp, when a block of
`st.T` has no stamp, when two blocks of `st.T` share a root, or when the `g1` or `g2` result of
the store's round is pending. -/
def update_confirmation (st : Store V) (s : Slot) : DRE (Store V) := do
  let early_votes ←
    {vote ∈ᴹ st.pool s | occurrenceBefore (← st.tau vote) (C.gf_confirmation_time s)}
  let late_votes ← beforeCutoff st.timestamp_vote (C.confirmation_time s) (st.pool s)
  let support_votes :=
    {vote ∈ early_votes | no_second_vote_in late_votes vote = true}
  let count := raw_voters_count late_votes
  let score := raw_goldfish_score st.T support_votes support_votes s
  let eligible := fun B => do
    let n ← score B
    return count < 2 * n
  let tree := get_filtered_block_tree st
  let root := get_fg_root st
  let A ← get_sg_root_with C st
  let H ← ghost A tree score eligible
  let H_eligible ← eligible H
  let G ← round_stable_root st (C.round_of st.s)
  let S? ← confirmation_candidate C st
  let mut st := st
  if H_eligible then
    st.live_confirmed ← H
  else
    st.live_confirmed ← root
  st.latest_stable ← advance_confirmed st.latest_stable G
  let mut candidate := st.latest_confirmed
  if H_eligible then
    candidate ← advance_confirmed st.latest_confirmed H
  else if S? ≠ none then
    candidate ← advance_confirmed st.latest_confirmed S?.value
  st.latest_confirmed ← floor_on_stable st.latest_stable candidate st.latest_confirmed
  return st

end Spec.Protocol
