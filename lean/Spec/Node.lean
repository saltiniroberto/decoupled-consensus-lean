import Spec.NodeState
import Spec.Protocol.GoldfishVotes
import Spec.Protocol.Attestations
import Spec.Protocol.Blocks
import Spec.Defs.Notation

/-!
# The node

The routines of the node, over the flat store `Store V` of `lean/Spec/Store.lean` and the
node state `NodeState V` of `lean/Spec/NodeState.lean` (the store, the signing history and
`awakeSince`, the instant since which the node has been awake without interruption), in the
namespace `Spec`:

- `make_grades_compatible_with_finalized`: the store with every block in its saved grades
  replaced by its deepest ancestor compatible with its finalized block;
- `initial`: the node state a node starts from;
- `tick`: what a node does when its clock reaches an instant: it updates the grades,
  sets the clock, and runs the proposal, the Goldfish vote, the confirmation and the attestation,
  each when its condition holds; the duties broadcast what they send;
- `receive_block`, `receive_goldfish_vote`, `receive_attestation`:
  what a node does on receiving a block, a Goldfish vote, an attestation, one routine
  per kind of object, each taking only the parameters it reads. The wiring
  (`lean/Sts.lean`) maps each delivered object to the routine of its kind.

This file holds every routine the wiring calls: `initial`, `tick` and the three
receiving routines. The routine that each receiving routine calls, and that admits its object into
the store, is in the file of that kind of object, beside the duty that sends it: `on_block`
in `lean/Spec/Protocol/Blocks.lean`, `on_goldfish_vote_checked` in
`lean/Spec/Protocol/GoldfishVotes.lean`, `admit_attestation` in
`lean/Spec/Protocol/Attestations.lean`. `tick` calls the four duties by name.

**The wake rule.** `tick` first records the wake's instant (`record_awake`), then runs each
duty only if the node passes its test `NodeState.awake_since` (`lean/Spec/NodeState.lean`)
against `awakeSince`; `wake` (`lean/Spec/NodeState.lean`) erases `awakeSince`; the three
receiving routines keep it. A
failed test suspends one duty: the grades are still updated, the clock is still set, and each
other duty is tested on its own condition.

**Arguments.** Every routine here that reads a parameter takes the parameters `C : Config` of
`lean/Spec/Config.lean`, and also the values `P : Provisional V` when it reads the proposer, a
committee or the weights, and the values `X : External V` when it reads the root of a new block,
directly or through a routine it calls. `tick` takes all three; `receive_block`
takes `C` and `P`; `receive_goldfish_vote` takes `P` alone;
`receive_attestation` takes `C` alone, and so does `initial`, which fixes its
`awakeSince`; it also takes the validator `v` the node runs as. The tick reads that validator from
the node state, `n.v`. The body of the tick reads `C.Δ`, `C.slotOf t`, `C.round_of s`,
`C.round_attestation_time r`, `P.proposer s`, and the instants of a slot's schedule
`C.proposal_time s`, `C.vote_time s`, `C.gf_confirmation_time s`. No routine takes the instant
after which delivery is bounded: no routine reads it.

**Raising.** `tick` raises exactly where `update_grades` or a duty it runs raises. The
other routines are total.

**Order.** The tick updates the saved grades `st.saved_grades` from the
incoming store before the clock is set (`update_grades`). At the end, both transitions replace
every block in the saved grades by its deepest ancestor compatible with the store's finalized
block (`make_saved_grades_compatible_with`).

This file holds definitions only.
-/
open scoped DC

open Spec.Protocol (update_grades make_saved_grades_compatible_with goldfish_vote
  update_confirmation on_block on_goldfish_vote_checked admit_attestation propose_block
  attest)

namespace Spec

variable {V : Type} [DecidableEq V] [Fintype V]
variable (C : Config) (P : Provisional V) (X : External V)

/-- The store `st` with every block in its saved grades `st.saved_grades` replaced by its deepest
ancestor compatible with its finalized block `st.F` (`make_saved_grades_compatible_with`). Every
other field is kept. -/
def make_grades_compatible_with_finalized (st : Store V) : Store V := Id.run do
  let mut st := st
  st.saved_grades ← make_saved_grades_compatible_with st.F st.saved_grades
  return st

/-- The node state a node of the validator `v` starts from: the validator `v`, the initial store
`Store.init` (its saved grades included), the initial signing history `SigningHistory.initial`,
and `awakeSince` equal to `grade2_window_start C 0`, one
delay before the first cutoff of round `0`'s grade-2 result. A node that is awake from the start
and never sleeps keeps that value, and so passes every duty's test in every round, round `0`
included. -/
def initial (v : V) : NodeState V :=
  { v, st := Store.init, signingHistory := SigningHistory.initial,
    awakeSince := grade2_window_start C 0 }

/-- What the node of the validator `n.v` does when its clock reaches time `t`, from its state `n`,
with the
parameters `C`, the values `P` (the proposer of each slot, the committees, the weights) and the
values `X` (the root of each new block). Its
caller runs it at the multiples of the delay bound `C.Δ`; `s` is the slot of `t`, `C.slotOf t`. In
order:

1. record the wake's instant: if `n.awakeSince` is `none`, it becomes `some t` (`record_awake`);
2. update the grades whose completion time is `t`, reading the store `n.st` as it stands, before
   the clock is set (`update_grades`);
3. set the store's clock and slot to `t` and `s`;
4. test the four duties below in order, each reading the store the previous ones left. A duty
   runs only when its condition holds; one whose condition fails sends nothing. The objects the
   duties send are broadcast (`broadcast`, `lean/Spec/Broadcast.lean`), in the order
   proposal, Goldfish vote, attestation. In the conditions, "the node has been awake since `t₀`
   or earlier" is the test `n.awake_since t₀` (`NodeState.awake_since`), on `awakeSince` as step 1
   left it. With `r` the round of `s`, `C.round_of s`, the test against
   `grade1_window_start C r` is named `awake_for_grade1`, and the test against
   `grade2_window_start C r` is named `awake_for_grade2`. The first three duties run only in a
   slot after the genesis block's slot (`s > 0`):
   1. the proposal, when `t` is the proposal time of `s`, `n.v` is the proposer of `s`, and
      the node has been awake since `grade1_window_start C (C.round_of s)` or earlier: the store
      becomes the one `propose_block` returns, and its block is broadcast;
   2. the Goldfish vote, when `t` is the vote time of `s`, and the node has been awake since
      `grade1_window_start C (C.round_of s)` or earlier: the store becomes the one
      `goldfish_vote` returns, and its vote, if `n.v` is in the slot's committee, is broadcast;
   3. the confirmation, when `t` is the Goldfish confirmation time of `s`, and the node
      has been awake since `grade2_window_start C (C.round_of s)` or earlier: the store becomes
      the one `update_confirmation` returns for slot `s − 1`;
   4. the attestation, when `t` is round `r`'s attestation instant `C.round_attestation_time r`
      and the node has been awake since `grade2_window_start C r` or earlier
      (`awake_for_grade2`): the store and the signing history become the ones `attest`
      returns, and its attestation is broadcast;
5. replace every block in the store's saved grades by its deepest ancestor compatible with
   the store's finalized block (`make_grades_compatible_with_finalized`).

It returns the new node state: the store after step 5, the signing history after step 4, and
`awakeSince` after step 1. Its result type is `DREB V (NodeState V)`, so a caller reads the
objects sent with `.run []`. Raises when `update_grades` raises, or when a duty that runs raises. -/
def tick (n : NodeState V) (t : Time) : DREB V (NodeState V) := do
  let mut n := n
  n ← record_awake n t
  let mut st ← update_grades C P n.st t
  let s := C.slotOf t
  st.t ← t
  st.s ← s
  let mut signingHistory := n.signingHistory
  let r := C.round_of s
  let awake_for_grade1 := n.awake_since (grade1_window_start C r)
  let awake_for_grade2 := n.awake_since (grade2_window_start C r)
  if s > 0 then
    if t = C.proposal_time s && P.proposer s = n.v && awake_for_grade1 then
      st ⇐ propose_block C P X n.v st
    if t = C.vote_time s && awake_for_grade1 then
      st ⇐ goldfish_vote C P n.v st
    if t = C.gf_confirmation_time s && awake_for_grade2 then
      st ⇐ update_confirmation C st (s - 1)
  if t = C.round_attestation_time r && awake_for_grade2 then
    (st, signingHistory) ← attest C n.v st signingHistory
  st ← make_grades_compatible_with_finalized st
  return { v := n.v, st, signingHistory, awakeSince := n.awakeSince }

/-- On receiving the block `B`, in two steps: the store `n.st` admits `B` with
`on_block` (the attestations `B` includes admitted as well); then every block in the
store's saved grades is replaced by its deepest ancestor compatible with the store's finalized
block (`make_grades_compatible_with_finalized`). The signing history and `awakeSince` are kept. -/
def receive_block (n : NodeState V) (B : Block V) : NodeState V := Id.run do
  let mut n := n
  n.st ← on_block C P n.st B
  n.st ← make_grades_compatible_with_finalized n.st
  return n

/-- On receiving the Goldfish vote `vote`, in two steps: the store `n.st` admits `vote` with
`on_goldfish_vote_checked`; then every block in the store's saved grades is replaced by its
deepest ancestor compatible with the store's finalized block
(`make_grades_compatible_with_finalized`). The signing history and `awakeSince` are kept. -/
def receive_goldfish_vote (n : NodeState V) (vote : GoldfishVote V) : NodeState V := Id.run do
  let mut n := n
  n.st ← on_goldfish_vote_checked P n.st vote
  n.st ← make_grades_compatible_with_finalized n.st
  return n

/-- On receiving the attestation `a`, in two steps: the store `n.st` admits `a` with
`admit_attestation`; then every block in the store's saved grades is replaced by its
deepest ancestor compatible with the store's finalized block
(`make_grades_compatible_with_finalized`). The signing history and `awakeSince` are kept. -/
def receive_attestation (n : NodeState V) (a : Attestation V) : NodeState V := Id.run do
  let mut n := n
  n.st ← admit_attestation C n.st a
  n.st ← make_grades_compatible_with_finalized n.st
  return n

end Spec
