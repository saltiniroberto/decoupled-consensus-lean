module
public import Goldilocks.FG.State
public import Goldilocks.AC.Interface
public import Spec2.Defs.Notation

@[expose] public section

/-!
# The node

A validator's node keeps its clock `t`, the FG state `S`, the AC state `A`, its anti-slashing
record `Λ`, and `awakeSince`, the time since which the node has been awake without interruption.
The node's routines read the clock and hand `S`, `A` and `Λ` whole to the routines of the finality
gadget and of the available chain.

This file declares, in the namespace `Goldilocks`:

- `NodeState V`, the node state;
- the wake rule: `proposal_window_start` and `duty_window_start`, the two times a duty's test
  compares `awakeSince` with; `NodeState.awake_since`, the test; `wake`, what the node state
  becomes when the node wakes; and `record_awake`, what the first tick after a wake writes;
- `initial`, the node state a node starts from;
- the form checks of a received object, `attestation_well_formed` and `block_well_formed`;
- `block_admissible`, the one test of every refusal of a block, run before any write;
- the handlers of a received object: `on_block`, `on_ac_message` and `on_attestation`;
- the duties: `propose_block` and `attest`;
- `tick`, what the node does when its clock reaches a time.

**The wake rule.** A validator performs a duty of slot `s` only if it has been awake, without
interruption, since a time fixed for that duty: the proposal since `proposal_window_start C s`,
the time `C.t_ s + C.Δ − 4 * C.Δ * (C.k + 1)`, one slot before the start of the slow window of the
lock state it reads; the revocation of the locks, the Goldfish vote, the confirmation update and
the attestation since `duty_window_start C s`, the time `C.t_ s + C.Δ − 4 * C.Δ * C.k`. The lock
entries and the saved confirmations a duty of slot `s` reads were then written by this node's own
ticks while it was awake. `tick` first records the time of a wake (`record_awake`), then tests
each duty against `awakeSince`; `wake` erases `awakeSince`; the handlers of received objects keep
it. A failed test suspends one duty: the clock is still set, the lock entries past their deadline
are still deleted, and each other duty is tested on its own condition.

**Restarts.** A restart is not modelled: a node is built by `initial` only. The anti-slashing
record `Λ` persists through a restart (`SigningHistory`).

This file holds definitions only.
-/

open scoped DC

open DC (DRE)

namespace Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The node state -/

/-- The state of a validator's node: the validator `v` it runs as, its clock `t`, the FG state
`S`, the AC state `A`, the anti-slashing record `Λ`, and `awakeSince`, the time since which the
node has been awake without interruption. `awakeSince` is `none` between a wake and the first
tick the node runs after it, and `some t'` afterwards, `t'` being that tick's time. -/
structure NodeState (V : Type) where
  /-- The validator this node runs as. -/
  v : V
  /-- The node's clock. -/
  t : Time
  /-- The FG state. -/
  S : FGState V
  /-- The AC state. -/
  A : ACState V
  /-- The anti-slashing record. -/
  Λ : SigningHistory
  /-- The time since which the node has been awake without interruption, or `none` between a
  wake and the first tick after it. -/
  awakeSince : Option Time

/-! ## The wake rule -/

section WakeRule

variable (C : Config)

/-- The time from which a validator must have been awake to propose the block of slot `s`: one
delay `C.Δ` after the start of slot `s − k − 1`, `C.t_ s + C.Δ − 4 * C.Δ * (C.k + 1)`, with `k`
the slow window `C.k`. It is computed as a time, so for a small `s` it is negative. -/
@[no_expose] def proposal_window_start (s : Slot) : Time :=
  C.t_ s + C.Δ - 4 * C.Δ * ((C.k : Time) + 1)

/-- The time from which a validator must have been awake to run the revocation of the locks, the
Goldfish vote, the confirmation update and the attestation of slot `s`: one delay `C.Δ` after the
start of slot `s − k`, `C.t_ s + C.Δ − 4 * C.Δ * C.k`, with `k` the slow window `C.k`. It is
computed as a time, so for a small `s` it is negative. -/
@[no_expose] def duty_window_start (s : Slot) : Time :=
  C.t_ s + C.Δ - 4 * C.Δ * (C.k : Time)

end WakeRule

/-- The test of the wake rule: whether the node whose state is `n` has been awake, without
interruption, since the time `t₀` or earlier. It is true when `n.awakeSince` is `some t'` with
`t' ≤ t₀`, and false when `n.awakeSince` is `none`. -/
@[no_expose] def NodeState.awake_since (n : NodeState V) (t₀ : Time) : Bool := Id.run do
  if n.awakeSince ≠ none then
    return n.awakeSince.value ≤ t₀
  return false

/-- The node's state when the node wakes at the time `t`: the state `n` with `awakeSince` set to
`none` and the clock set to `t`. The FG state, the AC state and the signing history are kept. A
message delivered between the wake and the first tick is then handled at the clock `t`: a block of
the current slot passes `block_admissible`'s clock test, and the AC state stamps it with `t`. -/
@[no_expose] def wake (n : NodeState V) (t : Time) : NodeState V := Id.run do
  let mut n := n
  n.awakeSince ← none
  n.t ← t
  return n

/-- What a tick at the time `t` first writes into the node's state `n`: if `awakeSince` is `none`
(the node has woken and run no tick since), it becomes `some t`; otherwise `n` is unchanged. -/
@[no_expose] def record_awake (n : NodeState V) (t : Time) : NodeState V := Id.run do
  let mut n := n
  if n.awakeSince = none then
    n.awakeSince ← t
  return n

/-- The node state a node of the validator `v` starts from: the clock at `0`, the initial FG state
`FGState.initial`, the initial AC state `ACState.initial`, the initial anti-slashing record
`SigningHistory.initial`, and `awakeSince` equal to `proposal_window_start C 0`, the earliest time
a duty's test compares it with. A node that is awake from the start and never sleeps keeps that
value, and so passes every duty's test in every slot. -/
@[no_expose] def initial (C : Config) (v : V) : NodeState V :=
  NodeState.mk (v := v) (t := 0) (S := FGState.initial) (A := ACState.initial)
    (Λ := SigningHistory.initial) (awakeSince := proposal_window_start C 0)

/-! ## The form checks of a received object -/

/-- `attestation_well_formed a`: whether the attestation `a` has the form of an attestation: its
height `a.h` is at least `1`, and, when it has a finality pair, the pair's height is less than
`a.h`. This is a check of the form alone: the signature of an attestation is not modelled, and
the validator `a.val_index` is taken to be its sender. -/
@[no_expose] def attestation_well_formed (a : Attestation V) : Bool := Id.run do
  if a.finality_pair ≠ none then
    return 1 ≤ a.h && a.finality_pair.value.hf < a.h
  return 1 ≤ a.h

/-- `block_well_formed P X B`: whether the block `B` has the form of a block: every attestation it
includes is well formed (`attestation_well_formed`); its Goldfish votes are well placed and their
validators are in the committee of their slot (`ac_valid_payload`); and its root `B.root` is the
digest `X.digest` of its content, the root of its parent, its slot, its attestations, its Goldfish
votes and its support votes. This is a check of the form alone: the signature of a block is not
modelled, and the validator `B.proposer?` names is taken to be its proposer. -/
@[no_expose] def block_well_formed (P : Provisional V) (X : External V) (B : Block V) : Bool :=
  (∀ a ∈ B.attestations, attestation_well_formed a : Bool) && ac_valid_payload P B &&
    B.root = X.digest B.parent.root B.slot B.attestations B.votes B.support_votes

/-! ## The test of a block -/

/-- `block_admissible C P X n B`: whether the node whose state is `n` accepts the block `B`. Every
refusal of a block is tested here, before any write. It returns false in each of these cases,
tested in order, and true otherwise:

1. `B` is not well formed (`block_well_formed`);
2. `B`'s slot is later than the slot of the node's clock, `C.slot n.t`;
3. some block of the FG state's tree `n.S.T` has the root `B.root`;
4. the tree `n.S.T` does not hold `B`'s parent;
5. the finalized block `n.S.F` is neither an ancestor of `B` nor `B`;
6. `B`'s proposer is not the proposer of its slot, `P.proposer B.slot`;
7. `B`'s parent's slot is not earlier than `B`'s slot;
8. some attestation of `B.attestations` is not valid against the chain state of `B`'s parent,
   `n.S.σ[B.parent]` (`valid_attestation`).

When it returns true, the chain state of `B` is computed from its parent's, which cannot fail. -/
@[no_expose] def block_admissible (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (B : Block V) : Bool := Id.run do
  if !block_well_formed P X B then
    return false
  if C.slot n.t < B.slot then
    return false
  if ∃ B' ∈ n.S.T, B'.root = B.root then
    return false
  if B.parent ∉ n.S.T then
    return false
  if !n.S.F.ancestorEq B then
    return false
  if B.proposer? ≠ P.proposer B.slot then
    return false
  if !(B.parent.slot < B.slot) then
    return false
  if ∃ a ∈ B.attestations, !valid_attestation n.S.σ[B.parent] a then
    return false
  return true

/-! ## The handlers of a received object -/

/-- On receiving the attestation `a`: when `a` is well formed (`attestation_well_formed`), the FG
state receives it into its pool (`fg_on_attestation`); otherwise the node state is unchanged. -/
@[no_expose] def on_attestation (n : NodeState V) (a : Attestation V) : NodeState V := Id.run do
  let mut n := n
  if !attestation_well_formed a then
    return n
  n.S ← fg_on_attestation n.S a
  return n

variable [RootOrder]

/-- On receiving the block `B`: when the node refuses it (`block_admissible` is false), the node
state is unchanged; otherwise, in order, the FG state accepts it (`fg_on_block`), and the AC state
admits it at the node's clock `n.t` (`ac_on_block`). A refused block is not seen by the available
chain. -/
@[no_expose] def on_block (C : Config) (P : Provisional V) (X : External V) (n : NodeState V) (B : Block V) :
    NodeState V := Id.run do
  let mut n := n
  if !block_admissible C P X n B then
    return n
  n.S ← fg_on_block C n.S B
  n.A ← ac_on_block C P n.A n.t B
  return n

/-- On receiving the Goldfish vote `vote`: the AC state admits it at the node's clock `n.t`
(`ac_on_message`). -/
@[no_expose] def on_ac_message (C : Config) (P : Provisional V) (n : NodeState V) (vote : GoldfishVote V) :
    NodeState V := Id.run do
  let mut n := n
  n.A ← ac_on_message C P n.A n.t vote
  return n

/-! ## The duties -/

/-- The proposal of the node whose state is `n`, at its clock `n.t`, in the slot
`s := C.slot n.t`:

1. the available chain gives the parent `H`, the Goldfish votes `votes` and the support votes
   `support_votes` (`ac_proposal`), read over the frame `fg_to_ac n.S`;
2. the attestations are those of the FG state's pool that a block on `H` includes
   (`proposal_attestations`);
3. the root is the digest `X.digest` of the block's content;
4. the block of slot `s`, with parent `H`, that root, those votes, support votes and attestations,
   and the proposer `n.v`, is broadcast, and the node receives it (`on_block`).

Raises when `ac_proposal` does. -/
@[no_expose] def propose_block (C : Config) (P : Provisional V) (X : External V) (n : NodeState V) :
    DREB V (NodeState V) := do
  let s := C.slot n.t
  let Φ := fg_to_ac n.S
  let {H := H, votes := votes, support_votes := support_votes} ⇐ ac_proposal C n.A Φ n.t
  let attestations := proposal_attestations n.S H
  let root := X.digest H.root s attestations votes support_votes
  let B := Block.node (parent := H) (slot := s) (root := root) (votes := votes)
    (support_votes := support_votes) (attestations := attestations) (proposer := n.v)
  broadcast (NamedObject.block B)
  return on_block C P X n B

/-- The attestation duty of the node whose state is `n`, at its clock `n.t`:

1. the available chain gives a source and a head (`ac_to_fg`), read over the frame
   `fg_to_ac n.S`;
2. when there is no source, nothing is sent and the node state is unchanged;
3. otherwise the attestation is built from the source, the head and the anti-slashing record
   (`fg_attest`), and the record becomes the one `fg_attest` returns;
4. when `fg_attest` returns no attestation, nothing is sent;
5. otherwise the attestation is broadcast, and the node receives it (`on_attestation`).

Raises when `ac_to_fg` does. -/
@[no_expose] def attest (C : Config) (n : NodeState V) : DREB V (NodeState V) := do
  let mut n := n
  let Φ := fg_to_ac n.S
  let {source := source, head := head} ⇐ ac_to_fg C n.A Φ n.t
  if source ≠ none then
    let mut Λ := n.Λ
    let {fst ← Λ, snd := a?} := fg_attest n.S Λ n.v source.value head
    n.Λ ← Λ
    if a? ≠ none then
      broadcast (NamedObject.attest a?.value)
      n ← on_attestation n a?.value
  return n

/-! ## The tick -/

/-- What the node of the validator `n.v` does when its clock reaches the time `t`, from its state
`n`, with the parameters `C`, the values `P` (the proposer and the committee of each slot) and the
values `X` (the digest). `s` is the slot of `t`, `C.slot t`. In order, each step reading the
state the steps before it left:

1. record the time of a wake: if `n.awakeSince` is `none`, it becomes `some t` (`record_awake`);
2. set the clock `n.t` to `t`;
3. the tests of the wake rule, on `awakeSince` as step 1 left it: `awake_for_proposal`, whether
   the node has been awake since `proposal_window_start C s` or earlier, and `awake_for_duty`,
   whether it has been awake since `duty_window_start C s` or earlier (`NodeState.awake_since`);
4. the tick of the available chain (`ac_on_tick`), over the frame `fg_to_ac n.S`: the lock
   entries past their deadline are deleted; at the vote time of `s`, when `awake_for_duty` holds,
   the locks are revoked and the Goldfish vote duty runs; at the support cutoff of `s`, when
   `awake_for_duty` holds, the confirmation update runs;
5. the proposal (`propose_block`), when `s > 0`, `t` is the start of `s`, `C.t_ s`, `n.v` is the
   proposer of `s`, and `awake_for_proposal` holds;
6. the attestation (`attest`), when `t` is the action time of the round of `s`,
   `C.a_ (C.round s)`, and `awake_for_duty` holds.

A failed test suspends one duty: the clock is still set, the lock entries past their deadline are
still deleted, and each other duty is tested on its own condition. Each of steps 5 and 6 computes
its own frame from the FG state as the steps before it left it. The objects the duties send are
broadcast (`broadcast`), in the order of the steps.

Raises when the tick of the available chain or a duty that runs raises. -/
@[no_expose] def tick (C : Config) (P : Provisional V) (X : External V) (n : NodeState V) (t : Time) :
    DREB V (NodeState V) := do
  let mut n := n
  n ← record_awake n t
  n.t ← t
  let s := C.slot t
  let awake_for_proposal := n.awake_since (proposal_window_start C s)
  let awake_for_duty := n.awake_since (duty_window_start C s)
  let Φ := fg_to_ac n.S
  n.A ⇐ ac_on_tick C P n.A Φ t n.v awake_for_duty awake_for_duty
  if s > 0 && t = C.t_ s && n.v = P.proposer s && awake_for_proposal then
    n ⇐ propose_block C P X n
  if t = C.a_ (C.round s) && awake_for_duty then
    n ⇐ attest C n
  return n

end Goldilocks
