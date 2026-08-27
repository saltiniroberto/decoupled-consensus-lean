import Spec.«04_SGForkChoice»
import Spec.«02_GoldfishDuties»
import Spec.Defs.Nondet

/-!
# The SG duty and store handler

`sg_vote`, the head a validator votes for its round, and `process_sg_vote`, the handler
that stores one.

## The duty produces a vote; it does not send one

`sg_vote` returns the vote and touches nothing. Under the assembled protocol the head it
returns travels inside the round's one combined attestation, and it is the attestation duty
that broadcasts — `Store.onTick` in `09_Healing.lean`, at the sending validator's own time.
So this file has no line that reaches the wire, and `process_sg_vote` is reached only by a
receiver's handler.

This layer therefore adds no line to `on_tick`, and holds no reading of it. The tick that
runs the round's action is the graded layer's.

## The round's action instant

`a_r = t_{rR} + 6Δ`, `6Δ` after the round opens, is `heightDecisionTime` in `Model.lean`. It
is also `t_{rR+1} + 2Δ`, the tick at which the opening slot's confirmation is evaluated, so a
head signed for the round rests on a confirmation computed in the same tick.

## An empty head is never stored

At `a_r` an honest validator votes its current `live_confirmed`, which is a block; an
empty head can appear only in adversarial votes, and `SGVote.head` is an `Option` only
because the wire object admits `⊥`. `process_sg_vote` drops an empty-headed vote at
admission, so every stored vote's head is a `Block` (`SGHeadVote`, `Store.lean`) and every
reader — `latest`, `sg_support`, the healing scores — reads heads with no `Option` in
sight. Consequence: an empty-headed vote leaves no trace — it neither represents its
sender nor counts toward an equivocation.

## Extract

`sg_vote` produces the head a validator votes for its round: its current `live_confirmed`,
which is a block. Nothing is sent here. The head travels inside the round's one combined
attestation, and the graded layer's `on_tick` is what broadcasts that.

The proposer and voter of [fig:02_GoldfishDuties] call the `get_head` of
[fig:04_SGForkChoice]; that redirected reading is not written out here, because later layers
redefine `get_head` again and the last reading is the protocol's. Available confirmation is
unchanged at this layer.

At `a_r`, an honest validator votes its current `live_confirmed`, which is a block; the
empty head appears only in adversarial votes here. `process_sg_vote(Σ, vote)` is
`process_goldfish_vote` one field over: it records a round-`r` vote with its processing
time, unless its head is empty, it is from a future round, already held, or a third vote
by a validator already seen equivocating. An empty-headed vote is never stored, so every
stored head is a block.

-/

set_option autoImplicit false

namespace DC

variable {Validator : Type} [Roots] [DecidableEq Validator] [Committees Validator] [Params]
  [RootComputation Validator] [GoldfishWalk Validator]

/-! ## Figure `process_sg_vote(Σ, vote)` -/
/-- Record a round-`r` SG vote with its
    processing time, unless its head is empty, it is from a future round, already held,
    or a third vote by a validator already seen equivocating. Only votes whose head is a
    block are stored, so the stored entry (`SGHeadVote`) carries the head as a `Block`:
    the empty head is turned away first, and the extraction after it is the raising
    lift — so the routine's `DRE` advertises a failure no admitted vote can reach.

    `process_goldfish_vote` one field over, plus the head test: the round test is against
    `round(Σ.s)` rather than `Σ.s`, and the two-votes test is where "at most two distinct
    votes per validator" is maintained — "two witness the equivocation; nothing reads a
    third". A Goldfish vote's target is a block rather than an optional head, so that
    routine tests no head and stays pure. -/
def Store.processSGVote (S : Store Validator) (vote : SGVote Validator) :
    DRE (Store Validator) := do
  let mut S := S
  if vote.round > round S.s then
    return S
  -- an empty head is never stored, so the extraction below cannot raise
  if vote.head = ⊥ then
    return S
  let hv := SGHeadVote.mk (validator := vote.validator) (head := (← vote.head))
  if ∃ e ∈ S.sgVotes[vote.round], e.vote = hv then
    return S
  -- two distinct votes by this validator are already held
  if ∃ a ∈ S.sgVotes[vote.round], ∃ b ∈ S.sgVotes[vote.round],
      a.vote.validator = vote.validator ∧ b.vote.validator = vote.validator ∧
      a.vote ≠ b.vote then
    return S
  S.sgVotes[vote.round] ← S.sgVotes[vote.round] ∪
    {TimestampedVote.mk (vote := hv) (time := S.t)}
  return S

/-! ## Figure `sg_vote(Σ)` — runs at `a_r` -/
/-- The head this validator votes for
    the current round: its `live_confirmed`, which is a block.

    It returns the vote and leaves the store alone. Nothing is broadcast and nothing is
    recorded here — the caller sends the head inside the round's combined attestation, and a
    receiver's `process_sg_vote` is what stores one. See the module header.

    The result carries the full wire tuple rather than the head alone, so the caller has the
    validator and the round without recomputing them. `NDRE` and not a pure value only
    because the monad is where the rest of the tick lives; this routine walks nothing, picks
    nothing and raises nothing. -/
def Store.sgVote (S : Store Validator):
    NDRE (SGVote Validator) := do
  let r := round S.s
  let vote := SGVote.mk (validator := S.id) (round := r) (head := some S.liveConfirmed)
  return vote
end DC
