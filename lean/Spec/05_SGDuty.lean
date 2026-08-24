import Spec.«04_SGForkChoice»
import Spec.«02_GoldfishDuties»
import Spec.Defs.Nondet

/-!
# Figure 5 — the SG duty and store handler

`sg_vote`, run at the round's vote time `a_r`, and `process_sg_vote` — and the protocol's
`on_tick`, the SG layer's extension of Figure 2's.

The `-- line n` comments number the algorithm's lines.

## What the SG layer adds to `on_tick`

One line: at `t = a_r` for the current round `r`, run `sg_vote`. The proposer and voter of
Figure 2 then call Figure 4's `get_head`; nothing else in their duties changes, and
available confirmation is unchanged.

The added line is this file's `Store.onTick`: run Figure 2's reading, `Fig2.onTick`, and
then the one line. The finality layer never touches `on_tick`, so that composition is the
protocol's tick. The redirected `get_head` is not written out: the finality layer
redefines it again, and that version, `Store.getHead`, is the protocol's. So this file
holds the two routines Figure 5 itself introduces and the protocol's `on_tick`.

`a_r` is a public parameter, no formula fixed — the `SGSchedule` class in `Model.lean`:
assumed, so `on_tick` can dispatch on it and `sg_vote` can require it.

## An honest vote is never empty

At `a_r` an honest validator votes its current `live_confirmed`, which is a block; an
empty head can appear only in adversarial votes. So line 3 always names a block, and
`SGVote.head` is an `Option` only because the wire object admits `⊥` — nothing an honest
duty produces uses it.

## Extract

`on_tick` gains one line: at `t = a_r` for the current round `r`, run `sg_vote`. The
proposer and voter of [fig:02_GoldfishDuties] then call the `get_head` of
[fig:04_SGForkChoice]; that redirected reading is not written out here, because the
finality layer redefines `get_head` again and that final reading is the protocol's. Available confirmation is unchanged.

At `a_r`, an honest validator votes its current `live_confirmed`, which is a block; the
empty head appears only in adversarial votes here. `process_sg_vote(Σ, vote)` is
`process_goldfish_vote` one field over: it records a round-`r` vote with its processing
time, unless it is from a future round, already held, or a third vote by a validator
already seen equivocating.

-/

set_option autoImplicit false

namespace Consensus1

variable {Validator : Type} [Roots] [DecidableEq Validator] [Committees Validator] [Params]
  [RootComputation Validator] [SGSchedule]

/-- `process_sg_vote(Σ, vote)`: record a round-`r` SG vote with its
    processing time, unless it is from a future round, already held, or a third vote by a
    validator already seen equivocating.

    `process_goldfish_vote`'s shape exactly, one field over: the round test is against
    `round(Σ.s)` rather than `Σ.s`, and line 8 is where "at most two distinct votes per
    validator" is maintained — "two witness the equivocation; nothing reads a third".

    ## Extract -/
def Store.processSGVote (S : Store Validator) (vote : SGVote Validator) :
    Store Validator := Id.run do
  let mut S := S
  -- line 6
  if vote.round > round S.s ∨ vote ∈ S.sgVotes[vote.round] then
    return S                                                   -- line 7
  -- line 8: two distinct votes by this validator are already held
  if ∃ a ∈ S.sgVotes[vote.round], ∃ b ∈ S.sgVotes[vote.round],
      a.validator = vote.validator ∧ b.validator = vote.validator ∧ a ≠ b then
    return S                                                   -- line 9
  S.sgVotes[vote.round] ← S.sgVotes[vote.round] ∪ {vote}       -- line 10
  S.sgVoteTime[vote] ← S.t
  return S

/-- `sg_vote(Σ)`, run at `a_r`: vote the store's current
    `live_confirmed` for the current round.

    A `NDREB` duty, as the Goldfish duties are: line 4 is the protocol's two verbs. Total —
    this duty runs no walk, picks nothing, raises nothing; only the outbox is under the
    monad. "Runs at `a_r`" is an input precondition, as the Goldfish duties' instants
    are, over the assumed `SGSchedule`.

    ## Extract -/
def Store.sgVote (i : Validator) (S : Store Validator)
    (_ : S.t = SGSchedule.a (round S.s) := by solve_by_elim [And.left, And.right]) :
    NDREB Validator (Store Validator) := do
  let r := round S.s                                           -- line 2
  -- line 3
  let vote := SGVote.mk (validator := i) (round := r) (head := some S.liveConfirmed)
  broadcast (Message.sgVote vote)                              -- line 4
  return S.processSGVote vote

/-- `on_tick(Σ, t)`, the protocol's reading: Figure 2's `on_tick`, then the SG layer's
    one line — at `t = a_r` for the current round, run `sg_vote`. No later layer touches
    `on_tick`.

    `Fig2.onTick` has already written the clock into the store it returns, so the
    dependent `if` hands `sg_vote` its instant precondition, exactly as Figure 2's own
    branches do.

    The protocol fixes no relation between `a_r` and the Goldfish instants. On a schedule
    where `a_r` coincided with one, the two actions compose: `sg_vote` runs on the
    Goldfish duty's post-state, and both broadcasts are in the outbox — no union is
    written anywhere, the monad carrying the earlier sends past the `if`. On the protocol's
    own schedules the instants are distinct (`Fig2.onTick`'s docstring). -/
def Store.onTick (i : Validator) (S : Store Validator) (t : Int)
    (isProposer : Nat → Validator → Bool) : NDREB Validator (Store Validator) := do
  let S ← Fig2.onTick i S t isProposer
  -- the SG layer's line: at `t = a_r` for the current round, run `sg_vote`
  if _ : S.t = SGSchedule.a (round S.s) then
    return ← S.sgVote i
  return S

end Consensus1
