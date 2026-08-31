import Spec.«04_SGForkChoice»
import Spec.«02_GoldfishStore»
import Spec.Defs.Nondet

/-!
# The SG store handler

`process_sg_vote`, the handler that admits one combined attestation into the round pool
`Σ.attestations[·]`.

## One pool, keyed by the SG projection

The pool holds whole attestations, and admission reads only the SG vote — the
`(validator, round, confirmed)` projection: at most two attestations with *distinct
confirmed blocks* per
validator are kept, so attestations differing only in their pair fields are one vote and
the second is turned away. Two distinct confirmed blocks from one validator in one round are an
equivocation, and nothing reads a third.

## An empty confirmed block is stored

At the round's voting time an honest validator's confirmed block is its `live_confirmed`,
which is a block; an empty one appears only in adversarial attestations. It is still **a value the
pool holds**: it counts its sender into `majority_fork_choice`'s denominator and into an
equivocation, and it resolves at receipt — what it never does is support a block
(`sg_support`) or carry a grade (`09_Healing.lean`).

## The window has both ends

A round-`r` attestation is admitted only while `max(0, round(Σ.s) − ηSG) ≤ r ≤ round(Σ.s)`:
one already expired for `latest`'s window is not stored, and one from a future round is
turned away as every handler turns away the future.

## Extract

`process_sg_vote(Σ, a)` records a round-`r` attestation with its processing time, unless
its round is outside the window `[max(0, round(Σ.s) − ηSG), round(Σ.s)]`, the pool already
holds an attestation by that validator with the same confirmed block, or it already holds
two with distinct ones. An empty confirmed block is stored like any other value. The
producing side is the
tick (`11_Duties.lean`): the FG vote is computed at `a_r`, the SG vote at the validator's
own voting time, and the assembled attestation is broadcast and processed there.

-/

set_option autoImplicit false

namespace DC

variable {Validator : Type} [BlockIds] [BlockIdentity Validator]
  [DecidableEq Validator] [Params]

open Params

/-! ## Figure `process_sg_vote(Σ, a)` -/
/-- Record a round-`r` attestation with its
    processing time, unless its round is outside the admission window, its confirmed block
    is one the
    pool already holds for this validator — attestations differing only in their pair
    fields are one vote — or two distinct confirmed blocks by this validator are already
    held: "two
    witness the equivocation; nothing reads a third."

    `round(Σ.s) − ηSG` is `Nat` subtraction, which truncates at `0` — exactly the
    protocol's `max(0, ·)`. -/
def Store.processSGVote (S : Store Validator) (a : Attestation Validator) :
    Store Validator := Id.run do
  let mut S := S
  -- the distinct confirmed blocks the pool already holds for this validator's round
  let roundVotes := {e.vote.confirmed | e ∈ S.attestations[a.round], e.vote.validator = a.validator}
  if a.round < round S.s - ηSG ∨ a.round > round S.s ∨
      a.confirmed ∈ roundVotes ∨ |roundVotes| = 2 then
    return S
  S.attestations[a.round] ← S.attestations[a.round] ∪
    {TimestampedVote.mk (vote := a) (time := S.t)}
  return S

end DC
