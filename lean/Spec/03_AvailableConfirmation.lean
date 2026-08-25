import Spec.«01_GoldfishWalk»

/-!
# Available confirmation

`update_confirmation(Σ, s)`, run once per slot at `t_s + 6Δ`. "Confirmation is the same walk
over a stricter vote set and a larger denominator."

## What makes it stricter

Two cutoffs on the same pool, `early ⊆ late`; the walk scores the `early` votes whose
validator the equivocation record does not mark before the late cutoff, against `late`'s
participants — the rule itself is the Extract prose below. The two consequences the
protocol draws there — the scored set holds at most one vote per validator, and at most
one child can pass the eligibility condition — are facts about the sets rather than
about this routine, so neither is rendered as a hypothesis.

## Why it does not reuse `goldfish_eligible`

Confirmation's eligibility condition is the majority test *without* the current-slot
escape: the walk runs at `t_s + 6Δ` over slot-`s` votes, and a block of the current slot
has no business being confirmed for free. So the routine defines its own `eligible`
inline, as the figure does, and passes it to `ghost` directly rather than going through
`goldfish_fork_choice`.

The walk starts at genesis over `Σ.T` — from genesis over the live tree. Once the
finality layer exists the live tree is `T_F(Σ)`; at this layer nothing has been finalized
yet and `Σ.T` is all there is. The finality layer runs available confirmation's walk from
`Σ.F` over `T_F(Σ)`, so its version of this rule is a change to `Σ.F` and `T_F`, not to
this routine.

## Extract

Confirmation is the same walk over a stricter vote set and a larger denominator. Let
`early` and `late` be the stored slot-`s` votes timestamped before `t_s + 2Δ` and
before `t_s + 6Δ`. The walk scores

`votes = {vote ∈ early : Σ.gf_equiv[s][vote.validator] is not before t_s + 6Δ}`

against the participant count of `late`: a validator counts when it voted in time and
no differing vote of its was processed before the late cutoff, while the denominator
counts everyone who voted at all.

The store keeps one vote per slot and validator, so `votes` holds at most one vote per
validator and the score's equivocator inputs are empty here. At most one child can pass
the eligibility condition, so the descent has no choice to make.

Slot `s` is evaluated once, at `t_s + 6Δ`, from genesis over the live tree. The result
is at worst genesis, never empty. `Σ.live_confirmed` takes the result unconditionally;
`Σ.latest_confirmed` only ever moves forward.

-/

set_option autoImplicit false

namespace DC

variable {Validator : Type} [Roots] [DecidableEq Validator] [Committees Validator] [Params]

open Params

/-! ## Figure at `t_s + 6Δ` -/
/-- Run at `t_s + 6Δ`: evaluate slot `s`
    once and record what it confirms.

    `Σ.live_confirmed` takes the result unconditionally — it is "the block the last evaluated
    slot confirmed", and an evaluation that walks nowhere leaves genesis, never nothing.
    `Σ.latest_confirmed` only ever moves forward, its write behind the test
    `Σ.latest_confirmed ⪯ H`.

    Both cutoffs read the timestamps with the raising bracket, through `Finset.filterM`
: a held vote the store never stamped raises rather than silently
    failing the cutoff. `process_goldfish_vote` stamps everything it stores, so the raise
    marks a store the handlers cannot build — a coherence fact for `Analysis/`.

    "Run at `t_s + 6Δ`" — slot `s`'s own start — is an input precondition, as the
    Goldfish duties' instants are. -/
def Store.updateConfirmation (S : Store Validator) (s : Nat)
    (_ : S.t = slotStart s + 6 * (Δ : Int) := by solve_by_elim [And.left, And.right]) :
    NDRE (Store Validator) := do
  let mut S := S
  let early ← {vote ∈ᴹ S.gfVotesAt s | (← S.gfVoteTime[vote]) < slotStart s + 2 * (Δ : Int)}
  let late ← {vote ∈ᴹ S.gfVotesAt s | (← S.gfVoteTime[vote]) < slotStart s + 6 * (Δ : Int)}
  -- the early votes whose validator the record does not mark before `t_s + 6Δ`
  let votes := {vote ∈ early |
    ¬ timeBefore (S.gfEquiv s vote.validator) (slotStart s + 6 * (Δ : Int))}
  -- the denominator is `late`'s participants
  let votersCount := |{v ∈ Committees.K s | ∃ a ∈ late, a.validator = v}|
  -- the majority condition, with no current-slot escape — see the module header;
  -- `votes` is already cleaned, so the score's equivocator inputs are empty
  let eligible := fun B => 2 * goldfishScore votes ∅ s B > votersCount
  let H ← ghost .genesis S.T (goldfishScore votes ∅ s) (fun B => pure (eligible B))
  S.liveConfirmed ← H
  if S.latestConfirmed ⪯ H then
    S.latestConfirmed ← H
  return S

end DC
