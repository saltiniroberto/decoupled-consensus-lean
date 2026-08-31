import Spec.«09_Healing»

/-!
# Available confirmation

`update_confirmation(Σ, s)`, the slot-`s` confirmation evaluation: the same walk as the
fork choice over a stricter vote set and a larger denominator, whose result — a genuine
confirmation, or the FG root — is what `Σ.live_confirmed` takes. One routine, as the
protocol writes it; the tick runs it at `t_s + 6Δ`, which is `t_{s+1} + 2Δ`
(`11_Duties.lean`).

## What makes it stricter

Two cutoffs on the same pool, `early ⊆ late`; the walk scores the `early` votes whose
validator `late` has not caught equivocating, against `late`'s participants — the rule
itself is the Extract prose below. The two consequences the protocol draws there — the
scored set holds at most one vote per validator, and at most one child can pass the
eligibility condition — are facts about the sets rather than about this routine, so
neither is rendered as a hypothesis.

## Why it does not reuse `goldfish_eligible`

Confirmation's eligibility condition is the majority test *without* the current-slot
escape: the walk runs at `t_s + 6Δ` over slot-`s` votes, and a block of the current slot
has no business being confirmed for free. So the routine defines its own `eligible`
inline, as the figure does, and passes it to `ghost` directly.

## Where the walk starts, and over what

From `get_goldfish_tree(Σ)` (`09_Healing.lean`): the round's SG root, over the
height-filtered blocks — the same tree the fork choice descends, no grade-0 veto, which
constrains signing, never a walk.

## Extract

Confirmation is the same walk over a stricter vote set and a larger denominator. Let
`early` and `late` be the slot-`s` votes *resolved* before `t_s + 2Δ` and *processed*
before `t_s + 6Δ`. The walk scores

`votes = {vote ∈ early : vote.validator does not equivocate in late}`

against the participant count of `late`: a validator counts when it voted in time and
no second vote of its has appeared since, while the denominator counts everyone who
voted at all.

Because `early ⊆ late`, a validator equivocating in `early` equivocates in `late` too,
so `votes` holds at most one vote per validator and the score's equivocator clause
never fires here. At most one child can pass the eligibility condition, so the descent
has no choice to make.

A slot is evaluated once, at `t_s + 6Δ`. The result is the walk's answer `H` when `H`
itself carries a window majority — `eligible(H)` — and the FG root otherwise:
`Σ.live_confirmed` is always this evaluation's output, either a genuine confirmation or
the root, and a split store collapses to the root rather than keeping a stale
confirmation. `Σ.latest_confirmed`, the monotone record, advances exactly when the new
value descends from it.

-/

set_option autoImplicit false

namespace DC

variable {Validator : Type} [BlockIds] [BlockIdentity Validator] [DecidableEq Validator] [Electorate Validator]
  [Committees Validator] [Proposers Validator] [Params]

open Params

/-! ## Figure `update_confirmation(Σ, s)` — runs at `t_s + 6Δ` -/
/-- The slot-`s` confirmation evaluation.
    `early` and `late` are the slot-`s` votes *resolved* before `t_s + 2Δ` and *processed*
    before `t_s + 6Δ`; what the walk scores is the `early` votes whose
    validator `late` does not catch equivocating, and what it scores them against is the
    number of `late`'s participants.

    The eligibility condition is the majority test alone, without `goldfish_eligible`'s
    current-slot escape — see the module header on why.

    One set serves as both of `goldfish_score`'s: `support_votes` already excludes every
    validator `late` catches equivocating, so the score's own equivocator set is empty and the
    equivocation handling is the `late` test rather than the score's. The `early` cut is on
    *resolution* time and the `late` cut on arrival — a vote supports only once its target is
    held, while a second vote betrays its sender the moment it arrives.

    `Σ.live_confirmed` takes the walk's answer `H` when `eligible(H)`, else the FG root —
    always this evaluation's output. `Σ.latest_confirmed` advances exactly when the new
    value descends from it. -/
def Store.updateConfirmation (S : Store Validator) (s : Nat) :
    NDRE (Store Validator) := do
  let mut S := S
  -- the early set cuts on *resolution* time, the late one on arrival
  let early := {e.vote | e ∈ S.gfVotes[s], S.resolvedBefore e (slotStart s + 2 * (Δ : Int))}
  let late := {e.vote | e ∈ S.gfVotes[s], e.time < slotStart s + 6 * (Δ : Int)}
  -- the early votes whose validator `late` does not catch equivocating
  let supportVotes := {vote ∈ early | ¬ ∃ b ∈ late, b.validator = vote.validator ∧ b ≠ vote}
  -- the denominator is `late`'s participants
  let votersCount := |{v ∈ Electorate.V | ∃ a ∈ late, a.validator = v}|
  -- the majority condition, with no current-slot escape — see the module header
  let eligible := fun B => 2 * S.goldfishScore supportVotes supportVotes s B > votersCount
  let root := S.getFGRoot
  let H ← S.ghost (← S.getGoldfishTree) (S.goldfishScore supportVotes supportVotes s)
    (fun B => pure (eligible B))
  S.liveConfirmed ← if eligible H then H else root
  if S.latestConfirmed ⪯[S] S.liveConfirmed then
    S.latestConfirmed ← S.liveConfirmed
  return S

end DC
