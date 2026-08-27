import Spec.«01_GoldfishWalk»

/-!
# Available confirmation

The confirmation walk and the two routines around it. Confirmation is the same walk as the
fork choice over a stricter vote set and a larger denominator.

The file holds three routines. `get_goldfish_confirmation` is the walk: it takes the tree to
descend, reads the slot's votes, and writes nothing. `Store.getConfirmation` runs it over the
layer's own tree for the store's current slot. `Store.updateConfirmation` records what comes
back. Splitting them is what lets the healing layer change the tree without touching the
walk.

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
inline, as the figure does, and passes it to `ghost` directly rather than going through
`goldfish_fork_choice`.

## Where the walk starts, and over what

Neither is this file's to decide any more. `Store.getConfirmation` takes both from the single
`GoldfishWalk` instance (`Defs/GoldfishWalk.lean`), so confirmation descends the same tree the
fork choice descends and starts where it starts. With the healing layer assembled that is the
round's SG root, over the height-filtered blocks with the grade-0 blocks dropped.

On its own this file would walk from genesis over `Σ.T`. It no longer does, and no reading
of it that does is kept here.

## Extract

Confirmation is the same walk over a stricter vote set and a larger denominator. Let
`early` and `late` be the slot-`s` votes timestamped before `t_s + 2Δ` and before
`t_s + 6Δ`. The walk scores

`votes = {vote ∈ early : vote.validator does not equivocate in late}`

against the participant count of `late`: a validator counts when it voted in time and
no second vote of its has appeared since, while the denominator counts everyone who
voted at all.

Because `early ⊆ late`, a validator equivocating in `early` equivocates in `late` too,
so `votes` holds at most one vote per validator and the score's equivocator clause
never fires here. At most one child can pass the eligibility condition, so the descent
has no choice to make.

A slot is evaluated once, at `t_s + 6Δ`. The result is at worst the tree's own root, never
empty. `Σ.live_confirmed` takes it unconditionally.

Two deviations from that reading are worth naming here rather than leaving a reader to find
them. The slot evaluated is the store's own `Σ.s`, not a parameter, so the `t_s + 6Δ`
precondition that pinned the two together is gone with it. And nothing writes
`Σ.latest_confirmed`: the rule that advanced it, only when the new result descended from the
old, is not rendered.

-/

set_option autoImplicit false

namespace DC

variable {Validator : Type} [Roots] [DecidableEq Validator] [Committees Validator] [Params]

open Params

/-! ## Figure -/
/-- The confirmation walk over `tree`,
    scoring the slot-`s` votes twice filtered. `early` and `late` are the votes processed
    before `t_s + 2Δ` and before `t_s + 6Δ`; what the walk scores is the `early` votes whose
    validator `late` does not catch equivocating, and what it scores them against is the
    number of `late`'s participants.

    The eligibility condition is the majority test alone, without `goldfish_eligible`'s
    current-slot escape — see the module header on why.

    The walk and nothing else: the tree is the caller's, the only store field read is
    `Σ.gf_votes[s]`, and nothing is written. -/
def Store.getGoldfishConfirmation (S : Store Validator) (tree : BlockTree Validator)
    (s : Nat) : NDRE (Block Validator) := do
  let early := {e.vote | e ∈ S.gfVotes[s], e.time < slotStart s + 2 * (Δ : Int)}
  let late := {e.vote | e ∈ S.gfVotes[s], e.time < slotStart s + 6 * (Δ : Int)}
  -- the early votes whose validator `late` does not catch equivocating
  let votes := {vote ∈ early | ¬ ∃ b ∈ late, b.validator = vote.validator ∧ b ≠ vote}
  -- the denominator is `late`'s participants
  let votersCount := |{v ∈ Committees.K s | ∃ a ∈ late, a.validator = v}|
  -- the majority condition, with no current-slot escape — see the module header
  let eligible := fun B => 2 * goldfishScore votes s B > votersCount
  return (← ghost tree (goldfishScore votes s) (fun B => pure (eligible B)))

/-! ## Figure -/
/-- What the node confirms now: the
    walk above, over the layer's own tree, for the store's current slot. The tree comes from
    the `GoldfishWalk` instance, so both where the walk starts and which blocks it may step
    onto are the assembled protocol's — see the module header. -/
def Store.getConfirmation (S : Store Validator) [GoldfishWalk Validator]:
  NDRE (Block Validator) := do
  return (← S.getGoldfishConfirmation (← S.getGoldfishFilteredBlockTree) S.s)

/-! ## Figure -/
/-- Record what the walk confirms:
    `Σ.live_confirmed` takes the result, unconditionally. `Σ.latest_confirmed` is not
    written — see the module header. -/
def Store.updateConfirmation (S : Store Validator) [GoldfishWalk Validator]:
  NDRE (Store Validator) := do
  let mut S := S
  let confirmed ← S.getConfirmation
  S.liveConfirmed ← confirmed
  return S
end DC
