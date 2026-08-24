import Spec.«01GoldfishWalk»

/-!
# Figure 3 — available confirmation

`update_confirmation(Σ, s)`, run once per slot at `t_s + 6Δ`. "Confirmation is the same walk
over a stricter vote set and a larger denominator."

The `-- line n` comments number the algorithm's lines.

## What makes it stricter

Two cutoffs on the same pool, `early ⊆ late`; the walk scores the `early` votes whose
validator `late` has not caught equivocating, against `late`'s participants — the rule
itself is the Extract prose below. The two consequences the protocol draws there — the
scored set holds at most one vote per validator, and at most one child can pass the
eligibility condition — are facts about the sets rather than about this routine, so
neither is rendered as a hypothesis.

## Why it does not reuse `goldfish_eligible`

The gate at line 6 is the majority test *without* the current-slot escape: the walk runs at
`t_s + 6Δ` over slot-`s` votes, and a block of the current slot has no business being
confirmed for free. So line 6 defines its own `eligible` inline, as the figure does, and the
routine passes it to `ghost` directly rather than going through `goldfish_fork_choice`.

The walk starts at genesis over `Σ.T` — from genesis over the live tree. Once the
finality layer exists the live tree is `T_F(Σ)`; at this layer nothing has been finalized
yet and `Σ.T` is all there is. The finality layer runs available confirmation's walk from
`Σ.F` over `T_F(Σ)`, so its version of this rule is a change to `Σ.F` and `T_F`, not to
this routine.

## Extract

Confirmation is the same walk over a stricter vote set and a larger denominator. Let
`early` and `late` be the slot-`s` votes timestamped before `t_s + 2Δ` and before
`t_s + 6Δ`. The walk scores `votes = {vote ∈ early : vote.validator does not equivocate
in late}` against the participant count of `late`: a validator counts when it voted in
time and no second vote of its has appeared since, while the denominator counts
everyone who voted at all.

Because `early ⊆ late`, a validator equivocating in `early` equivocates in `late` too,
so `votes` holds at most one vote per validator and the score's equivocator clause
never fires here. At most one child can pass the eligibility condition, so the descent
has no choice to make.

Slot `s` is evaluated once, at `t_s + 6Δ`, from genesis over the live tree. The result
is at worst genesis, never empty. `Σ.live_confirmed` takes the result unconditionally;
`Σ.latest_confirmed` only ever moves forward.

-/

set_option autoImplicit false

namespace Consensus1

variable {Validator : Type} [Roots] [DecidableEq Validator] [Committees Validator] [Params]

open Params

/-- `update_confirmation(Σ, s)`, run at `t_s + 6Δ`: evaluate slot `s`
    once and record what it confirms.

    `Σ.live_confirmed` takes the result unconditionally — it is "the block the last evaluated
    slot confirmed", and an evaluation that walks nowhere leaves genesis, never nothing.
    `Σ.latest_confirmed` only ever moves forward, line 9 testing `Σ.latest_confirmed ⪯ H`.

    Both cutoffs read the timestamps with the raising bracket, through `Finset.filterM`
: a held vote the store never stamped raises rather than silently
    failing the cutoff. `process_goldfish_vote` stamps everything it stores, so the raise
    marks a store the handlers cannot build — a coherence fact for `Analysis/`.

    "Run at `t_s + 6Δ`" — slot `s`'s own start — is an input precondition, as the Figure 2
    duties' instants are.

    ## Extract -/
def Store.updateConfirmation (S : Store Validator) (s : Nat)
    (_ : S.t = slotStart s + 6 * (Δ : Int) := by solve_by_elim [And.left, And.right]) :
    NDRE (Store Validator) := do
  let mut S := S
  -- line 2
  let early ← {vote ∈ᴹ S.gfVotes[s] | (← S.gfVoteTime[vote]) < slotStart s + 2 * (Δ : Int)}
  -- line 3
  let late ← {vote ∈ᴹ S.gfVotes[s] | (← S.gfVoteTime[vote]) < slotStart s + 6 * (Δ : Int)}
  -- line 4: the early votes whose validator `late` does not catch equivocating
  let votes := {vote ∈ early | ¬ ∃ b ∈ late, b.validator = vote.validator ∧ b ≠ vote}
  -- line 5: the denominator is `late`'s participants
  let votersCount := |{v ∈ Committees.K s | ∃ a ∈ late, a.validator = v}|
  -- line 6: the majority gate, with no current-slot escape — see the module header
  let eligible := fun B => 2 * goldfishScore votes s B > votersCount
  let H ← ghost .genesis S.T (goldfishScore votes s) (fun B => pure (eligible B))  -- line 7
  S.liveConfirmed ← H                                           -- line 8
  if S.latestConfirmed ⪯ H then                                 -- line 9
    S.latestConfirmed ← H                                       -- line 10
  return S



end Consensus1
