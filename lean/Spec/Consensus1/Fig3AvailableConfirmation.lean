import Spec.Consensus1.Fig1GoldfishWalk

/-!
# Figure 3 — available confirmation

`update_confirmation(Σ, s)`, run once per slot at `t_s + 6Δ`. "Confirmation is the same walk
over a stricter vote set and a larger denominator."

The `-- line n` comments use Figure 3's own line numbering, in the draft as of 2026-08-22.

## What makes it stricter

Two cutoffs on the same pool. `early` is the slot-`s` votes stamped before `t_s + 2Δ` and
`late` those stamped before `t_s + 6Δ`, so `early ⊆ late`. The walk scores the `early` votes
whose validator has not been *caught equivocating by* `late`, and divides by the participants
of `late`: "a validator counts when it voted in time and no second vote of its has appeared
since; the denominator counts everyone who voted at all".

Two consequences the draft draws, and neither is rendered as a hypothesis because both are
facts about the sets rather than about this routine. Because `early ⊆ late`, a validator
equivocating in `early` equivocates in `late` too, so the scored set holds at most one vote
per validator and `goldfish_score`'s equivocator clause never fires here. And at most one
child can pass the gate, so the descent has no choice to make.

## Why it does not reuse `goldfish_eligible`

The gate at line 6 is the majority test *without* the current-slot escape: the walk runs at
`t_s + 6Δ` over slot-`s` votes, and a block of the current slot has no business being
confirmed for free. So line 6 defines its own `eligible` inline, as the figure does, and the
routine passes it to `ghost` directly rather than going through `goldfish_fork_choice`.

The walk starts at genesis over `Σ.T` — "from genesis over the live tree". At Section 5 the
live tree is `T_F(Σ)`; at this layer nothing has been finalized yet and `Σ.T` is all there
is. Section 5.2 says available confirmation "runs its own walk from `Σ.F` over `T_F(Σ)`", so
the anchor and the tree are the ones this layer has, and the later layer's version of that
sentence is a change to `Σ.F` and `T_F`, not to this routine.
-/

set_option autoImplicit false

namespace Consensus1

namespace Goldfish

variable {Validator : Type} [Roots]

section Confirmation
variable [DecidableEq Validator] [Committees Validator] [TieBreak Validator] [Params]

open Params

/-- `update_confirmation(Σ, s)` (Figure 3, lines 1–10), run at `t_s + 6Δ`: evaluate slot `s`
    once and record what it confirms.

    `Σ.live_confirmed` takes the result unconditionally — it is "the block the last evaluated
    slot confirmed", and an evaluation that walks nowhere leaves genesis, never nothing.
    `Σ.latest_confirmed` only ever moves forward, line 9 testing `Σ.latest_confirmed ⪯ H`.
    `ResultOrExcept` because the walk is; it raises nowhere the walk does not. -/
def updateConfirmation (S : Store Validator) (s : Nat) :
    ResultOrExcept (Store Validator) := do
  let mut S := S
  -- line 2
  let early := {vote ∈ S.gfVotes[s] |
    (S.gfVoteTime vote).any (· < slotStart s + 2 * (Δ : Int))}
  -- line 3
  let late := {vote ∈ S.gfVotes[s] |
    (S.gfVoteTime vote).any (· < slotStart s + 6 * (Δ : Int))}
  -- line 4: the early votes whose validator `late` does not catch equivocating
  let votes := {vote ∈ early |
    ¬ ∃ b ∈ late, b.validator = vote.validator ∧ b ≠ vote}
  -- line 5: the denominator is `late`'s participants
  let votersCount := |{v ∈ (Committees.K s : Finset Validator) |
    ∃ a ∈ late, a.validator = v}|
  -- line 6: the majority gate, with no current-slot escape — see the module header
  let eligible := fun B => 2 * score votes s B > votersCount
  let H ← ghost .genesis S.T (score votes s) eligible           -- line 7
  S.liveConfirmed ← H                                           -- line 8
  if S.latestConfirmed ⪯ H then                                 -- line 9
    S.latestConfirmed ← H                                       -- line 10
  return S

end Confirmation

end Goldfish

end Consensus1
