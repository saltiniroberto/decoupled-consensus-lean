import Spec.Consensus1.Fig4SGForkChoice

/-!
# Figure 5 — the SG duty and store handler

`sg_vote`, run at the round's vote time `a_r`, and `process_sg_vote`.

The `-- line n` comments use Figure 5's own line numbering, in the draft as of 2026-08-22.

## What Section 3.4 changes in Figure 2, and what this file does about it

"`on_tick` gains one line: at `t = a_r` for the current round `r`, run `sg_vote`. The proposer
and voter of Figure 2 call the `get_head` of Figure 4; nothing else in their duties changes.
Available confirmation is unchanged."

Neither the extra `on_tick` line nor the redirected `get_head` is rendered here, and both for
the same reason: Section 5 changes the same two places again, and its version is the
protocol's. `Fig7FGStore.lean` carries the final `on_tick` and the final `get_head`. What this
file holds is the two routines Figure 5 itself introduces — which Section 5 does not touch.

`a_r` is "a public parameter in this intermediate protocol", not a function of `r` the draft
fixes, so `sg_vote`'s caller decides when to run it, exactly as it decides who proposes.

## An honest vote is never empty

"At `a_r`, an honest validator votes its current `live_confirmed`, which is a block; the empty
head appears only in adversarial votes here, and in the timeout votes of the graded protocol."
So line 3 always names a block, and `SGVote.head` is an `Option` only because the wire object
admits `⊥` — nothing an honest duty produces uses it.
-/

set_option autoImplicit false

namespace Consensus1

namespace SG

variable {Validator : Type} [Roots]

section Duty
variable [DecidableEq Validator] [Params]

/-- `process_sg_vote(Σ, vote)` (Figure 5, lines 5–10): record a round-`r` SG vote with its
    processing time, unless it is from a future round, already held, or a third vote by a
    validator already seen equivocating.

    `process_goldfish_vote`'s shape exactly, one field over: the round test is against
    `round(Σ.s)` rather than `Σ.s`, and line 8 is where "at most two distinct votes per
    validator" is maintained — "two witness the equivocation; nothing reads a third". -/
def processSGVote (S : Store Validator) (vote : SGVote Validator) :
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
  S.sgVoteTime[vote] ← some S.t
  return S

/-- `sg_vote(Σ)` (Figure 5, lines 1–4), run at `a_r`: vote the store's current
    `live_confirmed` for the current round.

    Returns the vote it would broadcast alongside the store that has processed it, as the
    Goldfish duties do; see `Fig2GoldfishDuties.lean` on why the broadcast is not modelled. -/
def sgVote (i : Validator) (S : Store Validator) :
    SGVote Validator × Store Validator := Id.run do
  let r := round S.s                                           -- line 2
  let vote : SGVote Validator := ⟨i, r, some S.liveConfirmed⟩   -- line 3
  return (vote, processSGVote S vote)                          -- line 4

end Duty

end SG

end Consensus1
