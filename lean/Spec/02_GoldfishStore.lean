import Mathlib.Data.Finset.Union
import Spec.«01_GoldfishWalk»
import Spec.Defs.Nondet

/-!
# The Goldfish vote handler

`process_goldfish_vote`, the handler that admits one Goldfish vote into the slot pool
`Σ.gf_votes[·]`. It changes the store in place and broadcasts nothing. The duties that
produce votes — `propose_block`, `goldfish_vote` — and the tick that runs them live in
`11_Duties.lean`, last in the file order because they call the whole specification; this
handler comes early because `process_block` (`07_FGStore.lean`) runs it on every vote a
block carries.

## Extract

`process_goldfish_vote(Σ, vote)` records a slot-`k` vote with its processing time. It
takes the store and changes it in place; nothing is broadcast — the vote reached this
node on the wire or inside a block, and relaying what a node processes is network
behaviour, the wiring layer's to render.

-/

set_option autoImplicit false

namespace DC

variable {Validator : Type} [BlockIds] [BlockIdentity Validator]
  [DecidableEq Validator] [Committees Validator] [Params]

open Params

/-! ## Figure -/
/-- Record a slot-`k` vote with its
    processing time, unless it is from before the previous slot or from the future, from
    a sender outside the slot's
    committee, already held, or a third vote by a validator already seen equivocating.

    The slot window has both ends: a slot-`k` vote is read only in slots `k` and `k + 1`,
    so one older than `Σ.s − 1` is not stored — `Σ.s − 1` in `Nat` subtraction, which at
    `Σ.s = 0` truncates to `0` and rejects nothing, as the protocol's `Σ.s − 1 = −1`
    rejects nothing.

    The committee test is made once, here at admission: every stored vote is a committee
    member's, so no counting rule retests membership.

    The two-votes test is where the protocol's "at most two distinct votes per validator"
    is maintained: "two witness the equivocation; nothing reads a third". -/
def Store.processGoldfishVote (S : Store Validator) (vote : GoldfishVote Validator) :
    Store Validator := Id.run do
  let mut S := S
  if vote.slot < S.s - 1 ∨ vote.slot > S.s ∨ vote.validator ∉ Committees.K vote.slot ∨
      ∃ e ∈ S.gfVotes[vote.slot], e.vote = vote then
    return S
  -- two distinct votes by this validator are already held
  if ∃ a ∈ S.gfVotes[vote.slot], ∃ b ∈ S.gfVotes[vote.slot],
      a.vote.validator = vote.validator ∧ b.vote.validator = vote.validator ∧
      a.vote ≠ b.vote then
    return S
  S.gfVotes[vote.slot] ← S.gfVotes[vote.slot] ∪
    {TimestampedVote.mk (vote := vote) (time := S.t)}
  return S

end DC
