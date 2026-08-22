import Spec.Consensus.Fig2FinalityStore

/-!
# Goldfish votes and slot committees

Definition 4 of the draft, plus the committee assignment it presupposes. The available chain
is Goldfish's; these are its raw votes, separate objects from the attestations of
Definition 3, cast by a slot's committee and counted one unit per member.

The confirmation rule over these votes is the draft's Section 5, which is `[To be drafted.]`
Nothing here anticipates it: this file gives the vote, who may cast one, the store
bookkeeping that records it, and the unit it is counted in — and stops.

## The bookkeeping mirrors the attestation heads

`Σ.gfVote[s][i]` and `Σ.gf_vote_equiv[s][i]` (fields of `Store`, `Fig2FinalityStore.lean`) are
`head[·]` and `equiv[·]` one level down: first write wins, the processing time recorded beside
the value, and a later vote for a different block records the vote-equivocation time instead.
Keyed by **slot**, because a Goldfish vote belongs to a slot where an attestation belongs to a
round. Both fields are beyond Definition 10, which keeps this bookkeeping only for heads
(Roberto, 2026-08-22).

`on_goldfish_vote` below is `on_attestation`'s shape and renders no line of any figure — the
draft's Figure 6 has `on_tick` and `on_attestation` only. Like `on_attestation` it records
whatever arrives without testing eligibility; committee membership is applied where votes are
*counted*, so a non-member's vote occupies its own key and is never read.

## `index` is dropped

Definition 4 as drafted writes a vote as `(index, slot, block)`, signed by "the validator at
index `index` in that slot's committee". That is not rendered, on Roberto's call
(2026-08-22), for two reasons.

**It presupposes an enumerated committee.** Under VRF sortition a validator learns privately
that it was drawn, so nobody holds the committee until the proofs arrive and two observers
hold different subsets at the same instant. There is no function from an index to a
validator, and no way to check that a vote claiming index 3 came from the right signer,
because "the third member" is undefined until the whole committee is known — which is after
the votes have been counted.

**And if the index is signed, aggregation breaks.** A bitfield over committee positions is
what makes BLS aggregation compact, but it works only when every signer signs the *identical*
message: one aggregate signature, plus a bitfield naming the signers. Ethereum's attestations
therefore carry no validator identity in the signed payload. An index inside the signed tuple
gives each member a different message, and aggregate verification over distinct messages
costs a pairing per message — the cost aggregation exists to avoid.

So identity belongs in the envelope, not in the object: the vote below names its signer, and
how signatures are aggregated is not a protocol notion.

## What that leaves open, deliberately

A compact bitfield needs a **publicly computable, ordered** committee — which rules out
private sortition. The three coherent positions, none of which this file takes:

* public deterministic committees, shuffled from a seed, so indices are canonical and the
  bitfield is `|committee|` bits — predictable to an adaptive adversary, mitigated by a short
  lookahead;
* private VRF sortition, unpredictable, with the signer set transmitted explicitly — a
  bitfield over the whole electorate instead, which is orders of magnitude larger;
* indices over the electorate rather than the committee, keeping VRF privacy at the cost of a
  sparse encoding.

If the draft comes to *rely* on cheap aggregation, that is an assumption to state — "committees
are publicly computable and ordered" — and it is not stated here, because nothing yet needs
it.

## Weight plays no part

Definition 4 counts votes "one unit each, independently of weight", so nothing below mentions
`w(·)`: a block's Goldfish support is a count of validators, where an attestation's support is
a sum of weights. Note the consequence for sortition: a committee that is a `Finset` gives
each member exactly one unit, so weighted sortition drawing a validator several times in one
slot is not expressible. That is consistent with Definition 4 as written and would need the
committee to become a multiset, or a count per member, if the draft ever wants Algorand-style
multiple draws.
-/

set_option autoImplicit false

namespace Consensus

variable {Validator : Type}

/-- Each slot's committee: "a known subset of `V`", indexed by the slot. How committees are
    drawn is outside the draft's scope — VRF sortition, a public shuffle, or anything else —
    so the assignment is a class, the way `Electorate` is. -/
class Committees (Validator : Type) where
  /-- The committee of the given slot. -/
  committee : Nat → Finset Validator

/-- A Goldfish vote (Definition 4 of the draft, without its `index` — see the module
    header): its signer, the slot it belongs to, and the block it supports. -/
structure GoldfishVote (Validator : Type) where
  /-- The committee member casting the vote. -/
  validator : Validator
  /-- The slot the vote belongs to. -/
  slot : Nat
  /-- The block the vote supports. -/
  block : Block Validator

/-- The vote was cast by a member of its slot's committee. A vote from a non-member is not a
    Goldfish vote of that slot, and nothing counts it. -/
def GoldfishVote.eligible [DecidableEq Validator] [Committees Validator]
    (v : GoldfishVote Validator) : Prop :=
  v.validator ∈ Committees.committee v.slot

instance [DecidableEq Validator] [Committees Validator] (v : GoldfishVote Validator) :
    Decidable v.eligible :=
  inferInstanceAs (Decidable (_ ∈ _))

/-! ## The handler -/

section Handler
variable [DecidableEq Validator]

/-- `on_goldfish_vote(Σ, v)`: keep, per slot and validator, the first processed vote with its
    processing time, and the time at which a vote for a *different* block from the same
    validator was first processed.

    `on_attestation`'s shape (Figure 6, lines 12–20), and it renders no figure line — see the
    module header. Two differences from that routine, both from Definition 4: a Goldfish vote
    carries a block and not an `Option`, so there is no empty case to ignore; and the key is
    the vote's slot, not a round.

    **Why the result raises** (Roberto, 2026-08-22): the equivocation test reads
    `(← Σ.vote[s][i]).1`, and the row bracket raises when there is no entry. The failure is
    unreachable — the branch above tested `i ∉ Σ.vote[s]` — so it never fires on any store.
    It is the price of reading the recorded block directly rather than through an `Option`
    test, and `on_attestation` pays the same price for the same reason. -/
def onGoldfishVote (S : Store Validator) (v : GoldfishVote Validator) :
    ResultOrExcept (Store Validator) := do
  let mut S := S
  let i := v.validator
  let s := v.slot
  if i ∉ S.gfVote[s] then
    S.gfVote[s][i] ← some { block := v.block, processedAt := S.t }
  else if (← S.gfVote[s][i]).block ≠ v.block ∧ i ∉ S.gfVoteEquiv[s] then
    S.gfVoteEquiv[s][i] ← S.t
  return S

end Handler

/-! ## Counting -/

section Counting
variable [DecidableEq Validator] [Committees Validator]

/-- The committee members whose recorded slot-`s` vote is for `B` and was processed before
    `t`. One entry per validator, so `.card` is Definition 4's count — one unit each, weight
    playing no part.

    The *direct* vote for `B`, not support in Section 5's sense: no ancestor of `B` is
    counted. Whatever closure the confirmation rule wants is that rule's, and it is not
    drafted. The time bound is why `gf_vote[·]` records a processing time at all — Section 5 will
    need to read the same slot at two instants — and this definition takes it as an argument
    rather than fixing one. -/
def Store.voters (S : Store Validator) (s : Nat) (t : Int) (B : Block Validator) :
    Finset Validator :=
  {i ∈ Committees.committee s | (S.gfVote[s] i).any fun rec => rec.processedAt < t ∧ rec.block = B}

/-- The committee members whose slot-`s` vote-equivocation was processed before `t`.
    Figure 4's `equivocators` one level down, and the reason `gf_vote_equiv[·]` exists: a
    validator that voted twice for one slot supplies no unit, and a counting rule that wants
    to exclude it reads this. -/
def Store.voteEquivocators (S : Store Validator) (s : Nat) (t : Int) : Finset Validator :=
  {i ∈ Committees.committee s | (S.gfVoteEquiv[s] i).any fun tE => tE < t}

end Counting

end Consensus
