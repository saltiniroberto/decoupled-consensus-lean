import Spec.Consensus.Model

/-!
# Goldfish votes and slot committees

Definition 4 of the draft, plus the committee assignment it presupposes. The available chain
is Goldfish's; these are its raw votes, separate objects from the attestations of
Definition 3, cast by a slot's committee and counted one unit per member.

The confirmation rule over these votes is the draft's Section 5, which is `[To be drafted.]`
Nothing here anticipates it: this file gives the vote, who may cast one, and the unit it is
counted in, and stops.

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

section Counting
variable [DecidableEq Validator] [Committees Validator]

/-- The vote was cast by a member of its slot's committee. A vote from a non-member is not a
    Goldfish vote of that slot, and nothing counts it. -/
def GoldfishVote.eligible (v : GoldfishVote Validator) : Prop :=
  v.validator ∈ Committees.committee v.slot

instance (v : GoldfishVote Validator) : Decidable v.eligible :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- The committee members who voted for `B` in slot `s`, among the votes in `A`. One entry
    per validator however many of its votes are in `A`, so `.card` is Definition 4's count —
    one unit each, weight playing no part.

    This is the *direct* vote for `B`, not support in Section 5's sense: no ancestor of `B`
    is counted here. Whatever closure the confirmation rule wants is that rule's, and it is
    not drafted. -/
def votersFor (A : Finset (GoldfishVote Validator)) (s : Nat) (B : Block Validator) :
    Finset Validator :=
  ({v ∈ A | v.eligible ∧ v.slot = s ∧ v.block = B}).image GoldfishVote.validator

end Counting

end Consensus
