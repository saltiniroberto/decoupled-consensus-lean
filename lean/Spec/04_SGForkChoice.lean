import Spec.«01_GoldfishWalk»

/-!
# The SG fork choice

`latest`, `sg_support`, `majority_fork_choice`. The SG layer
adds one message layer to Goldfish: a relative-majority fork choice over the latest
SG votes selects a root for the Goldfish walk. The SG vote is the
`(validator, round, confirmed)` projection of a combined attestation (`Model.lean`), and the
pool the rules read is `Σ.attestations[·]`.

## The two walks are one function

`majority_fork_choice` is `ghost` again, with the SG support as the score and a strict
majority of the represented weight as the eligibility condition. Nothing about the walk
changes — the two walks are the same function with different scores and conditions — so this
file instantiates
the shared `ghost` and defines no walk of its own.

## `latest_support_vote` is two definitions here

The protocol's `latest_support_vote(Σ, v, r)` selects the greatest eligible round and then
answers only when that round holds exactly one distinct SG vote by `v`. This file renders
it as the protocol's earlier two pieces: `latest`, the round selection, and the uniqueness
test inlined in `sg_support`'s set — the composition is the same function, and no reader
wants the projection as a value.

## The equivocator consequence is a fact, not a hypothesis

What "represented" and "supports" mean is the Extract prose below. The consequence the
protocol draws — an equivocator supplies no support but stays in the denominator, so
equivocating weight can only raise the bar and two conflicting children cannot both
pass — makes the descent uniquely determined, and it is a fact about the definition
rather than a hypothesis of it.

## Ancestry is read in the live tree

`sg_support` tests `B ⪯ H` on the block itself, with no reference to the `tree` the walk
is running over — the two are deliberately different views, and passing `tree` to the
walk does not narrow what counts as support.

## Extract

SG means stabilization gadget. This intermediate protocol adds one message layer to
Goldfish: a relative-majority fork choice over the latest SG votes selects the root
from which the Goldfish walk starts.

For a fixed integer `R ≥ 1`, round r consists of the R slots from rR on, and
`round(s) = ⌊s/R⌋`. Each round has one SG vote time `a_r = t_{rR} + 6Δ`, `6Δ` after the
beginning of the round. An SG vote is the tuple `(v, r, H)` from validator `v ∈ V` with
confirmed block `H`, a block or `⊥` — the projection of the round's combined attestation, which is
what travels. A round-`r` vote is read from round `r + 1` on.

## Extract — Definition (Latest vote, support, and majority root)

Fix an expiry window `ηSG ≥ 1` in rounds. `latest(Σ, v, r)` is the greatest round `k`
with `max(0, r − ηSG) ≤ k < r` whose `attestations[k]` holds a *resolved* attestation by
`v`, or `⊥` when there is none. A validator with a latest round is represented in that
round's reading; the denominator below is wider still. It supports a block only when its
latest round holds exactly one distinct SG vote by it, and that vote's confirmed block is
named.
An equivocating latest round therefore supplies
no support and, because only the latest round is read, also silences every older vote;
a later clean round restores support.

`sg_support(Σ, r, B)` is the weight supporting `B`. The entire represented
weight is

`W_r = w({v ∈ V : some round of the window holds an attestation by v})`

— any attestation at all, resolved or not, an empty confirmed block included. Ancestry is
read in the live tree `T`, so a confirmed block outside a restricted child tree still
supports the child through which it descends. `majority_fork_choice` runs the walk with
this score, the eligibility condition a strict majority of `W_r`. An equivocator
supplies no support but stays in the denominator, so equivocating weight can only raise
the bar, and two conflicting children cannot both pass: the descent is uniquely
determined.

## Extract

The composed head runs Goldfish from the majority root instead of genesis: the SG walk
selects the anchor, and the Goldfish walk selects a descendant of it. The two walks are
the same function with different scores and eligibility conditions.

-/

set_option autoImplicit false

namespace DC

variable {Validator : Type} [BlockIds] [BlockIdentity Validator] [DecidableEq Validator] [Electorate Validator]
  [Params]

open Params

/-! ## Figure -/
/-- The greatest round in
    `[max{0, r − ηSG}, r)` whose pool holds a *resolved* attestation by `v`, or `⊥` when
    there is none — an unresolved vote leaves its round ineligible, however late it is.

    The window is half-open at `r`: "a round-`r` vote is read from round `r + 1` on". -/
def Store.latest (S : Store Validator) (v : Validator) (r : Nat) : Option Nat :=
  -- the greatest eligible round; `Finset.max` answers `⊥` when there is none
  let eligible := ({k ∈ Finset.range r |
    max 0 (r - ηSG) ≤ k ∧ ∃ e ∈ S.attestations[k],
      e.vote.validator = v ∧ S.resolvedAtt e.vote})
  eligible.max

/-! ## Figure -/
/-- The weight supporting `B`.

    A validator supports `B` when its latest round holds *exactly one* distinct SG vote by
    it — one distinct confirmed block across its stored attestations there, the pair fields
    playing no part — that block is named, and `B` precedes it.

    The figure's loop builds a set by an order-free conditional add, so the loop *is* the
    set it builds, written as the set-builder. Its `k ← latest(Σ, v, r)` binds out of an
    `Option` that the loop's own `latest(Σ, v, r) ≠ ⊥` test has vouched for; the
    `∃ k, … = some k` form says it without a dependent `if`. -/
def Store.sgSupport (S : Store Validator) (r : Nat) (B : BlockId) : Nat :=
  -- as the set the loop builds
  w({v ∈ Electorate.V |
      ∃ k, S.latest v r = some k ∧
        ∃ a ∈ S.attestations[k], a.vote.validator = v ∧
          (∀ b ∈ S.attestations[k], b.vote.validator = v → b.vote.confirmed = a.vote.confirmed) ∧
          ∃ C, a.vote.confirmed = some C ∧ B ⪯[S] C})

/-! ## Figure -/
/-- The shared walk with
    the SG support as its score, eligibility a strict majority of the represented weight —
    spelled independently of `latest`: any attestation of the window counts its sender,
    resolved or not, an empty confirmed block included. -/
def Store.majorityForkChoice (S : Store Validator) (anchor : BlockId)
    (tree : Finset BlockId) (r : Nat) : NDRE BlockId :=
  let total := w({v ∈ Electorate.V | ∃ k ∈ Finset.range r,
    max 0 (r - ηSG) ≤ k ∧ ∃ e ∈ S.attestations[k], e.vote.validator = v})
  let eligible := fun B => 2 * S.sgSupport r B > total
  -- the pure condition offered to the walk's raising slot with `pure`
  S.ghost {root := anchor, blocks := tree } (S.sgSupport r) (fun B => pure (eligible B))

end DC
