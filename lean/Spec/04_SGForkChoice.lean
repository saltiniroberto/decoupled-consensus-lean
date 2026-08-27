import Spec.«01_GoldfishWalk»

/-!
# The SG fork choice

`latest`, `sg_support`, `majority_fork_choice`, and the SG layer's `get_head`. The SG
layer adds one message layer to Goldfish: a relative-majority fork choice over the latest
SG votes selects the root from which the Goldfish walk starts.

## The two walks are one function

`majority_fork_choice` is `ghost` again, with the SG support as the score and a strict
majority of the represented weight as the gate. Nothing about the walk changes — "the two
walks are the same function with different scores and gates" — so this file instantiates
the shared `ghost` and defines no walk of its own.

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
beginning of the round. An SG vote is a tuple `(v, r, H)` from validator `v ∈ V` with
head `H`, a block or `⊥`; at `a_r`, an honest validator votes its current
`live_confirmed`, which is a block. A round-`r` vote is read from round `r + 1` on.

## Extract — Definition (Latest vote, support, and majority root)

Fix an expiry window `ηSG ≥ 1` in rounds. `latest(Σ, v, r)` is the greatest round `k`
with `max(0, r − ηSG) ≤ k < r` whose `sg_votes[k]` holds a vote by `v`, or `⊥` when
there is none. Only votes whose head is a block are stored, so an empty-headed vote
leaves no trace. A validator with a latest round is represented: it counts in the
denominator whatever its votes say. It supports a block only when its latest round
holds exactly one distinct vote by it. An equivocating latest round therefore supplies
no support and, because only the latest round is read, also silences every older head;
a later clean round restores support.

`sg_support(Σ, r, B)` is the represented weight supporting `B`. The entire represented
weight is

`W_r = w({v ∈ V : latest(Σ, v, r) ≠ ⊥})`

Ancestry is read in the live tree `T`, so a head outside a restricted child tree still
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

variable {Validator : Type} [Roots] [DecidableEq Validator] [Electorate Validator]
  [Committees Validator] [Params]

open Params

/-! ## Figure -/
/-- The greatest round in
    `[max{0, r − ηSG}, r)` whose SG votes hold one by `v`, or `⊥` when there is none.

    The window is half-open at `r`: "a round-`r` vote is read from round `r + 1` on". -/
def Store.latest (S : Store Validator) (v : Validator) (r : Nat) : Option Nat :=
  -- the greatest eligible round; `Finset.max` answers `⊥` when there is none
  let eligible := ({k ∈ Finset.range r |
    max 0 (r - ηSG) ≤ k ∧ ∃ e ∈ S.sgVotes[k], e.vote.validator = v})
  eligible.max

/-! ## Figure -/
/-- The represented weight supporting `B`.

    A validator supports `B` when its latest round holds *exactly one* distinct vote by it,
    that vote's head is a block, and `B` precedes the head.

    The figure's loop builds a set by an order-free conditional add, so the loop *is* the
    set it builds, written as the set-builder. Its `k ← latest(Σ, v, r)` binds out of an
    `Option` that the loop's own `latest(Σ, v, r) ≠ ⊥` test has vouched for; the
    `∃ k, … = some k` form says it without a dependent `if`. -/
def Store.sgSupport (S : Store Validator) (r : Nat) (B : Block Validator) : Nat :=
  -- as the set the loop builds
  w({v ∈ Electorate.V |
      ∃ k, S.latest v r = some k ∧
        ∃ a ∈ S.sgVotes[k], a.vote.validator = v ∧
          (∀ b ∈ S.sgVotes[k], b.vote.validator = v → b.vote = a.vote) ∧
          B ⪯ a.vote.head})

/-! ## Figure -/
/-- The shared walk with
    the SG support as its score, gated on a strict majority of the represented weight. -/
def Store.majorityForkChoice (S : Store Validator) (anchor : Block Validator)
    (tree : Finset (Block Validator)) (r : Nat) : NDRE (Block Validator) :=
  let total := w({v ∈ Electorate.V | S.latest v r ≠ ⊥})
  let eligible := fun B => 2 * S.sgSupport r B > total
  -- the pure condition offered to the walk's raising slot with `pure`
  ghost {root := anchor, blocks := tree } (S.sgSupport r) (fun B => pure (eligible B))

/-! ## Figure -/
/-- The SG walk selects the anchor from
    genesis over the whole processed tree, and the Goldfish walk selects a descendant of it.
    The finality layer redefines it again, over the filtered tree and from the fork-choice
    root — that reading is the protocol's, reached as `S.getHead`, and this one is this
    file's. -/
def Fig4.getHead (S : Store Validator) (votes : Finset (GoldfishVote Validator)) (s : Nat) :
    NDRE (Block Validator) := do
  let anchor ← S.majorityForkChoice .genesis S.T (round S.s)
  S.goldfishForkChoice {root := anchor, blocks := S.T} votes s

end DC
