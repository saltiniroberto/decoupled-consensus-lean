import Spec.«01GoldfishWalk»

/-!
# Figure 4 — the SG fork choice

`latest`, `sg_support`, `majority_fork_choice`, and the SG layer's `get_head`. The SG
layer adds one message layer to Goldfish: a relative-majority fork choice over the latest
SG votes selects the root from which the Goldfish walk starts.

The `-- line n` comments number the algorithm's lines.

## The two walks are one function

`majority_fork_choice` is `ghost` again, with the SG support as the score and a strict
majority of the represented weight as the gate. Nothing about the walk changes — "the two
walks are the same function with different scores and gates" — so this file instantiates the
`ghost` of Figure 1 and defines no walk of its own.

## What "represented" means, and why an equivocator raises the bar

A validator with a latest round is *represented*: "it counts
in the denominator whatever its votes say". It *supports* a block only when its latest round
holds exactly one distinct vote by it and that vote's head is a block. So an empty or
equivocating latest round supplies no support and, because only the latest round is read,
"also silences every older head; a later clean round restores support".

The consequence the protocol draws: an equivocator supplies no support but stays in the
denominator, so equivocating weight can only raise the bar, and two conflicting children
cannot both pass. That is what makes the descent uniquely determined, and it is a fact about
the definition rather than a hypothesis of it.

## Ancestry is read in the live tree

"Ancestry is read in the live tree `T`, so a head outside a restricted child tree still
supports the child through which it descends." So `sg_support` tests `B ⪯ H` on the block
itself, with no reference to the `tree` the walk is running over — the two are deliberately
different views, and passing `tree` to the walk does not narrow what counts as support.

## Extract

SG means stabilization gadget. This intermediate protocol adds one message layer to
Goldfish: a relative-majority fork choice over the latest SG votes selects the root
from which the Goldfish walk starts.

For a fixed integer `R ≥ 1`, round r consists of the R slots from rR on, and
`round(s) = ⌊s/R⌋`. Each round has one SG vote time `a_r`, a public parameter in this
intermediate protocol. A round-`r` vote is read from round `r + 1` on.

## Extract — Definition (Latest vote, support, and majority root)

Fix an expiry window `ηSG ≥ 1` in rounds. `latest(Σ, v, r)` is the greatest round `k`
with `max(0, r − ηSG) ≤ k < r` whose `sg_votes[k]` holds a vote by `v`, or `⊥` when
there is none. A validator with a latest round is represented: it counts in the
denominator whatever its votes say. It supports a block only when its latest round
holds exactly one distinct vote by it and that vote's head is a block. An empty or
equivocating latest round therefore supplies no support and, because only the latest
round is read, also silences every older head; a later clean round restores support.

`sg_support(Σ, r, B)` is the represented weight supporting `B`. Ancestry is read in the
live tree `T`, so a head outside a restricted child tree still supports the child
through which it descends. `majority_fork_choice` runs the walk with this score, the
eligibility condition a strict majority of the entire represented weight. An
equivocator supplies no support but stays in the denominator, so equivocating weight
can only raise the bar, and two conflicting children cannot both pass: the descent is
uniquely determined.

-/

set_option autoImplicit false

namespace Consensus1

variable {Validator : Type} [Roots] [DecidableEq Validator] [Electorate Validator]
  [Committees Validator] [Params]

open Params

/-- `latest(Σ, v, r)`: the greatest round in
    `[max{0, r − ηSG}, r)` whose SG votes hold one by `v`, or `⊥` when there is none.

    The window is half-open at `r`: "a round-`r` vote is read from round `r + 1` on".

    ## Extract -/
def Store.latest (S : Store Validator) (v : Validator) (r : Nat) : Option Nat :=
  -- lines 2-5: the greatest eligible round; `Finset.max` answers `⊥` when there is none
  let eligible := ({k ∈ Finset.range r |
    max 0 (r - ηSG) ≤ k ∧ ∃ a ∈ S.sgVotes[k], a.validator = v})
  eligible.max

/-- `sg_support(Σ, r, B)`: the represented weight supporting `B`.

    A validator supports `B` when its latest round holds *exactly one* distinct vote by it,
    that vote's head is a block, and `B` precedes the head.

    Lines 7–12 build a set by an order-free conditional add, so the loop *is* the set it
    builds, written as the set-builder. Line 9's `k ← latest(Σ, v, r)` binds out of an
    `Option` the line-8 test has vouched for; the `∃ k, … = some k` form says it without a
    dependent `if`.

    ## Extract -/
def Store.sgSupport (S : Store Validator) (r : Nat) (B : Block Validator) : Nat :=
  -- lines 7–12, as the set the loop builds
  w({v ∈ Electorate.V |
      ∃ k, S.latest v r = some k ∧
        ∃ a ∈ S.sgVotes[k], a.validator = v ∧
          (∀ b ∈ S.sgVotes[k], b.validator = v → b = a) ∧
          ∃ H, a.head = some H ∧ B ⪯ H})

/-- `majority_fork_choice(Σ, anchor, tree, r)`: the shared walk with
    the SG support as its score, gated on a strict majority of the represented weight.

    ## Extract -/
def Store.majorityForkChoice (S : Store Validator) (anchor : Block Validator)
    (tree : Finset (Block Validator)) (r : Nat) : NDRE (Block Validator) :=
  let total := w({v ∈ Electorate.V | S.latest v r ≠ ⊥})       -- line 14
  let eligible := fun B => 2 * S.sgSupport r B > total         -- line 15
  -- line 16; the pure condition offered to the walk's raising slot with `pure`
  ghost anchor tree (S.sgSupport r) (fun B => pure (eligible B))

/-- `get_head(Σ, votes, s)`: the SG walk selects the anchor from
    genesis over the whole processed tree, and the Goldfish walk selects a descendant of it.
    Figure 7 redefines it again, over the filtered tree and from the fork-choice root — that
    reading, `S.getHead`, is the protocol's, and this one is Figure 4's.

    ## Extract -/
def Fig4.getHead (S : Store Validator) (votes : Finset (GoldfishVote Validator)) (s : Nat) :
    NDRE (Block Validator) := do
  let anchor ← S.majorityForkChoice .genesis S.T (round S.s)    -- line 18
  S.goldfishForkChoice anchor S.T votes s                       -- line 19

end Consensus1
