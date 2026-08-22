import Spec.Consensus1.Fig1GoldfishWalk

/-!
# Figure 4 — the SG fork choice

Definition 3 and Figure 4: `latest`, `sg_support`, `majority_fork_choice`, and the SG layer's
`get_head`. "This intermediate protocol adds one message layer to Goldfish: a
relative-majority fork choice over the latest SG votes selects the root from which the
Goldfish walk starts."

The `-- line n` comments use Figure 4's own line numbering, in the draft as of 2026-08-22.

## The two walks are one function

`majority_fork_choice` is `ghost` again, with the SG support as the score and a strict
majority of the represented weight as the gate. Nothing about the walk changes — "the two
walks are the same function with different scores and gates" — so this file instantiates the
`ghost` of Figure 1 and defines no walk of its own.

## What "represented" means, and why an equivocator raises the bar

Definition 3, in its own words. A validator with a latest round is *represented*: "it counts
in the denominator whatever its votes say". It *supports* a block only when its latest round
holds exactly one distinct vote by it and that vote's head is a block. So an empty or
equivocating latest round supplies no support and, because only the latest round is read,
"also silences every older head; a later clean round restores support".

The consequence the draft draws: an equivocator supplies no support but stays in the
denominator, so equivocating weight can only raise the bar, and two conflicting children
cannot both pass. That is what makes the descent uniquely determined, and it is a fact about
the definition rather than a hypothesis of it.

## Ancestry is read in the live tree

"Ancestry is read in the live tree `T`, so a head outside a restricted child tree still
supports the child through which it descends." So `sg_support` tests `B ⪯ H` on the block
itself, with no reference to the `tree` the walk is running over — the two are deliberately
different views, and passing `tree` to the walk does not narrow what counts as support.
-/

set_option autoImplicit false

namespace Consensus1

variable {Validator : Type} [Roots]

section ForkChoice
variable [DecidableEq Validator] [Electorate Validator] [Committees Validator]
  [TieBreak Validator] [Params]

open Params

namespace Store

/-- `latest(Σ, v, r)` (Figure 4, lines 1–5): the greatest round in
    `[max{0, r − ηSG}, r)` whose SG votes hold one by `v`, or `⊥` when there is none.

    The window is half-open at `r`: "a round-`r` vote is read from round `r + 1` on". -/
def latest (S : Store Validator) (v : Validator) (r : Nat) : Option Nat :=
  -- lines 2-5: the greatest eligible round; `Finset.max` answers `⊥` when there is none
  let eligible := ({k ∈ Finset.range r |
    max 0 (r - ηSG) ≤ k ∧ ∃ a ∈ S.sgVotes[k], a.validator = v})
  eligible.max

/-- `sg_support(Σ, r, B)` (Figure 4, lines 6–12): the represented weight supporting `B`.

    A validator supports `B` when its latest round holds *exactly one* distinct vote by it,
    that vote's head is a block, and `B` precedes the head.

    Lines 9–10 — `k ← latest(Σ, v, r)`, then the exactly-one-vote test — are one condition
    here: the draft's `k ←` binds out of an `Option` the loop's `with` clause has already
    tested, and `∃ k, S.latest v r = some k ∧ …` says the same thing without a dependent
    `if`. -/
def sgSupport (S : Store Validator) (r : Nat) (B : Block Validator) : Nat := Id.run do
  let mut supporters : Finset Validator := ∅                   -- line 7
  -- line 8: `for all v ∈ V with latest(Σ, v, r) ≠ ⊥ do`
  for all v ∈ Electorate.V with S.latest v r ≠ ⊥ do
    -- lines 9–10, as one condition on `v`; see the docstring
    if ∃ k, S.latest v r = some k ∧
        ∃ a ∈ S.sgVotes[k], a.validator = v ∧
          (∀ b ∈ S.sgVotes[k], b.validator = v → b = a) ∧
          ∃ H, a.head = some H ∧ B ⪯ H then
      supporters ← supporters ∪ {v}                            -- line 11
  return w(supporters)                                         -- line 12

/-- `majority_fork_choice(Σ, anchor, tree, r)` (Figure 4, lines 13–16): the shared walk with
    the SG support as its score, gated on a strict majority of the represented weight. -/
def majorityForkChoice (S : Store Validator) (anchor : Block Validator)
    (tree : Finset (Block Validator)) (r : Nat) : ResultOrExcept (Block Validator) :=
  let total := w({v ∈ Electorate.V | S.latest v r ≠ ⊥})       -- line 14
  ghost anchor tree (S.sgSupport r) (fun B => 2 * S.sgSupport r B > total)  -- lines 15–16

end Store

namespace SG

/-- `get_head(Σ, votes, s)` (Figure 4, lines 17–19): the SG walk selects the anchor from
    genesis over the whole processed tree, and the Goldfish walk selects a descendant of it.

    This is the SG layer's head. Figure 7 redefines it again, over the filtered tree and from
    the fork-choice root; that one is the protocol's. -/
    -- (in `SG`, not `Store`: three layers define a `get_head`, and a namespace holds one)
def getHead (S : Store Validator) (votes : Finset (GoldfishVote Validator)) (s : Nat) :
    ResultOrExcept (Block Validator) := do
  let anchor ← S.majorityForkChoice .genesis S.T (round S.s)    -- line 18
  Goldfish.forkChoice S anchor S.T votes s                      -- line 19

end SG

end ForkChoice

end Consensus1
