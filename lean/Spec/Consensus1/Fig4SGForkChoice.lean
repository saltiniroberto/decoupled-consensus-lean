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

namespace SG

variable {Validator : Type}

section ForkChoice
variable [DecidableEq Validator] [Electorate Validator] [Committees Validator]
  [Selection Validator] [Params]

open Params

/-- `latest(Σ, v, r)` (Figure 4, lines 1–5): the greatest round in
    `[max{0, r − ηSG}, r)` whose SG votes hold one by `v`, or `⊥` when there is none.

    The window is half-open at `r`: "a round-`r` vote is read from round `r + 1` on". -/
def latest (S : Store Validator) (v : Validator) (r : Nat) : Option Nat :=
  -- line 2
  let eligible := {k ∈ Finset.range r |
    max 0 (r - ηSG) ≤ k ∧ ∃ a ∈ S.sgVotes[k], a.validator = v}
  if h : eligible.Nonempty then
    some (eligible.max' h)                                     -- line 5
  else
    ⊥                                                          -- line 4

/-- The *represented* validators: those with a latest round. `W_r` of Definition 3 is the
    weight of this set, and it is both the denominator of the gate and what line 8 of
    `sg_support` iterates over. -/
def represented (S : Store Validator) (r : Nat) : Finset Validator :=
  {v ∈ (Electorate.V : Finset Validator) | (latest S v r).isSome}

/-- `sg_support(Σ, r, B)` (Figure 4, lines 6–12): the represented weight supporting `B`.

    A validator supports `B` when its latest round holds *exactly one* distinct vote by it,
    that vote's head is a block, and `B` precedes the head. Lines 7–11 build the supporter set
    and line 12 weighs it.

    Rendered as a filter rather than the figure's loop: a `Finset` has no computable loop, and
    the loop only ever adds to a set, so the two agree. -/
def support (S : Store Validator) (r : Nat) (B : Block Validator) : Nat :=
  -- lines 8–11, as one condition on `v`
  w({v ∈ represented S r |
      ∃ k, latest S v r = some k ∧
        ∃ a ∈ S.sgVotes[k], a.validator = v ∧
          (∀ b ∈ S.sgVotes[k], b.validator = v → b = a) ∧
          ∃ H, a.head = some H ∧ B ⪯ H})

/-- `majority_fork_choice(Σ, anchor, tree, r)` (Figure 4, lines 13–16): the shared walk with
    the SG support as its score, gated on a strict majority of the represented weight. -/
def majorityForkChoice (S : Store Validator) (anchor : Block Validator)
    (tree : Finset (Block Validator)) (r : Nat) : Block Validator :=
  let total := w(represented S r)                              -- line 14
  ghost anchor tree (support S r) (fun B => 2 * support S r B > total)  -- lines 15–16

/-- `get_head(Σ, votes, s)` (Figure 4, lines 17–19): the SG walk selects the anchor from
    genesis over the whole processed tree, and the Goldfish walk selects a descendant of it.

    This is the SG layer's head. Figure 7 redefines it again, over the filtered tree and from
    the fork-choice root; that one is the protocol's. -/
def getHead (S : Store Validator) (votes : Finset (GoldfishVote Validator)) (s : Nat) :
    Block Validator :=
  let anchor := majorityForkChoice S .genesis S.T (round S.s)   -- line 18
  Goldfish.forkChoice S anchor S.T votes s                      -- line 19

end ForkChoice

end SG

end Consensus1
