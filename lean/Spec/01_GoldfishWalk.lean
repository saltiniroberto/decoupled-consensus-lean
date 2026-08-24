import Spec.Defs.Store
import Spec.Defs.Nondet

/-!
# Figure 1 — the Goldfish score and the walk

`goldfish_score`, `ghost`, `goldfish_eligible`, `goldfish_fork_choice` and `get_head`.
`ghost` is the protocol's one building block: every later fork choice is the same walk
with a different score and eligibility condition.

## The protocol defines incrementally; the old readings are figure-named

Later figures redefine three routines — `get_head` (Figures 1, 4, 7), `process_block`
(Figures 2, 7), `goldfish_eligible` (Figures 1, 7). The last reading of each is the
protocol's and bears the plain `Store` name (`S.getHead`, `S.processBlock`,
`S.goldfishEligible`, all Figure 7's); each superseded reading is named by the figure that
defined it — `Fig1.getHead`, `Fig1.goldfishEligible`, `Fig4.getHead`, `Fig2.processBlock` —
so a call to an old reading says so in the protocol's own coordinates.

There are no namespace blocks: every definition carries its full name at its own `def`.
The full naming scheme is `doc/naming.md`.

## The arg-max step: the tie is a pick

Line 11 is `arg max score`, "ties by root order". The maximal-score children are a filter;
the tie is a **nondeterministic pick**, `←ᵖ`. The protocol never says what a root is or how one
is computed — only that the tie-break be fixed — so nothing is assumed at all:
every resolution is among the outcomes, a root order being one of them, and "the walk does
not depend on the tie" is a provable singleton statement, not a precondition.

## The walk is `NDRE`

The tie-break picks and the eligibility condition may raise — Figure 7's reads `Σ.σ[B].h` —
so the walk carries `NDRE`, and its `eligible` parameter is `Block → DRE Bool`:
the raising layer passes its condition directly, and the pure layers offer theirs with
`pure`. Line 8 filters the children
through `Finset.filterM` at `DRE`, whose fold instances exist; a per-child
condition in `NDRE` itself would not commute (a pick with no outcomes annihilates where an
error survives), which is why the parameter type is the raising monad, not the full stack.
One notation cost, measured: the figure's `H ← arg max` cannot use the plain arrow, which
the assignment macro claims for pure re-assignment, so the monadic bind is written
`H := (← bestChild …)`.

## The figure's `loop` gets a bound

The figure writes `loop … return H`, which terminates because each step moves to a child and
`tree` is finite. That argument is about the tree being a tree — parent-closed and acyclic —
which is an invariant of `Σ.T` rather than a fact about the `Finset` this routine takes. So
line 7's `loop` is written `for _ in [:|tree|]`: a descent through distinct blocks of
`tree` visits at most `|tree|` of them, so on anything that really is a tree the bound is
never reached and the `for` runs exactly the figure's `loop`.

What the bound costs is one reachable case the protocol does not have: the iterations run out
with an eligible child still available, and the routine returns the block it stands on — the
same answer the figure gives when no child is eligible. `Analysis/` is where "the bound is
never reached on a real tree" belongs. The alternative — a well-founded recursion on the set
of strict descendants — needs the tree invariant in the *definition*, and `Spec/` is not the
place to assume it.

## The score counts equivocators for every block

An equivocator "counts for every block and stays among the participants, so it
can neither create nor block a descent". That is why line 2 collects them separately and line
4 adds both cardinalities: a validator with two votes is added to every block's score without
its target being read at all.

## Extract — Definition (Goldfish score and walk)

Fix a vote slot `s` and a set `votes` of slot-`s` votes. Validator `v ∈ K_s`
equivocates when `votes` holds two of its distinct votes, and participates when it
holds at least one. `goldfish_score(votes, s, B)` counts every equivocator plus every
non-equivocating participant whose target descends from `B`. An equivocator counts for
every block and stays among the participants, so it can neither create nor block a
descent; a non-equivocating validator counts once, in one subtree.

## Extract

Throughout this document, we use this as a building block:

`ghost(anchor, tree, score, eligible)`

where `score` is a function on blocks and `eligible` a predicate on blocks. It descends
from `anchor` through eligible children in `tree`, taking the highest score at each
step, and stops where no child is eligible.

Goldfish instantiates the walk with `goldfish_score(votes, s, ·)` and the eligibility
condition

`2 goldfish_score(votes, s, B) > voters_count or B.slot = Σ.s`

with `voters_count = |{v ∈ K_s : votes holds a vote by v}|`. The majority condition
enforces timeliness; it only does not apply to proposals from the current slot, which
cannot yet have votes. At slot 0 the vote set is empty, no child is eligible, and the
head is genesis.

-/

set_option autoImplicit false

namespace DC

variable {Validator : Type} [Roots] [DecidableEq Validator] [Committees Validator]

/-! ## The shared walk -/

/-- Line 11's `arg max score`: the maximal-score members, the tie a genuine pick — every
    resolution among the outcomes, a root order being one. On empty `children` there are no
    outcomes at all, an answer `ghost`'s line 9 never asks for. -/
def bestChild (children : Finset (Block Validator)) (score : Block Validator → Nat) :
    NDR (Block Validator) := do
  let top := {B ∈ children | ∀ C ∈ children, score C ≤ score B}
  let W ←ᵖ top
  return W

/-- `ghost(anchor, tree, score, eligible)`: descend from `anchor`
    through eligible children in `tree`, taking the highest score at each step, and stop
    where no child is eligible. The tie at each step is a pick; the eligibility condition
    may raise. See the module header on both, and on why `eligible` is `DRE`
    rather than the full stack.

    The figure's `loop` is bounded by `|tree|`.

    ## Extract -/
def ghost (anchor : Block Validator) (tree : Finset (Block Validator))
    (score : Block Validator → Nat) (eligible : Block Validator → DRE Bool) :
    NDRE (Block Validator) := do
  let mut H := anchor
  for _ in [:|tree|] do                                        -- `loop`, bounded
    -- the eligible children of the block we stand on; the filter runs at
    -- `DRE` — the ascription keeps the stack out of it — and lifts whole
    let children ← (({B ∈ tree | B.parent = ↑H}).filterM eligible :
      DRE (Finset (Block Validator)))
    if children = ∅ then
      return H
    -- `H ← arg max score`; the plain arrow is the assignment macro's, so the
    -- monadic bind is written through `:=`
    H := (← bestChild children score)
  return H  -- the bound is reached: not a figure line, see the module header

/-! ## The Goldfish score and eligibility -/

/-- `goldfish_score(votes, s, B)`: every equivocator, plus every
    non-equivocating participant whose target descends from `B`. The equivocator set is a
    `let`, as line 2 writes it — the protocol defines no standalone function.

    An equivocator is counted without its target being read — see the module header.

    ## Extract -/
def goldfishScore (votes : Finset (GoldfishVote Validator)) (s : Nat) (B : Block Validator) :
    Nat :=
  -- `{v ∈ K_s : votes holds two distinct votes by v}`
  let equivocators : Finset Validator := {v ∈ Committees.K s |
    ∃ a ∈ votes, ∃ b ∈ votes, a.validator = v ∧ b.validator = v ∧ a ≠ b}
  -- `{v ∈ K_s \ equivocators : (v, s, B') ∈ votes with B ⪯ B'}`
  let supporters := {v ∈ Committees.K s \ equivocators |
    ∃ a ∈ votes, a.validator = v ∧ B ⪯ a.target}
  |equivocators| + |supporters|

/-- `goldfish_eligible(Σ, votes, s, B)`: a strict majority of the
    participants support `B`, or `B` is a block of the current slot. Figure 7 redefines it
    with a height clause; that reading, `S.goldfishEligible`, is the protocol's, and this one
    is Figure 1's — hence the name.

    Line 13's `voters_count` is a `let`, as the figure writes it — the protocol defines no such
    function, only this local and its Figure 3 and Figure 7 analogues over their own vote
    sets.

    The second disjunct is why a fresh proposal can be walked onto at all: "it only does not
    apply to proposals from the current slot, which cannot yet have votes".

    ## Extract -/
def Fig1.goldfishEligible (S : Store Validator) (votes : Finset (GoldfishVote Validator))
    (s : Nat) (B : Block Validator) : Bool :=
  -- `voters_count ← |{v ∈ K_s : votes holds a vote by v}|`
  let votersCount := |{v ∈ Committees.K s | ∃ a ∈ votes, a.validator = v}|
  2 * goldfishScore votes s B > votersCount ∨ B.slot = S.s

/-- `goldfish_fork_choice(Σ, anchor, tree, votes, s)`: the shared
    walk, instantiated with the Goldfish score and eligibility condition.

    ## Extract -/
def Store.goldfishForkChoice (S : Store Validator) (anchor : Block Validator)
    (tree : Finset (Block Validator)) (votes : Finset (GoldfishVote Validator)) (s : Nat) :
    NDRE (Block Validator) :=
  -- the pure condition offered to the walk's raising slot with `pure`
  ghost anchor tree (goldfishScore votes s) (fun B => pure (Fig1.goldfishEligible S votes s B))

/-- `get_head(Σ, votes, s)`: the walk from genesis over the whole
    processed tree. Figure 4 redefines it to start from the SG root, and Figure 7 again to
    start from the fork-choice root over the filtered tree — that reading, `S.getHead`, is
    the protocol's, and this one is Figure 1's.

    ## Extract -/
def Fig1.getHead (S : Store Validator) (votes : Finset (GoldfishVote Validator)) (s : Nat) :
    NDRE (Block Validator) :=
  S.goldfishForkChoice .genesis S.T votes s

end DC
