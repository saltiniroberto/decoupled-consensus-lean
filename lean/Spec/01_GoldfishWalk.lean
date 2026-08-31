import Spec.Defs.Store
import Spec.Defs.Nondet

/-!
# The Goldfish score and the walk

`goldfish_score` and `ghost` — the protocol's one building block: every fork choice is
the same walk with a different score and eligibility condition. The conditions live with
their layers (`goldfish_eligible`, `07_FGStore.lean`), and the assembled `get_head` with
the tree it walks (`09_Healing.lean`).

## One definition per routine

Each routine is defined once. Where the protocol's layers build a routine up, the definition
here is the assembled one, and the earlier forms are not rendered: a reader auditing this
spec is auditing the protocol, not its presentation.

`get_head` is written once, `Store.getHead` in `09_Healing.lean`: the walk over a tree — the
anchor its root, the blocks it may step onto — testing an eligibility condition. The tree and
the condition are the healing layer's, which is why it is written there and not here. A duty
writes `S.getHead votes k`.

## The walk steps over identifiers

A block names its parent by identifier, so a tree is a set of identifiers and every walk in
this spec steps from identifier to identifier. `Σ.parent_of` (`Defs/Store.lean`) is where the
parent links are read — `⊥` at genesis, and raising where the store holds nothing, since it
reads through `Σ.T[B]` like every other rule that wants a field of a processed block.

The parameters keep the protocol's letters — `B`, `C`, `H` — even though what each holds is an
identifier, because that is how the figures read and how the protocol writes them.

There are no namespace blocks: every definition carries its full name at its own `def`.
The full naming scheme is `doc/naming.md`.

## The arg-max step: the tie is a pick

The walk's step is `H ← arg max score`, "ties by root order". The maximal-score children are a filter;
the tie is a **nondeterministic pick**, `←ᵖ`. Blocks here carry no root (`Model.lean`),
and the protocol asks only that the tie-break be fixed — so nothing is assumed at all:
every resolution is among the outcomes, the identifier order being one of them, and "the
walk does not depend on the tie" is a provable singleton statement, not a precondition.

## The walk is `NDRE`

The tie-break picks and the eligibility condition may raise — the finality layer's reads
`Σ.σ[B].h` — so the walk carries `NDRE`, and its `eligible` parameter is
`Block → DRE Bool`: the raising layer passes its condition directly, and the pure layers
offer theirs with `pure`. The children step is the raising set-builder
`{B ∈ᴹ …}` (`Notation.lean`), which is `Finset.filterM` at `DRE` with the monad pinned in
the builder rather than at the call: the two conditions the figure states — the parent link
and eligibility — are its one condition, and the whole filter lifts into `NDRE`. A per-child
condition in `NDRE` itself would not commute (a pick with no outcomes annihilates where an
error survives), which is why the parameter type is the raising monad, not the full stack.
The figure's `H ← arg max` keeps an arrow: `H ⇐ bestChild children score`, the
assignment whose right-hand side computes (`Notation.lean`), the second arrowhead saying
that the step picks.

## The figure's `loop` gets a bound

The figure writes `loop … return H`, which terminates because each step moves to a child and
`tree` is finite. That argument is about the tree being a tree — parent-closed and acyclic —
which is an invariant of `Σ.T` rather than a fact about the `Finset` this routine takes. So
the `loop` is written `for _ in [:|tree|]`: a descent through distinct blocks of
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
can neither create nor block a descent". That is why `equivocators` is collected
separately and the score adds both cardinalities: a validator with two votes is added to
every block's score without its target being read at all.

## Extract — Definition (Goldfish score and walk)

Fix a vote slot `s` and a set `votes` of slot-`s` votes. Validator `v`
equivocates when `votes` holds two of its distinct votes, and participates when it
holds at least one. `goldfish_score(votes, s, B)` counts every equivocator plus every
non-equivocating participant whose target descends from `B`. An equivocator counts for
every block and stays among the participants, so it can neither create nor block a
descent; a non-equivocating validator counts once, in one subtree. Membership in `K_s`
is not retested here: `process_goldfish_vote` admits only committee members' votes, so
every stored vote is a member's.

## Extract

Throughout this document, we use this as a building block:

`ghost(tree, score, eligible)`

where `tree` is a root together with a set of blocks, `score` a function on blocks and
`eligible` a predicate on blocks. It descends from the root through eligible blocks of the
set, taking the highest score at each step, and stops where no child is eligible.

Goldfish instantiates the walk with `goldfish_score(votes, s, ·)` and the eligibility
condition

`2 goldfish_score(votes, s, B) > voters_count or B.slot = Σ.s`

with `voters_count = |{v ∈ V : votes holds a vote by v}|`. The majority condition
enforces timeliness; it only does not apply to proposals from the current slot, which
cannot yet have votes. At slot 0 the vote set is empty, no child is eligible, and the
head is genesis.

-/

set_option autoImplicit false

namespace DC

variable {Validator : Type} [BlockIds] [BlockIdentity Validator]
  [DecidableEq Validator] [Electorate Validator]

/-! ## The shared walk -/

/-- The walk's `arg max score`: the maximal-score members, the tie a genuine pick — every
    resolution among the outcomes, a root order being one. On empty `children` there are no
    outcomes at all, an answer `ghost`'s emptiness test never lets it ask for. -/
def bestChild (children : Finset BlockId) (score : (B : BlockId) → Nat) :
    NDR BlockId := do
  let top := {B ∈ children | ∀ C ∈ children, score C ≤ score B}
  let W ←ᵖ top
  return W

/-! ## Figure -/
/-- Descend from `anchor`
    through eligible children in `tree`, taking the highest score at each step, and stop
    where no child is eligible. The tie at each step is a pick; the eligibility condition
    may raise. See the module header on both, and on why `eligible` is `DRE`
    rather than the full stack.

    The figure's `loop` is bounded by `|tree|`. -/
def Store.ghost (S : Store Validator) (tree : BlockTree)
    (score : (B : BlockId) → Nat) (eligible : (B : BlockId) → DRE Bool) :
    NDRE BlockId := do
  let mut H := tree.root
  let blocks := tree.blocks
  for _ in [:|blocks|] do                                        -- `loop`, bounded
    -- the eligible children of the block we stand on
    let children ← {B ∈ᴹ blocks | (← S.parentOf B) = ↑H ∧ (← eligible B)}
    if children = ∅ then
      return H
    -- `H ← arg max score`, the step picking among the maximal-score children
    H ⇐ bestChild children score
  return H  -- the bound is reached: not a figure line, see the module header

/-! ## The Goldfish score and eligibility -/

/-! ## Figure -/
-- `s` is the protocol's own signature and no longer read: membership is the handler's test
set_option linter.unusedVariables false in
/-- Every equivocator, plus every
    non-equivocating participant whose target descends from `B`. The equivocator set is a
    `let`, as the figure writes it — the protocol defines no standalone function.

    An equivocator is counted without its target being read — see the module header.

    **The two sets are not interchangeable.** Equivocation is read off `votes`, every vote the
    node holds; support is read off `support_votes`, the ones that have resolved
    (`Defs/Store.lean`). Collapsing them would hand an equivocator its weight back as weight
    that picks a side: publish two votes, withhold one target, and the surviving vote makes its
    sender an ordinary supporter of one subtree instead of an equivocator counting for every
    block and steering nothing. -/
def Store.goldfishScore (S : Store Validator)
    (votes supportVotes : Finset (GoldfishVote Validator))
    (s : Nat) (B : BlockId) : Nat :=
  -- `{v ∈ V : votes holds two distinct votes by v}`
  let equivocators : Finset Validator := {v ∈ Electorate.V |
    ∃ a ∈ votes, ∃ b ∈ votes, a.validator = v ∧ b.validator = v ∧ a ≠ b}
  -- `{v ∉ equivocators : (v, s, B') ∈ support_votes with B ⪯ B'}`
  let supporters := {v ∈ Electorate.V \ equivocators |
    ∃ a ∈ supportVotes, a.validator = v ∧ B ⪯[S] a.target}
  |equivocators| + |supporters|

end DC
