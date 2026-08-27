import Spec.Defs.Store
import Spec.Defs.Nondet
import Spec.Defs.GoldfishWalk

/-!
# The Goldfish score and the walk

`goldfish_score`, `ghost`, `goldfish_eligible`, `goldfish_fork_choice` and `get_head`.
`ghost` is the protocol's one building block: every later fork choice is the same walk
with a different score and eligibility condition.

## The protocol defines incrementally; the old readings are numbered

Later files redefine three routines — `get_head` (files `01`, `04`, `07`, `09`),
`process_block` (`02`, `07`), `goldfish_eligible` (`01`, `07`). Each superseded reading is
named by the number of the file that defines it — `Fig1.getHead`, `Fig4.getHead`,
`Fig7.getHead`, `Fig1.goldfishEligible`, `Fig2.processBlock` — so a call names the reading it
makes.

`get_head` is the one a duty must not name, since the duties outlive every reading of it. So
it is written once, `Store.getHead` at the end of this file: the walk over a tree — the
anchor its root, the blocks it may step onto — testing an eligibility condition. Those two
come from `GoldfishWalk`
(`Defs/GoldfishWalk.lean`), whose single instance the layer owning the protocol's readings
supplies — the healing layer, which is why there is no `Fig9.getHead`: that layer's reading
*is* its instance. A duty writes `S.getHead votes k` and means whatever the assembled
protocol's fork choice is.

There are no namespace blocks: every definition carries its full name at its own `def`.
The full naming scheme is `doc/naming.md`.

## The arg-max step: the tie is a pick

The walk's step is `H ← arg max score`, "ties by root order". The maximal-score children are a filter;
the tie is a **nondeterministic pick**, `←ᵖ`. The protocol never says what a root is or how one
is computed — only that the tie-break be fixed — so nothing is assumed at all:
every resolution is among the outcomes, a root order being one of them, and "the walk does
not depend on the tie" is a provable singleton statement, not a precondition.

## The walk is `NDRE`

The tie-break picks and the eligibility condition may raise — the finality layer's reads
`Σ.σ[B].h` — so the walk carries `NDRE`, and its `eligible` parameter is
`Block → DRE Bool`: the raising layer passes its condition directly, and the pure layers
offer theirs with `pure`. The children filter runs
through `Finset.filterM` at `DRE`, whose fold instances exist; a per-child
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

/-- The walk's `arg max score`: the maximal-score members, the tie a genuine pick — every
    resolution among the outcomes, a root order being one. On empty `children` there are no
    outcomes at all, an answer `ghost`'s emptiness test never lets it ask for. -/
def bestChild (children : Finset (Block Validator)) (score : (B : Block Validator) → Nat) :
    NDR (Block Validator) := do
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
def ghost (tree :  BlockTree Validator)
    (score : (B : Block Validator) → Nat) (eligible : (B : Block Validator) → DRE Bool) :
    NDRE (Block Validator) := do
  let mut H := tree.root
  let blocks := tree.blocks
  for _ in [:|blocks|] do                                        -- `loop`, bounded
    -- the eligible children of the block we stand on; the filter runs at
    -- `DRE` — the ascription keeps the stack out of it — and lifts whole
    let children ← (({B ∈ blocks | B.parent = ↑H}).filterM eligible :
      DRE (Finset (Block Validator)))
    if children = ∅ then
      return H
    -- `H ← arg max score`; the arrowhead says the step picks
    H ⇐ bestChild children score
  return H  -- the bound is reached: not a figure line, see the module header

/-! ## The Goldfish score and eligibility -/

/-! ## Figure -/
/-- Every equivocator, plus every
    non-equivocating participant whose target descends from `B`. The equivocator set is a
    `let`, as the figure writes it — the protocol defines no standalone function.

    An equivocator is counted without its target being read — see the module header. -/
def goldfishScore (votes : Finset (GoldfishVote Validator)) (s : Nat) (B : Block Validator) :
    Nat :=
  -- `{v ∈ K_s : votes holds two distinct votes by v}`
  let equivocators : Finset Validator := {v ∈ Committees.K s |
    ∃ a ∈ votes, ∃ b ∈ votes, a.validator = v ∧ b.validator = v ∧ a ≠ b}
  -- `{v ∈ K_s \ equivocators : (v, s, B') ∈ votes with B ⪯ B'}`
  let supporters := {v ∈ Committees.K s \ equivocators |
    ∃ a ∈ votes, a.validator = v ∧ B ⪯ a.target}
  |equivocators| + |supporters|

/-! ## Figure -/
/-- A strict majority of the
    participants support `B`, or `B` is a block of the current slot. The finality layer
    redefines it with a height clause; that reading, `S.goldfishEligible`, is the
    protocol's, and this one is this file's — hence the `Fig1` name.

    `voters_count` is a `let`, as the figure writes it — the protocol defines no such
    function, only this local and its analogues in `update_confirmation` and
    `S.goldfishEligible`, each over its own vote set.

    The second disjunct is why a fresh proposal can be walked onto at all: "it only does not
    apply to proposals from the current slot, which cannot yet have votes". -/
def Fig1.goldfishEligible (S : Store Validator) (votes : Finset (GoldfishVote Validator))
    (s : Nat) (B : Block Validator) : Bool :=
  -- `voters_count ← |{v ∈ K_s : votes holds a vote by v}|`
  let votersCount := |{v ∈ Committees.K s | ∃ a ∈ votes, a.validator = v}|
  2 * goldfishScore votes s B > votersCount ∨ B.slot = S.s

/-! ## Figure -/
/-- The shared
    walk, instantiated with the Goldfish score and eligibility condition. -/
def Store.goldfishForkChoice (S : Store Validator)
    (tree :  BlockTree Validator)
    (votes : Finset (GoldfishVote Validator))
    (s : Nat) :
    NDRE (Block Validator) :=
  -- the pure condition offered to the walk's raising slot with `pure`
  ghost tree (goldfishScore votes s) (fun B => do return Fig1.goldfishEligible S votes s B)

/-! ## Figure -/
/-- This file's tree: genesis, over the whole processed tree. The first field of
    `Fig1.goldfishWalk` below. -/
def Fig1.getGoldfishFilteredBlockTree (S : Store Validator) : NDRE (BlockTree Validator) :=
  pure { root := .genesis, blocks := S.T }

/-- This file's reading of what the fork choice takes from the layer: the whole processed
    tree from genesis, and this file's eligibility condition, offered to the class's raising
    slot with `pure`.

    It is a `def`, not an `instance`: `GoldfishWalk` carries exactly one instance, the
    assembled protocol's, and this is the value a caller names to pin *this* reading —
    `@Store.getHead _ _ Fig1.goldfishWalk` is `Fig1.getHead`. See `Defs/GoldfishWalk.lean`. -/
abbrev Fig1.goldfishWalk : GoldfishWalk Validator :=
  ⟨Fig1.getGoldfishFilteredBlockTree,
   fun S votes s B => pure (Fig1.goldfishEligible S votes s B)⟩

/-! ## Figure -/
/-- The walk from genesis over the whole
    processed tree. The SG layer redefines it to start from the SG root (`Fig4.getHead`),
    and the finality layer again, from the fork-choice root over the filtered tree — that
    reading is the protocol's, reached as `S.getHead`, and this one is this file's. -/
def Fig1.getHead (S : Store Validator) (votes : Finset (GoldfishVote Validator)) (s : Nat) :
    NDRE (Block Validator) := do
  S.goldfishForkChoice (← Fig1.getGoldfishFilteredBlockTree S) votes s

/-! ## Figure -/
/-- The protocol's `get_head`: the
    Goldfish walk over the layer's tree — descending from its root, stepping onto its blocks —
    testing the layer's eligibility condition. Both come from the single `GoldfishWalk`
    instance (`Defs/GoldfishWalk.lean`), so this is the only definition of `get_head` a caller
    reaches and it means whatever the assembled protocol's fork choice is. The superseded
    readings are `Fig1.getHead` above, `Fig4.getHead` and `Fig7.getHead`. -/
def Store.getHead [GoldfishWalk Validator] (S : Store Validator)
    (votes : Finset (GoldfishVote Validator)) (k : Nat) : NDRE (Block Validator) := do
  ghost (← S.getGoldfishFilteredBlockTree) (goldfishScore votes k) (S.goldfishEligible votes k)

end DC
