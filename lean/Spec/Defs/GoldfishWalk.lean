import Spec.Defs.Nondet

/-!
# What the fork choice takes from the layer

`get_head` is one definition (`Store.getHead`, `01_GoldfishWalk.lean`): the Goldfish walk
from an anchor, over a set of blocks, testing an eligibility condition. Those three are what
the protocol redefines as the layers accumulate — the SG layer selects the anchor with a
walk of its own, the finality layer descends `get_filtered_block_tree(Σ)` rather than `Σ.T`
and extends `goldfish_eligible` with a height clause, the healing layer starts the SG walk
from the round's own root and drops the grade-0 blocks. They are the three fields of
`GoldfishWalk` below.

So `get_head` is written once, and the duties that call it name no reading. A proposer builds
on the head and a voter votes for it, and neither statement changes when the walk beneath it
does: they write `S.getHead votes k`, and the layer that owns the protocol's readings
supplies the instance.

## One instance, and moving it is how a layer takes over

The class carries **exactly one** instance. A layer takes the fork choice over by moving it,
not by adding a second: two instances would leave a duty's meaning to instance resolution,
which is not where a protocol decision belongs. Each superseded reading stays a plain
`Fig<n>.getHead` definition — the figure content a reader audits — and nothing calls it.

## Why the three sit in one class

They are redefined together and consumed together: `get_head` hands `ghost` the anchor, the
blocks and the condition in the same call. One class means one instance to move when a layer
takes the walk over, rather than three that could disagree about which layer is speaking. A
layer that changes only one field builds its instance from the others' earlier readings, and
says so where the instance is declared.

## Why a class rather than parameters

A `get_head` that took the three as parameters would carry three arguments the protocol's
figures do not write, through every duty and every tick. One that took the whole `get_head`
as a parameter would carry one — still an argument the figures do not write, and one every
caller must thread. The class puts the choice where the other ambient facts of the protocol
live, and leaves the duties reading as the figures write them.

What it costs: a reader at a call site sees `S.getHead` without being told which reading
runs. The answer is always the same — whichever layer holds the instance — and this file is
where that rule is written down.
-/

set_option autoImplicit false

namespace DC

variable {Validator : Type} [Roots]

/-- The three things the fork choice takes from the layer: the block its walk descends from,
    the blocks it may descend, and the condition a child must satisfy. Exactly one instance
    exists, supplied by the layer whose readings are the protocol's. -/
class GoldfishWalk (Validator : Type) [Roots] where
  /-- The block the walk descends from. From the SG layer on it is selected by a walk of its
      own, so it picks as well as raises — hence `NDRE` rather than `DRE`. -/
  anchor : (S : Store Validator) → NDRE (Block Validator)
  /-- The blocks the walk may descend. It raises: the readings that filter by height read
      `Σ.σ[·]`, and a block the map does not record has no height. -/
  getFilteredBlockTree : (S : Store Validator) → DRE (Finset (Block Validator))
  /-- Whether the walk may step onto `B`, given the slot-`s` votes it counts. It raises for
      the same reason. -/
  eligible : (S : Store Validator) → (votes : Finset (GoldfishVote Validator)) →
    (s : Nat) → (B : Block Validator) → DRE Bool

/-- The anchor `get_head`'s walk starts from: the instance's reading, reached by dot
    notation. -/
abbrev Store.anchor [GoldfishWalk Validator] (S : Store Validator) :
    NDRE (Block Validator) :=
  GoldfishWalk.anchor S

/-- `get_filtered_block_tree(Σ)`, as the figures call it: the instance's reading, reached by
    dot notation. -/
abbrev Store.getFilteredBlockTree [GoldfishWalk Validator] (S : Store Validator) :
    DRE (Finset (Block Validator)) :=
  GoldfishWalk.getFilteredBlockTree S

/-- `goldfish_eligible(Σ, votes, s, B)`, as the figures call it: the instance's reading,
    reached by dot notation. -/
abbrev Store.goldfishEligible [GoldfishWalk Validator] (S : Store Validator)
    (votes : Finset (GoldfishVote Validator)) (s : Nat) (B : Block Validator) : DRE Bool :=
  GoldfishWalk.eligible S votes s B

end DC
