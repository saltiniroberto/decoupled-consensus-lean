import Spec.Defs.Nondet

/-!
# What the fork choice takes from the layer

`get_head` is one definition (`Store.getHead`, `01_GoldfishWalk.lean`): the Goldfish walk
over a tree, testing an eligibility condition. Those two are what the protocol redefines as
the layers accumulate — the SG layer roots the tree at a walk of its own rather than at
genesis, the finality layer holds the blocks of `get_filtered_block_tree(Σ)` rather than
`Σ.T` and extends `goldfish_eligible` with a height clause, the healing layer starts the SG
walk from the round's own root and drops the grade-0 blocks. They are the two fields of
`GoldfishWalk` below.

So `get_head` is written once, and the duties that call it name no reading. A proposer builds
on the head and a voter votes for it, and neither statement changes when the walk beneath it
does: they write `S.getHead votes k`, and the layer that owns the protocol's readings
supplies the instance.

## The tree carries its own anchor

`BlockTree` (`Defs/Model.lean`) is a root and a set of blocks, and the walk needs both: it
descends from the root through the blocks. So one field supplies the pair rather than two
supplying the halves. That also keeps the two out of step with each other by construction —
from the SG layer on, the root is selected by a walk over those very blocks.

The field is `NDRE` because that selecting walk picks: `ghost`'s arg-max step is a
nondeterministic choice, so a layer whose root comes from a walk cannot supply it in `DRE`.

## One instance, and moving it is how a layer takes over

The class carries **exactly one** instance. A layer takes the fork choice over by moving it,
not by adding a second: two instances would leave a duty's meaning to instance resolution,
which is not where a protocol decision belongs. Each superseded reading stays a plain
`Fig<n>.getHead` definition — the figure content a reader audits — and nothing calls it.

## Why the two sit in one class

They are redefined together and consumed together: `get_head` hands `ghost` the tree and the
condition in the same call. One class means one instance to move when a layer takes the walk
over, rather than two that could disagree about which layer is speaking. A layer that changes
one field builds its instance from the other's earlier reading, and says so where the
instance is declared.

## Why a class rather than parameters

A `get_head` that took the two as parameters would carry two arguments the protocol's figures
do not write, through every duty and every tick. One that took the whole `get_head` as a
parameter would carry one — still an argument the figures do not write, and one every caller
must thread. The class puts the choice where the other ambient facts of the protocol live,
and leaves the duties reading as the figures write them.

What it costs: a reader at a call site sees `S.getHead` without being told which reading
runs. The answer is always the same — whichever layer holds the instance — and this file is
where that rule is written down.
-/

set_option autoImplicit false

namespace DC

variable {Validator : Type} [Roots]

/-- The two things the fork choice takes from the layer: the tree its walk descends, root and
    blocks together, and the condition a child must satisfy. Exactly one instance exists,
    supplied by the layer whose readings are the protocol's. -/
class GoldfishWalk (Validator : Type) [Roots] where
  /-- The tree the walk descends: `root` is the block it starts from and `blocks` are the
      blocks it may step onto. It picks as well as raises — from the SG layer on the root is
      selected by a walk of its own — hence `NDRE` rather than `DRE`. -/
  getGoldfishFilteredBlockTree : (S : Store Validator) → NDRE (BlockTree Validator)
  /-- Whether the walk may step onto `B`, given the slot-`s` votes it counts. It raises: the
      readings that test a height read `Σ.σ[B]`, and a block the map does not record has
      none. -/
  eligible : (S : Store Validator) → (votes : Finset (GoldfishVote Validator)) →
    (s : Nat) → (B : Block Validator) → DRE Bool

/-- The tree `get_head`'s walk descends: the instance's reading, reached by dot notation. -/
abbrev Store.getGoldfishFilteredBlockTree [GoldfishWalk Validator] (S : Store Validator) :
    NDRE (BlockTree Validator) :=
  GoldfishWalk.getGoldfishFilteredBlockTree S

/-- `goldfish_eligible(Σ, votes, s, B)`, as the figures call it: the instance's reading,
    reached by dot notation. -/
abbrev Store.goldfishEligible [GoldfishWalk Validator] (S : Store Validator)
    (votes : Finset (GoldfishVote Validator)) (s : Nat) (B : Block Validator) : DRE Bool :=
  GoldfishWalk.eligible S votes s B

end DC
