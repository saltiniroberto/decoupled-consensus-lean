import Spec.Defs.Nondet

/-!
# What the Goldfish walk takes from the layer

`ghost` (`01_GoldfishWalk.lean`) descends a set of blocks, testing each child against an
eligibility condition. The protocol redefines both: the finality layer descends
`get_filtered_block_tree(Σ)` rather than `Σ.T`, and tests `goldfish_eligible` extended with
a height clause. A routine that walks should not have to name a reading of either, so it
names the two fields of `GoldfishWalk` below, written `S.getFilteredBlockTree` and
`S.goldfishEligible`, and the layer that owns the protocol's readings supplies the instance.

## One instance, and moving it is how a layer takes over

The same discipline as `ForkChoice` (`Defs/ForkChoice.lean`). The class carries **exactly
one** instance: two would leave a walk's meaning to instance resolution, which is not where
a protocol decision belongs. A later layer takes the pair over by moving the instance, not
by adding a second, and each layer's own readings stay plain `Fig<n>` definitions — the
figure content a reader audits.

## Why the two sit in one class

They are redefined together and consumed together: a walk hands `ghost` the blocks and the
condition in the same call, and every layer that has changed one has changed the other. One
class means one instance to move when a layer takes the walk over, rather than two that
could disagree about which layer is speaking.

## Why a class rather than parameters

A walk that took the tree and the condition as arguments would carry two arguments the
protocol's figures do not write, through every caller. The class puts them where the other
ambient facts of the protocol live, and leaves each walk reading as its figure writes it.

What it costs is the same as `ForkChoice`'s: a reader at a call site sees
`S.getFilteredBlockTree` without being told which reading runs. The answer is always
whichever layer holds the instance, and this file is where that rule is written down.
-/

set_option autoImplicit false

namespace DC

variable {Validator : Type} [Roots]

/-- The two things a Goldfish walk takes from the layer: the blocks it may descend, and the
    condition a child must satisfy. Exactly one instance exists, supplied by the layer whose
    readings are the protocol's. -/
class GoldfishWalk (Validator : Type) [Roots] where
  /-- The blocks the walk may descend. It raises: the readings that filter by height read
      `Σ.σ[·]`, and a block the map does not record has no height. -/
  getFilteredBlockTree : (S : Store Validator) → DRE (Finset (Block Validator))
  /-- Whether the walk may step onto `B`, given the slot-`s` votes it counts. It raises for
      the same reason. -/
  eligible : (S : Store Validator) → (votes : Finset (GoldfishVote Validator)) →
    (s : Nat) → (B : Block Validator) → DRE Bool

/-- `get_filtered_block_tree(Σ)`, as the figures call it: the instance's reading, reached by
    dot notation, so a walk writes `S.getFilteredBlockTree` and means whichever reading the
    assembled protocol has. -/
abbrev Store.getFilteredBlockTree [GoldfishWalk Validator] (S : Store Validator) :
    DRE (Finset (Block Validator)) :=
  GoldfishWalk.getFilteredBlockTree S

/-- `goldfish_eligible(Σ, votes, s, B)`, as the figures call it: the instance's reading,
    reached by dot notation. -/
abbrev Store.goldfishEligible [GoldfishWalk Validator] (S : Store Validator)
    (votes : Finset (GoldfishVote Validator)) (s : Nat) (B : Block Validator) : DRE Bool :=
  GoldfishWalk.eligible S votes s B

end DC
