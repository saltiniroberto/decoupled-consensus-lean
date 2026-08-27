import SpecM.Defs.Nondet

/-!
# The fork choice the duties call

The protocol redefines `get_head` at every layer, and its duties outlive all of those
readings: a proposer builds on the head, a voter votes for it, and neither statement
changes when the walk beneath it does. So the duties name no reading. They name the field
of `ForkChoice` below, written `S.getHead votes k`, and the layer that owns the protocol's
reading supplies the instance.

## One instance, and moving it is how a layer takes over

The class carries **exactly one** instance. A layer takes the fork choice over by moving
it, not by adding a second: two instances would leave a duty's meaning to instance
resolution, which is not where a protocol decision belongs. Each layer's own reading stays
a plain `Fig<n>.getHead` definition — the figure content a reader audits — and nothing
calls it.

## Why a class rather than a parameter

The readings differ in three things at once: the anchor the walk starts from, the tree it
descends, and the eligibility condition it tests. A duty that took those as parameters
would carry three arguments the protocol's figures do not write, through every duty and
every tick. A duty that took the whole `get_head` as one parameter would carry one — still
an argument the figures do not write, and one every caller must thread. The class puts the
choice where the other ambient facts of the protocol live, and leaves the duty reading as
the figure writes it.

What it costs: a reader at a call site sees `S.getHead` without being told which reading
runs. The answer is always the same — whichever layer holds the instance — and this file
is where that rule is written down.
-/

set_option autoImplicit false

namespace DC

variable {Validator : Type} [Roots]

/-- The fork choice the duties call: the head to build on or to vote for. Exactly one
    instance exists, supplied by the layer whose reading is the protocol's. -/
class ForkChoice (Validator : Type) [Roots] where
  /-- The head, from the store, a set of slot-`k` votes, and the vote slot `k`. -/
  getHead : (S : Store Validator) → (votes : Finset (GoldfishVote Validator)) →
    (k : Nat) → NDRE (Block Validator)

/-- `Σ.get_head(votes, k)`, as the figures call it: the instance's reading, reached by dot
    notation, so a duty writes `S.getHead votes k` and means whichever reading the
    assembled protocol has. -/
abbrev Store.getHead [ForkChoice Validator] (S : Store Validator)
    (votes : Finset (GoldfishVote Validator)) (k : Nat) : NDRE (Block Validator) :=
  ForkChoice.getHead S votes k

end DC
