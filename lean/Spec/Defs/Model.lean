import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Lattice.Basic

/-!
# The model of the protocol, and the `⊥` spelling

The section `## Extract` of this header describes the model of the protocol that `Spec` renders.
Besides it, this file declares, in the namespace `DC`, the scoped instance that spells `none` as
`⊥`, `Bot (Option α)`. A file that opens `open scoped DC` can write `x ≠ ⊥` for `x ≠ none`. In
`Spec` it is read by `Option.value` of `lean/Spec/Defs/Raise.lean`, whose hypothesis is written
`x ≠ ⊥`; the routines of `Spec` test absence with `none` (`if x ≠ none then`, the notation of
`lean/Spec/Objects.lean`).

The section `## Extract` is the opening prose of the generated document (`extract/`).

## Extract

A finite set of validators `V` is given, each validator with a fixed positive weight; `W` is the
total weight of all validators. Slot `s` starts at the instant `4Δs` and has an assigned proposer
and a committee, a set of validators. Round `r` is the slots `rR` to `rR + R − 1`. After an
instant no node knows, `Δ` bounds the delivery of every object; no routine reads that instant.
A node's tick runs at the multiples of `Δ`.

A block `B` is the genesis block, or a block with a parent `B.parent`, a slot `B.slot`, a root
`B.root`, a proposer, the Goldfish votes `B.gf_votes` it includes, the list
`B.gf_support_votes` of those resolved in the proposer's view, and the attestations
`B.attestations` it includes. The genesis block has slot `0` and the least root. Goldfish votes
and attestations name blocks by their roots. A node's block tree holds the blocks it has
admitted; it admits a block only when the tree holds the block's parent, the parent's slot is
earlier than the block's slot, and the block's proposer is the proposer of its slot. `A` is an
ancestor of `B`, or `B` itself, when `A.ancestorEq B`; two blocks are compatible when one is an
ancestor of the other or they are equal. The deepest block of a set has the greatest depth and,
among those, the greatest root.

Slot `s` has these actions:

| instant | action |
| `4Δs` | proposal, by the proposer of slot `s` |
| `4Δs + Δ` | Goldfish vote, by the members of the committee of slot `s` |
| `4Δs + 2Δ` | Goldfish confirmation of slot `s − 1` |
| `4Δs + 3Δ` | view freeze of slot `s` |

Round `r` has one more: a validator sends its attestation of round `r` at `4ΔrR + 6Δ`, in the round's
second slot.

A Goldfish vote is a tuple `(v, s, head)`: the validator `v` votes at the slot `s` for the block
whose root is `head`. A node admits it only from a member of the committee of slot `s`. An
attestation is a tuple `(v, r, confirmed, height pair, finality pair)`: the vote of the
validator `v` at the round `r`, made of the root of the block it confirms or none, its height
pair and its finality pair.
-/

set_option autoImplicit false

namespace DC

/-- `⊥` for an absent block, height or confirmed block, as the protocol writes it. Scoped, so it cannot
    leak into a file that means something else by `⊥`. -/
scoped instance {α : Type} : Bot (Option α) := ⟨none⟩

end DC
