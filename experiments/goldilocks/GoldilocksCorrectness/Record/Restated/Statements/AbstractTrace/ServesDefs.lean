module
public import GoldilocksCorrectness.Statements.AbstractTrace.TraceDefs
public import GoldilocksCorrectness.Statements.AbstractTrace.DeliveryDefs
public import GoldilocksCorrectness.Record.Model

@[expose] public section

/-!
# What a Goldilocks node holds, and what it serves to a peer that asks

The sync fact `SyncedWithinBy A x serves ok sync`
(`GoldilocksCorrectness/Statements/AbstractTrace/TraceDefs.lean`) takes the selection `serves` as a
parameter: what a node state serves at a time to a peer that asks. This page gives the two
selections the proofs over a Goldilocks model read.

- `holdsG M n o`: the node state `n` holds the object `o`: a block of its tree, a Goldfish vote of
  its `votesHeld` under the vote's slot, an attestation of its `attestationsHeld`.
- `servesMin M C n t o`: the minimal selection the proofs need: a block of the tree compatible with
  the node's finalized block; a Goldfish vote held whose slot is the slot of `t` or the one before;
  an attestation held at a height at least the node's justification height.
- `holdsG_of_servesMin`: what `servesMin` serves is held.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GoldilocksCorrectness.Record.Statements.AbstractTrace

open Goldilocks (NamedObject Config Block)

variable {V : Type} [DecidableEq V] [Fintype V] (M : GoldilocksModel V)

/-- `holdsG M n o`: the node `n` holds the object `o`: a block of its tree, a Goldfish vote of its
`votesHeld` under the vote's slot, an attestation of its `attestationsHeld`.

The variables:
- `M`: the model; `n`: the node state; `o`: the object.

Read aloud: `o` is in `n`'s tree, pool or attestations. -/
def holdsG (n : M.N) : NamedObject V → Prop
  | .block B => B ∈ M.tree n
  | .gfVote vote => vote ∈ M.votesHeldSet n vote.slot
  | .attest a => a ∈ M.attestationsHeld n

/-- `servesMin M C n t o`: the minimal selection the proofs need, what the node `n` serves at the
time `t` to a peer that asks: a block of its tree, other than the genesis block, that is compatible
with its finalized block (an ancestor of it, or a descendant of it, or the block itself); a Goldfish
vote it holds whose slot is the slot of `t` or the one before; an attestation it holds at a height
at least its justification height `justifiedHeight n`. The genesis block is not served: every node
holds it from the start.

The variables:
- `M`: the model; `C`: the configuration (for the slot of `t`); `n`: the node state; `t`: the time
  at which a peer asks; `o`: the object.

Read aloud: the holder serves the blocks of the chain it follows and of the forks its finalized
block has not pruned, the votes of the current and the previous slot, the attestations from its
justified height on; no holder serves the genesis block. -/
def servesMin (C : Config) (n : M.N) (t : ℕ) : NamedObject V → Prop
  | .block B => B ∈ M.tree n ∧ (M.finalized n).compatible B = true ∧ B ≠ Block.genesis
  | .gfVote vote => vote ∈ M.votesHeldSet n vote.slot ∧ M.slot C t ≤ vote.slot + 1
  | .attest a => a ∈ M.attestationsHeld n ∧ M.justifiedHeight n ≤ a.h

/-- `releaseOf M C o`: the clock value from which a Goldilocks node admits the object `o` at its
delivery: the start of the block's slot for a block, the start of the vote's slot for a Goldfish
vote; an attestation has none (a well-formed attestation is admitted at any clock value). The
environment's promises `EnvFactsBy` and the sync fact `SyncedWithinBy` take it as their `release`
on every restated statement.

The variables:
- `M`: the model; `C`: the configuration (for the slot starts); `o`: the object.

Read aloud: a block or a Goldfish vote of slot `s` is admitted only once the receiver's clock has
reached the start of slot `s`; an attestation at any clock value. -/
def releaseOf (C : Config) : NamedObject V → Option ℕ
  | .block B => some (M.slotStart C B.slot)
  | .gfVote vote => some (M.slotStart C vote.slot)
  | .attest _ => none

/-- What the minimal selection serves, the node holds.

The variables:
- `M`: the model; `C`: the configuration; `n`: the node state; `t`: the time; `o`: the object;
  `h`: `n` serves `o` at `t`.

Read aloud: `servesMin` is contained in `holdsG`. -/
theorem holdsG_of_servesMin (C : Config) (n : M.N) (t : ℕ) (o : NamedObject V)
    (h : servesMin M C n t o) : holdsG M n o := by
  cases o with
  | block B => exact h.1
  | gfVote vote => exact h.1
  | attest a => exact h.1

end GoldilocksCorrectness.Record.Statements.AbstractTrace
