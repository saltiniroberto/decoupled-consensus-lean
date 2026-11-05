module
public import GoldilocksCorrectness.Record.ModelSpellings

@[expose] public section

/-!
# The facts of the wake

`WakeFacts M` holds, for a model `M`, what a wake at the time `t` does to a node state: `M.wake n t`
has no wake time (`awakeSince` is none), its clock is `t`, and every other reader of a node state
answers on `M.wake n t` what it answers on `n`. That a wake keeps the model's node invariant is the
field `wake_nodeInv` of `NodeInvFacts`. This file holds the structure only.
-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Record

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The facts of `M` about the node state after a wake at the time `t`, `M.wake n t`.

Read aloud: a wake forgets the wake time, sets the clock to the wake time, and changes nothing
else. -/
structure WakeFacts (M : GoldilocksModel V) : Prop where
  /-- After a wake the node has no wake time.

      Read aloud: a wake sets the time the node has been awake since to none. -/
  wake_awakeSince : ∀ (n : M.N) (t : Goldilocks.Time), (M.wake n t).awakeSince = none
  /-- The clock of `M.wake n t` is `t`, and every reader of a node state other than `awakeSince` and
      the clock answers on `M.wake n t` what it answers on `n`: the validator, the tree, the
      finalized and the justified blocks, the justification height, the attestations and the
      Goldfish votes held, the stamps, the saved confirmations, the lock entries, the fast blocks,
      the record of the confirmed tip, and the anti-slashing record and the attestations sent.

      Read aloud: a wake sets the clock to the wake time and changes nothing else the node holds. -/
  wake_readers : ∀ (n : M.N) (t : Goldilocks.Time),
    M.validator (M.wake n t) = M.validator n ∧ M.clock (M.wake n t) = t ∧
      M.tree (M.wake n t) = M.tree n ∧ M.finalized (M.wake n t) = M.finalized n ∧
      M.justified (M.wake n t) = M.justified n ∧
      M.justifiedHeight (M.wake n t) = M.justifiedHeight n ∧
      M.attestationsHeld (M.wake n t) = M.attestationsHeld n ∧
      M.votesHeld (M.wake n t) = M.votesHeld n ∧ M.voteStamp (M.wake n t) = M.voteStamp n ∧
      M.blockStamp (M.wake n t) = M.blockStamp n ∧
      M.savedConfirmation (M.wake n t) = M.savedConfirmation n ∧
      M.lockEntries (M.wake n t) = M.lockEntries n ∧ M.fastBlocks (M.wake n t) = M.fastBlocks n ∧
      M.latestConfirmed (M.wake n t) = M.latestConfirmed n ∧
      M.sentTarget (M.wake n t) = M.sentTarget n ∧ M.sentTimeout (M.wake n t) = M.sentTimeout n ∧
      M.sentLock (M.wake n t) = M.sentLock n ∧
      M.sentAttestations (M.wake n t) = M.sentAttestations n

end GoldilocksCorrectness.Record
