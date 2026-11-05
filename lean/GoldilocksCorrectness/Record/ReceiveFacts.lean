module
public import GoldilocksCorrectness.Record.ModelSpellings
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ACStoreDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOfDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGCachesDefs

@[expose] public section

/-!
# The facts of the receipt

`ReceiveFacts M` holds, for a model `M`, what a delivery does to a node state: what each reader
answers on `M.receive C P X n o`, the node state `n` after the object `o` is delivered to it,
against what it answers on `n`; and which objects the node re-sends, `M.relayedObjects o`. A
delivery keeps the confirmation state, the lock entries, the wake time, the clock, the validator
and the anti-slashing record; it grows the tree, the finalized block's chain, the votes held, the
stamps and the attestations held; what it adds is the delivered object or what that object
carries, stamped with the clock; a delivered Goldfish vote is admitted under the slot and
committee conditions; the votes of a delivered block that enters the tree are admitted under the
same conditions; a delivered attestation that is well formed is held; and under the model's node
invariant the finalized block, the justified block and the justification caches move only as the
chain states of the tree's blocks allow. That a delivery keeps the node invariant is the field
`receive_nodeInv` of `NodeInvFacts`.

The relations between `n` and the node state after the delivery are written out in each field, as
the landed definitions over the spec's node state say them (`StepFrom`, `TreeGrows`, `StampsAt`,
`AttPoolGrows`, `ChainsInPool`, `FinalizedFrom`, `JustifiedFrom`, `CachesFrom` of
`GoldilocksCorrectness/Proofs/Routines/Node.lean`), read through the record's node readers. Four
facts of the receipt have no field here: whether a delivered block enters the tree, and the stamp
of an admitted block, read the reader `block_admissible`, and the two relations that read the
greatest chain-state height `hMax` (`WitnessedFrom`, `ReachFrom`) are not stated; This file holds the structure only.
-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Record

open Goldilocks (Config Provisional External RootOrder Block Attestation GoldfishVote NamedObject
  Slot Stamp)
open GoldilocksCorrectness.Record.Proofs.Routines (SlotKeyed ACStampsAt JustifiedOnChainWith
  CachesOnChainWith)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The facts of `M` about the node state after a delivery, `M.receive C P X n o`.

Read aloud: a delivery adds to what the node holds only the delivered object and what it carries,
stamped with the clock, and changes no confirmation, lock, wake time, clock or signature. -/
structure ReceiveFacts (M : GoldilocksModel V) : Prop where
  /-- A delivery keeps the saved confirmations, the fast blocks, the lock entries, the record of
      the confirmed tip, the wake time and the clock.

      Read aloud: a delivery changes no confirmation, lock, wake time or clock. -/
  receive_keeps_confirmation : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V)
      (n : M.N) (o : NamedObject V),
    M.savedConfirmation (M.receive C P X n o) = M.savedConfirmation n ∧
      M.fastBlocks (M.receive C P X n o) = M.fastBlocks n ∧
      M.lockEntries (M.receive C P X n o) = M.lockEntries n ∧
      M.latestConfirmed (M.receive C P X n o) = M.latestConfirmed n ∧
      M.awakeSince (M.receive C P X n o) = M.awakeSince n ∧ (M.receive C P X n o).t = n.t
  /-- A delivery keeps the validator.

      Read aloud: a delivery does not change the validator the node runs as. -/
  receive_validator : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (o : NamedObject V),
    (M.receive C P X n o).v = n.v
  /-- A delivery keeps the anti-slashing record and the attestations sent.

      Read aloud: a delivery changes nothing the node has signed. -/
  receive_Λ : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (o : NamedObject V),
    M.sentTarget (M.receive C P X n o) = M.sentTarget n ∧
      M.sentTimeout (M.receive C P X n o) = M.sentTimeout n ∧
      M.sentLock (M.receive C P X n o) = M.sentLock n ∧
      M.sentAttestations (M.receive C P X n o) = M.sentAttestations n
  /-- From a node state `n` whose votes are filed by slot, a delivery gives a node state `n'` whose
      votes are filed by slot; `n'`'s tree holds `n`'s; `n`'s finalized block is `n'`'s or an
      ancestor of it; `n`'s votes of each slot are a prefix of `n'`'s; the stamps of `n`'s blocks
      and of `n`'s votes are kept; every block of `n'`'s tree not in `n`'s, and every vote `n'`
      holds under a slot that `n` does not hold under it, is stamped with the clock `n'.t`; and
      `n'.t` is `n.t` (the landed `StepFrom n n.t n'`).

      Read aloud: a delivery grows what the node holds, keeps every stamp it had, stamps what it
      adds with the clock, and keeps the clock. -/
  receive_step : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (o : NamedObject V),
    SlotKeyed M n →
      SlotKeyed M (M.receive C P X n o) ∧
      (n.tree ⊆ (M.receive C P X n o).tree ∧
        n.finalized.AncestorEq (M.receive C P X n o).finalized ∧
        (∀ s : Slot, n.votesHeld s <+: (M.receive C P X n o).votesHeld s) ∧
        (∀ B ∈ n.tree, (M.receive C P X n o).blockStamp B = n.blockStamp B) ∧
        ∀ s : Slot, ∀ vote ∈ n.votesHeld s,
          (M.receive C P X n o).voteStamp vote = n.voteStamp vote) ∧
      ((∀ B ∈ (M.receive C P X n o).tree, B ∉ n.tree →
          (M.receive C P X n o).blockStamp B = some ((M.receive C P X n o).t : Stamp)) ∧
        ACStampsAt M n (M.receive C P X n o) (M.receive C P X n o).t) ∧
      (M.receive C P X n o).t = n.t
  /-- A delivery keeps every block of the tree.

      Read aloud: a delivery forgets no accepted block. -/
  receive_tree_mono : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (o : NamedObject V),
    n.tree ⊆ (M.receive C P X n o).tree
  /-- A delivery keeps every attestation the node holds (the landed `AttPoolGrows`).

      Read aloud: a delivery forgets no attestation. -/
  receive_pool : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (o : NamedObject V),
    ∀ a ∈ n.attestationsHeld, a ∈ (M.receive C P X n o).attestationsHeld
  /-- When every attestation on the chain of every block of `n`'s tree is held by `n`, the same
      holds after a delivery (the landed `ChainsInPool`).

      Read aloud: a delivery keeps the node holding every attestation on the chains of its tree. -/
  receive_chainsInPool : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (o : NamedObject V),
    (∀ Y ∈ n.tree, ∀ a : Attestation V, M.on_chain a Y = true → a ∈ n.attestationsHeld) →
      ∀ Y ∈ (M.receive C P X n o).tree, ∀ a : Attestation V, M.on_chain a Y = true →
        a ∈ (M.receive C P X n o).attestationsHeld
  /-- From a node state satisfying the clock-free part of the model's node invariant, a delivery
      gives a node state whose tree holds `n`'s, and whose finalized block is `n`'s or the finalized
      block of the chain state of a block of its tree (the landed `FinalizedFrom`).

      Read aloud: a delivery finalizes only a block some accepted block's chain state finalizes. -/
  receive_finalizedFrom : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V)
      (n : M.N) (o : NamedObject V),
    M.nodeInvCore C P X n →
      n.tree ⊆ (M.receive C P X n o).tree ∧
        ((M.receive C P X n o).finalized = n.finalized ∨
          ∃ B ∈ (M.receive C P X n o).tree,
            (M.receive C P X n o).finalized = (M.chainStateOf C B).F)
  /-- From a node state satisfying the model's node invariant, a delivery gives a node state whose
      justified block is `n`'s, or the justified block of the chain state of some block (the landed
      `JustifiedFrom`).

      Read aloud: a delivery moves the justified block only to a block some chain state
      justifies. -/
  receive_justifiedFrom : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V)
      (n : M.N) (o : NamedObject V),
    M.nodeInv C P X n →
      (M.receive C P X n o).justified = n.justified ∨
        ∃ D : Block V, (M.receive C P X n o).justified = (M.chainStateOf C D).J
  /-- From a node state satisfying the model's node invariant, a delivery gives a node state whose
      tree holds `n`'s, and which satisfies `CachesOnChainWith M C H OnChain` when `n` does and every
      block of its tree satisfies `JustifiedOnChainWith M C H OnChain` (the landed `CachesFrom`).

      Read aloud: a delivery keeps the node's justification, justified at a height greater than
      `H`, on blocks satisfying `OnChain`, when every accepted block's justification is. -/
  receive_cachesFrom : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (H : ℕ)
      (OnChain : Block V → Prop) (n : M.N) (o : NamedObject V),
    M.nodeInv C P X n →
      n.tree ⊆ (M.receive C P X n o).tree ∧
        ((∀ B ∈ (M.receive C P X n o).tree, JustifiedOnChainWith M C H OnChain B) →
          CachesOnChainWith M C H OnChain n →
            CachesOnChainWith M C H OnChain (M.receive C P X n o))
  /-- A delivery of `o` adds to the votes held only votes `o` carries (`o` is the vote, or a block
      whose `votes` holds it), and to the tree only `o`'s block, of a slot at most the slot of the
      clock.

      Read aloud: a delivery adds only what the delivered object is or carries, and no block of a
      later slot than the node's. -/
  receive_new : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (o : NamedObject V),
    (∀ s : Slot, ∀ vote ∈ (M.receive C P X n o).votesHeld s, vote ∉ n.votesHeld s →
        o = NamedObject.gfVote vote ∨ ∃ B : Block V, o = NamedObject.block B ∧ vote ∈ B.votes) ∧
      ∀ B ∈ (M.receive C P X n o).tree, B ∉ n.tree →
        o = NamedObject.block B ∧ B.slot ≤ C.slot (M.receive C P X n o).t
  /-- Every attestation the node holds after the delivery of `o` and did not hold before is `o`
      itself, or is included in `o`, when `o` is a block.

      Read aloud: a delivery adds to the attestations held only the delivered attestation, or the
      attestations of the delivered block. -/
  receive_new_attestations : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V)
      (n : M.N) (o : NamedObject V),
    ∀ a ∈ (M.receive C P X n o).attestationsHeld, a ∉ n.attestationsHeld →
      o = NamedObject.attest a ∨ ∃ B : Block V, o = NamedObject.block B ∧ a ∈ B.attestations
  /-- A delivery adds to the votes held only votes of a slot at most the slot of the clock.

      Read aloud: a delivery admits no vote of a slot later than the node's. -/
  receive_new_slot : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (o : NamedObject V),
    ∀ s : Slot, ∀ vote ∈ (M.receive C P X n o).votesHeld s, vote ∉ n.votesHeld s →
      vote.slot ≤ C.slot n.t
  /-- A delivered Goldfish vote whose slot is the slot of the clock or the one before, and whose
      validator is in its slot's committee, is held after the delivery, or `n`'s votes of its slot
      already hold two distinct votes of its validator.

      Read aloud: a vote of the current or the previous slot, from a committee member, is admitted
      unless its validator has already equivocated. -/
  receive_gfVote_cases : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (vote : GoldfishVote V),
    C.slot n.t ≤ vote.slot + 1 → vote.slot ≤ C.slot n.t → vote.val_index ∈ P.committee vote.slot →
      vote ∈ M.votesHeldSet (M.receive C P X n (NamedObject.gfVote vote)) vote.slot ∨
        M.equivocates (M.votesHeldSet n vote.slot) vote.val_index = true
  /-- A delivered Goldfish vote either leaves the votes held and their stamps as they were, or is a
      vote `n` does not hold under its slot, of a validator of its slot's committee, appended to
      `n`'s votes of its slot and stamped with the clock `n.t`.

      Read aloud: a delivered vote is ignored, or admitted at the clock. -/
  receive_gfVote_admits : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V)
      (n : M.N) (vote : GoldfishVote V),
    (M.votesHeld (M.receive C P X n (NamedObject.gfVote vote)) = M.votesHeld n ∧
        M.voteStamp (M.receive C P X n (NamedObject.gfVote vote)) = M.voteStamp n) ∨
      (vote ∉ n.votesHeld vote.slot ∧ vote.val_index ∈ P.committee vote.slot ∧
        M.votesHeld (M.receive C P X n (NamedObject.gfVote vote)) =
          Function.update (M.votesHeld n) vote.slot (n.votesHeld vote.slot ++ [vote]) ∧
        M.voteStamp (M.receive C P X n (NamedObject.gfVote vote)) =
          Function.update (M.voteStamp n) vote (some (n.t : Stamp)))
  /-- When a delivered block `B` enters the tree, every Goldfish vote `B` includes whose slot is
      the slot of the clock or the one before, and whose validator is in its slot's committee, is
      held after the delivery, or the votes of its slot held after the delivery hold two distinct
      votes of its validator.

      Read aloud: an accepted block's votes of the current or the previous slot, from committee
      members, are admitted unless their validator has equivocated. -/
  receive_block_votes : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V)
      (n : M.N) (B : Block V),
    B ∉ n.tree → B ∈ (M.receive C P X n (NamedObject.block B)).tree →
      ∀ vote ∈ B.votes, C.slot n.t ≤ vote.slot + 1 → vote.slot ≤ C.slot n.t →
        vote.val_index ∈ P.committee vote.slot →
          vote ∈ M.votesHeldSet (M.receive C P X n (NamedObject.block B)) vote.slot ∨
            M.equivocates (M.votesHeldSet (M.receive C P X n (NamedObject.block B)) vote.slot)
              vote.val_index = true
  /-- A delivered attestation that is well formed is held after the delivery.

      Read aloud: a well-formed attestation the node receives is held. -/
  receive_attestation_held : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V)
      (n : M.N) (a : Attestation V),
    M.attestation_well_formed a = true →
      a ∈ (M.receive C P X n (NamedObject.attest a)).attestationsHeld
  /-- The objects re-sent on the delivery of `o` are `o`, and, when `o` is a block, each Goldfish
      vote and each attestation it includes.

      Read aloud: a node re-sends the delivered object, and a block's votes and attestations. -/
  mem_relayedObjects_iff : ∀ (o o' : NamedObject V),
    o' ∈ M.relayedObjects o ↔
      o' = o ∨ ∃ B : Block V, o = NamedObject.block B ∧
        ((∃ vote ∈ B.votes, o' = NamedObject.gfVote vote) ∨
          ∃ a ∈ B.attestations, o' = NamedObject.attest a)

end GoldilocksCorrectness.Record
