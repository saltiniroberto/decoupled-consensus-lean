module
public import GoldilocksCorrectness.Record.ModelSpellings
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ACStoreDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOfDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGCachesDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickDefs

@[expose] public section

/-!
# The facts of the tick, part 1

`TickFacts1 M` holds, for a model `M`, the facts of its tick that read no duty's computation: of
every answer `(n', sent)` of the tick `M.tick C P X n t` (an outcome `.ok (n', sent)`), what each
reader of `n'` is against `n`, and what `sent` holds. A tick keeps the validator, sets the clock to
`t`, and records `t` as the wake time when none was recorded; away from its slot's vote time and
support cutoff it keeps exactly the lock entries live at `t`; away from the support cutoff it keeps
the saved confirmations, the fast blocks and the record of the confirmed tip, and it changes the
saved confirmations or that record only at the support cutoff of a node awake since the slot's duty
window started; it grows the tree, the votes, the stamps, the attestations held and the
attestations signed, and what it adds to the votes and the tree it sent; under the model's node
invariant the finalized block, the justified block and the justification caches move only as the
chain states of the tree's blocks allow. Of what it sends: a Goldfish vote only as the node's
validator, for the slot, at its vote time, and at most one; a vote when an awake committee member's
tick runs at the vote time; a block when an awake proposer's tick runs at a slot's start; at most
one block, which the node then holds when the block is new and passes the checks the proposal does
not make itself; an attestation only when awake; and every attestation it signs is one it sent.

The times of a slot `s` are written as the configuration computes them (`C.t_ s` its start,
`C.t_ s + C.Δ` its vote time, `C.t_ s + 2 * C.Δ` its support cutoff), and the wake windows as the
spec's `duty_window_start C s` and `proposal_window_start C s`, as the landed statements read them.
What the tick does at the vote time and at the support cutoff of an awake node (the revocation of
the locks, the confirmation update) and how its Goldfish vote, its block and its attestation are
built are the facts of part 2 and part 3, each its own structure. That a tick keeps the node
invariant and answers under it are fields of `NodeInvFacts`. Two relations of the landed tick
theorems read the greatest chain-state height `hMax` (`WitnessedFrom`, `ReachFrom`) and are not
stated; This file holds the structure only.
-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Record

open Goldilocks (Config Provisional External RootOrder Block Attestation GoldfishVote NamedObject
  Slot Time Stamp duty_window_start proposal_window_start)
open GoldilocksCorrectness.Record.Proofs.Routines (SlotKeyed ACStampsAt JustifiedOnChainWith
  CachesOnChainWith)
open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The facts of `M` about the outcomes of a tick, `M.tick C P X n t`, part 1: those that read no
duty's computation.

Read aloud: a tick sets the clock, records a wake, expires the locks, grows what the node holds,
changes a confirmation only at an awake node's support cutoff, and sends only its own duties'
objects. -/
structure TickFacts1 (M : GoldilocksModel V) : Prop where
  /-- T1. A tick keeps the validator, sets the clock to the tick's time `t`, and has as its wake
      time `n`'s, or `t` when `n` has none.

      Read aloud: a tick keeps the validator, sets the clock to the tick's time, and records the
      tick's time as the wake time when none was recorded. -/
  tick_clock_validator_awakeSince : ∀ [RootOrder] (C : Config) (P : Provisional V)
      (X : External V) (n : M.N) (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t →
      n'.v = n.v ∧ n'.t = t ∧
        n'.awakeSince = some (match n.awakeSince with | none => t | some τ => τ)
  /-- T2. A tick at neither the vote time nor the support cutoff of the slot of `t` leaves exactly
      `n`'s lock entries whose deadline is after `t`.

      Read aloud: away from its slot's two duty times, a tick deletes the lock entries whose
      deadline has passed, and changes no other. -/
  tick_lock_entries : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t →
      n'.lockEntries = {e ∈ n.lockEntries | t < e.d} ∨ t = C.t_ (C.slot t) + C.Δ ∨
        t = C.t_ (C.slot t) + 2 * C.Δ
  /-- A tick away from the support cutoff of the slot of `t` keeps the saved confirmations, the
      fast blocks and the record of the confirmed tip.

      Read aloud: away from its slot's support cutoff, a tick changes no confirmation. -/
  tick_keeps_confirmation_off_cutoff : ∀ [RootOrder] (C : Config) (P : Provisional V)
      (X : External V) (n : M.N) (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t → t ≠ C.t_ (C.slot t) + 2 * C.Δ →
      M.savedConfirmation n' = M.savedConfirmation n ∧ n'.fastBlocks = n.fastBlocks ∧
        n'.latestConfirmed = n.latestConfirmed
  /-- A tick keeps the saved confirmations and the record of the confirmed tip, unless `t` is the
      support cutoff of its slot and `n` has been awake since that slot's duty window started.

      Read aloud: only an awake node's tick at the support cutoff changes a saved confirmation or
      the confirmed tip's record. -/
  tick_confirmation_awake : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V)
      (n : M.N) (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t →
      (M.savedConfirmation n' = M.savedConfirmation n ∧ n'.latestConfirmed = n.latestConfirmed) ∨
        (t = C.t_ (C.slot t) + 2 * C.Δ ∧ AwakeFor M C n (C.slot t))
  /-- From a node state whose votes are filed by slot, a tick at `t` gives a node state `n'` whose
      votes are filed by slot; `n'`'s tree holds `n`'s; `n`'s finalized block is `n'`'s or an
      ancestor of it; `n`'s votes of each slot are a prefix of `n'`'s; the stamps of `n`'s blocks
      and of `n`'s votes are kept; every block of `n'`'s tree not in `n`'s, and every vote `n'`
      holds under a slot that `n` does not hold under it, is stamped with `t`; and `n'.t` is `t`
      (the landed `StepFrom n t n'`).

      Read aloud: a tick grows what the node holds, keeps every stamp it had, stamps what it adds
      with the tick's time, and sets the clock to it. -/
  tick_step : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t → SlotKeyed M n →
      SlotKeyed M n' ∧
      (n.tree ⊆ n'.tree ∧ n.finalized.AncestorEq n'.finalized ∧
        (∀ s : Slot, n.votesHeld s <+: n'.votesHeld s) ∧
        (∀ B ∈ n.tree, n'.blockStamp B = n.blockStamp B) ∧
        ∀ s : Slot, ∀ vote ∈ n.votesHeld s, n'.voteStamp vote = n.voteStamp vote) ∧
      ((∀ B ∈ n'.tree, B ∉ n.tree → n'.blockStamp B = some (t : Stamp)) ∧
        ACStampsAt M n n' t) ∧
      n'.t = t
  /-- A tick keeps every block of the tree.

      Read aloud: a tick forgets no accepted block. -/
  tick_tree_mono : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t → n.tree ⊆ n'.tree
  /-- A tick keeps every attestation the node holds (the landed `AttPoolGrows`).

      Read aloud: a tick forgets no attestation. -/
  tick_pool : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t → ∀ a ∈ n.attestationsHeld, a ∈ n'.attestationsHeld
  /-- When every attestation on the chain of every block of `n`'s tree is held by `n`, the same
      holds after a tick (the landed `ChainsInPool`).

      Read aloud: a tick keeps the node holding every attestation on the chains of its tree. -/
  tick_chainsInPool : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t →
      (∀ Y ∈ n.tree, ∀ a : Attestation V, M.on_chain a Y = true → a ∈ n.attestationsHeld) →
        ∀ Y ∈ n'.tree, ∀ a : Attestation V, M.on_chain a Y = true → a ∈ n'.attestationsHeld
  /-- What a tick adds to the votes held is carried by an object it sent (the vote, or a block
      whose `votes` holds it), and what it adds to the tree is a block it sent, of a slot at most
      the slot of the clock after the tick (the landed `NewObjectsIn`).

      Read aloud: a tick adds to what the node holds only what it sent. -/
  tick_prov : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t →
      (∀ s : Slot, ∀ vote ∈ n'.votesHeld s, vote ∉ n.votesHeld s →
          ∃ o ∈ sent, o = NamedObject.gfVote vote ∨
            ∃ B : Block V, o = NamedObject.block B ∧ vote ∈ B.votes) ∧
        ∀ B ∈ n'.tree, B ∉ n.tree → NamedObject.block B ∈ sent ∧ B.slot ≤ C.slot n'.t
  /-- After a tick of `n` at `t` whose answer is `n'` and whose objects sent are `sent`, every
      attestation `n'` holds and `n` does not is an object of `sent`, or is included in a block of
      `sent`.

      Read aloud: a tick adds to the attestations held only what it sent, alone or inside a
      block. -/
  tick_prov_attestations : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V)
      (n : M.N) (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t →
      ∀ a ∈ n'.attestationsHeld, a ∉ n.attestationsHeld →
        NamedObject.attest a ∈ sent ∨ ∃ B : Block V, NamedObject.block B ∈ sent ∧ a ∈ B.attestations
  /-- From a node state satisfying the clock-free part of the model's node invariant, a tick gives a
      node state whose tree holds `n`'s, and whose finalized block is `n`'s or the finalized block of
      the chain state of a block of its tree (the landed `FinalizedFrom`).

      Read aloud: a tick finalizes only a block some accepted block's chain state finalizes. -/
  tick_finalizedFrom : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t → M.nodeInvCore C P X n →
      n.tree ⊆ n'.tree ∧
        (n'.finalized = n.finalized ∨ ∃ B ∈ n'.tree, n'.finalized = (M.chainStateOf C B).F)
  /-- From a node state satisfying the model's node invariant, a tick gives a node state whose
      justified block is `n`'s, or the justified block of the chain state of some block (the landed
      `JustifiedFrom`).

      Read aloud: a tick moves the justified block only to a block some chain state justifies. -/
  tick_justifiedFrom : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t → M.nodeInv C P X n →
      n'.justified = n.justified ∨ ∃ D : Block V, n'.justified = (M.chainStateOf C D).J
  /-- From a node state satisfying the model's node invariant, a tick gives a node state whose tree
      holds `n`'s, and which satisfies `CachesOnChainWith M C H OnChain` when `n` does and every
      block of its tree satisfies `JustifiedOnChainWith M C H OnChain` (the landed `CachesFrom`).

      Read aloud: a tick keeps the node's justification, justified at a height greater than `H`, on
      blocks satisfying `OnChain`, when every accepted block's justification is. -/
  tick_cachesFrom : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (H : ℕ)
      (OnChain : Block V → Prop) (n : M.N) (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t → M.nodeInv C P X n →
      n.tree ⊆ n'.tree ∧
        ((∀ B ∈ n'.tree, JustifiedOnChainWith M C H OnChain B) →
          CachesOnChainWith M C H OnChain n → CachesOnChainWith M C H OnChain n')
  /-- Every Goldfish vote a tick sends is of the node's validator, for the slot of `t`, and `t` is
      that slot's vote time; and a tick sends at most one Goldfish vote.

      Read aloud: a tick votes once, as itself, for the slot of its time, and only at that slot's
      vote time. -/
  tick_sends : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t →
      (∀ vote : GoldfishVote V, NamedObject.gfVote vote ∈ sent →
          vote.val_index = n.v ∧ vote.slot = C.slot t ∧ t = C.t_ (C.slot t) + C.Δ) ∧
        (sent.filter (fun o => match o with | NamedObject.gfVote _ => true | _ => false)).length ≤ 1
  /-- A tick at the vote time of the slot of `t`, whose answer has been awake since that slot's
      duty window started, of a member of that slot's committee, sends a Goldfish vote of the
      node's validator for that slot.

      Read aloud: at the vote time, an awake committee member's tick sends its vote. -/
  tick_emits_vote : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t → t = C.t_ (C.slot t) + C.Δ →
      M.awake_since n' (duty_window_start C (C.slot t)) = true → n.v ∈ P.committee (C.slot t) →
        ∃ h, NamedObject.gfVote (GoldfishVote.mk n.v (C.slot t) h) ∈ sent
  /-- A tick at the start of a slot other than slot `0`, of that slot's proposer, whose answer has
      been awake since that slot's proposal window started, sends a block.

      Read aloud: at a slot's start, an awake proposer's tick sends a block. -/
  tick_emits_proposal : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t → 0 < C.slot t → t = C.t_ (C.slot t) →
      n.v = P.proposer (C.slot t) →
      M.awake_since n' (proposal_window_start C (C.slot t)) = true →
        ∃ B : Block V, NamedObject.block B ∈ sent
  /-- A tick that sends an attestation has an answer awake since the duty window of the slot of
      `t` started.

      Read aloud: a tick attests only when the node has been awake since the duty window's
      start. -/
  tick_attest_awake : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t →
      ∀ a : Attestation V, NamedObject.attest a ∈ sent →
        M.awake_since n' (duty_window_start C (C.slot t)) = true
  /-- A block a tick sends is in the tree of its answer, when `n`'s votes of the previous slot have
      that slot and committee members as validators, no block of `n`'s tree has the block's root,
      every attestation `n` holds is well formed, the block's parent is in `n`'s tree, the block is
      `n`'s finalized block or a descendant of it, and the parent's slot is less than the slot of
      `t`.

      Read aloud: the node holds the block it proposes, when the block is new and passes the checks
      the proposal does not make itself. -/
  tick_proposal_mem_tree : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V)
      (n : M.N) (t : Time) (n' : M.N) (sent : List (NamedObject V)) (B : Block V),
    .ok (n', sent) ∈ M.tick C P X n t → NamedObject.block B ∈ sent →
      (∀ vote ∈ n.votesHeld (C.slot t - 1),
        vote.slot = C.slot t - 1 ∧ vote.val_index ∈ P.committee (C.slot t - 1)) →
      (∀ B' ∈ n.tree, B'.root ≠ B.root) →
      (∀ a ∈ n.attestationsHeld, M.attestation_well_formed a = true) →
      B.parent ∈ n.tree → n.finalized.AncestorEq B → B.parent.slot < C.slot t →
        B ∈ n'.tree
  /-- A tick sends at most one block.

      Read aloud: a tick proposes at most one block. -/
  tick_block_unique : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (t : Time) (n' : M.N) (sent : List (NamedObject V)) (B B' : Block V),
    .ok (n', sent) ∈ M.tick C P X n t → NamedObject.block B ∈ sent →
      NamedObject.block B' ∈ sent → B = B'
  /-- Every attestation content the answer of a tick has signed was signed by `n`, or is the
      content of an attestation the tick sent whose validator is `n`'s (the landed
      `RecordFromSent`).

      Read aloud: a tick signs only what it sends, as the node's validator. -/
  tick_record_rel : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t →
      ∀ b ∈ n'.sentAttestations, b ∈ n.sentAttestations ∨
        ∃ a : Attestation V, NamedObject.attest a ∈ sent ∧ a.content = b ∧ a.val_index = n.v
  /-- A tick keeps every attestation content the node has signed.

      Read aloud: a tick forgets nothing the node has signed. -/
  tick_record_grows : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t → n.sentAttestations ⊆ n'.sentAttestations

end GoldilocksCorrectness.Record
