module
public import GoldilocksCorrectness.Record.ModelSpellings
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickDefs

@[expose] public section

/-!
# The facts of the tick, part 3: what its duties send

`TickFacts3 M` holds, for a model `M`, what the objects a tick `M.tick C P X n t` sends are, of
every answer `(n', sent)` from a node state `n` satisfying the model's node invariant, and what the
validator client builds:

- T5, the Goldfish vote: it is sent at the vote time of the slot of `t`, as the node's validator,
  a member of that slot's committee, by a node awake since that slot's duty window started
  (`AwakeFor`); its head is the root of the end of the vote's walk (`HeadOf`) over `n`, from the
  anchor over `n`'s frame with the lock entries of `n'` (`AnchorAt`);
- T7, the block: it is sent at the start of a slot other than slot `0`, by that slot's proposer,
  awake since that slot's proposal window started (`AwakeForProposal`); its parent is the end of
  the walk counting `n`'s votes of the previous slot from `n`'s anchor (`PoolHeadOf`), and its
  content is those votes, those that resolve, the attestations a child of the parent includes, the
  digest and the node's validator;
- T8, the attestation: it is sent at the action time of the round of the slot of `t`, by a node
  awake since that slot's duty window started; its source is the deepest fast block of `n'` in the
  viable tree of `n`'s frame, its head the end of the walk counting `n`'s votes of the slot from
  the anchor over `n`'s frame with the lock entries of `n'`; it is what the validator client
  builds from the chain states of the source and the head (`AttestationFrom`), and the record of
  `n'` is `n`'s with it written in (`AttestationRecorded`); and, conversely, at the action time an
  awake node sends what the client builds there (T8b);
- what a tick holds after it: the Goldfish vote it sent, unless the node's votes of that slot
  already held two votes of its validator, and the attestation it sent;
- the validator client: what it builds at a height its record does not lock onto another block
  (Lemma 50), and the finality pair it attaches (Lemma 92).

The source, the head and the anchor of the attestation duty (the landed `ac_to_fg_source_fast`,
`ac_to_fg_source_mem`, `ac_to_fg_head_mem`, Lemmas 48, 48b) are consequences of these fields,
proved on `Record/Restated/Proofs/Routines/ACInterface.lean` and
`Record/Restated/Proofs/Routines/Attestation.lean`. The definitions are on
`Record/Restated/Statements/Routines/TickDefs.lean`. This file holds the structure only.
-/

set_option autoImplicit false
-- the hypotheses of the fields are named, as in the theorems the fields restate
set_option linter.unusedVariables false

open scoped DC

namespace GoldilocksCorrectness.Record

open Goldilocks (Config Provisional External RootOrder Block Attestation GoldfishVote NamedObject
  BlockId FinalityPair Height Slot Time Stamp)
open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor AwakeForProposal ResolvesAt
  AnchorAt HeadOf PoolHeadOf AttestationFrom AttestationRecorded)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The facts of `M` about the objects a tick sends, part 3, and about the attestation its
validator client builds.

Read aloud: the vote, the block and the attestation a tick sends are what the node's walks and its
validator client compute, each sent only by a node awake for its duty. -/
structure TickFacts3 (M : GoldilocksModel V) : Prop where
  /-- T5 (Lemma 14). A Goldfish vote `vote` that a tick sends, from a node state satisfying the
      model's node invariant, is sent at the vote time of the slot of `t`; it is the node's
      validator's vote for that slot; the validator is in that slot's committee; the node has been
      awake since that slot's duty window started; and `vote.head` is the root of the end `H` of
      the walk of the Goldfish vote of that slot over `n` (`HeadOf`), from the anchor over `n`'s
      frame with the lock entries of `n'` (`AnchorAt M (M.fg_to_ac n) n'.lockEntries t`).

      Read aloud: a vote a tick sends is an awake committee member's vote at the vote time, for
      the root of the end of its walk from the anchor its revoked locks give. -/
  tick_vote_head : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (t : Time) (n' : M.N) (sent : List (NamedObject V)) (vote : GoldfishVote V),
    .ok (n', sent) ∈ M.tick C P X n t → M.nodeInv C P X n → NamedObject.gfVote vote ∈ sent →
      t = C.t_ (C.slot t) + C.Δ ∧ vote.val_index = n.v ∧ vote.slot = C.slot t ∧
        n.v ∈ P.committee (C.slot t) ∧ AwakeFor M C n (C.slot t) ∧
        ∃ H : Block V, HeadOf M C n (AnchorAt M (M.fg_to_ac n) n'.lockEntries t) t (C.slot t) H ∧
          vote.head = H.root
  /-- T7 (Lemma 19). A block `B` that a tick sends, from a node state satisfying the model's node
      invariant, is sent at the start of the slot of `t`, a slot other than slot `0`, by that
      slot's proposer, awake since that slot's proposal window started; and `B` is the block of
      that slot whose parent `H` is the end of the walk counting `n`'s votes of the previous slot
      from `n`'s anchor (`PoolHeadOf M C n (M.get_anchor n t) t (C.slot t - 1) H`), whose votes are
      `n`'s list `votes` of the previous slot, whose support votes are a list `support_votes` of
      exactly those of `votes` that resolve in `n`, whose attestations are those a child of `H`
      includes (`M.proposal_attestations n H`), whose root is the digest of that content, and
      whose proposer is the node's validator.

      Read aloud: a block a tick sends is the awake proposer's block at its slot's start, built on
      the end of the walk from the node's anchor, with the node's votes of the previous slot. -/
  tick_proposal : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (t : Time) (n' : M.N) (sent : List (NamedObject V)) (B : Block V),
    .ok (n', sent) ∈ M.tick C P X n t → M.nodeInv C P X n → NamedObject.block B ∈ sent →
      0 < C.slot t ∧ t = C.t_ (C.slot t) ∧ n.v = P.proposer (C.slot t) ∧
        AwakeForProposal M C n (C.slot t) ∧
        ∃ (H : Block V) (votes support_votes : List (GoldfishVote V)),
          votes = n.votesHeld (C.slot t - 1) ∧
          (∀ vote : GoldfishVote V, vote ∈ support_votes ↔
            vote ∈ votes ∧ ∃ y : Stamp, ResolvesAt M n vote y) ∧
          PoolHeadOf M C n (M.get_anchor n t) t (C.slot t - 1) H ∧
          B = Block.node H (C.slot t)
            (X.digest H.root (C.slot t) (M.proposal_attestations n H) votes support_votes)
            votes support_votes (M.proposal_attestations n H) n.v
  /-- T8 (Lemma 49). An attestation `a` that a tick sends, from a node state satisfying the model's
      node invariant, is sent at the action time of the round of the slot of `t`, by a node awake
      since that slot's duty window started; and for some `source` and `head`: `source` is the
      deepest fast block of `n'` in the viable tree of the tree of `n`'s frame; `head` is the end
      of the walk counting `n`'s votes of the slot of `t` from the anchor over `n`'s frame with the
      lock entries of `n'` (`PoolHeadOf`); `a` is what `n`'s validator client builds for the
      node's validator from the height and the root of the block that took `source`'s chain state
      into that height, and the justification height, justified root and finalization height of
      `head`'s chain state (`AttestationFrom`); and the record of `n'` is `n`'s with `a` written
      into it (`AttestationRecorded`).

      Read aloud: an attestation a tick sends is the awake node's attestation at the round's action
      time, built by its validator client from the deepest fast block in the viable tree and the
      end of the walk, and the node records it. -/
  tick_attestation : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (t : Time) (n' : M.N) (sent : List (NamedObject V)) (a : Attestation V),
    .ok (n', sent) ∈ M.tick C P X n t → M.nodeInv C P X n → NamedObject.attest a ∈ sent →
      t = C.a_ (C.round (C.slot t)) ∧ AwakeFor M C n (C.slot t) ∧
        ∃ source head : Block V,
          Block.deepest? (n'.fastBlocks ∩ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree) =
            some source ∧
          PoolHeadOf M C n (AnchorAt M (M.fg_to_ac n) n'.lockEntries t) t (C.slot t) head ∧
          AttestationFrom M n n.v (M.chainStateOf C source).h (M.chainStateOf C source).T_h.root
            (M.chainStateOf C head).h_j (M.chainStateOf C head).J.root
            (M.chainStateOf C head).h_F a ∧
          AttestationRecorded M n a n'
  /-- T8b (Lemma 49b). A tick at the action time of the round of the slot of `t`, from a node
      state satisfying the model's node invariant and awake since that slot's duty window started,
      sends the attestation `a` the validator client builds from the deepest fast block `source`
      of `n'` in the viable tree of the tree of `n`'s frame and the end `head` of the walk counting
      `n`'s votes of the slot from the anchor over `n`'s frame with the lock entries of `n'`.

      Read aloud: at the action time, an awake node with a source sends what its validator client
      builds. -/
  tick_attestation_sent : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V)
      (n : M.N) (t : Time) (n' : M.N) (sent : List (NamedObject V)) (a : Attestation V)
      (source head : Block V),
    .ok (n', sent) ∈ M.tick C P X n t → M.nodeInv C P X n → t = C.a_ (C.round (C.slot t)) →
      AwakeFor M C n (C.slot t) →
      Block.deepest? (n'.fastBlocks ∩ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree) =
        some source →
      PoolHeadOf M C n (AnchorAt M (M.fg_to_ac n) n'.lockEntries t) t (C.slot t) head →
      AttestationFrom M n n.v (M.chainStateOf C source).h (M.chainStateOf C source).T_h.root
        (M.chainStateOf C head).h_j (M.chainStateOf C head).J.root
        (M.chainStateOf C head).h_F a →
      NamedObject.attest a ∈ sent
  /-- A tick holds what it sends. After a tick from a node state
      satisfying the model's node invariant, a Goldfish vote the tick sent is among the node's
      votes of the vote's slot, unless the node's votes of that slot already held, before the tick,
      two distinct votes of the vote's validator (`M.equivocates`, the case in which the node
      refuses a vote on a delivery too, `receive_gfVote_cases`); and an attestation the tick sent
      is among the node's held attestations.

      Read aloud: after a tick, the node holds the vote it sent, unless its votes of that slot
      already held two votes of its own validator, and it holds the attestation it sent. -/
  tick_holds_sent : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t → M.nodeInv C P X n →
      (∀ vote : GoldfishVote V, NamedObject.gfVote vote ∈ sent →
        vote ∈ M.votesHeldSet n' vote.slot ∨
          M.equivocates (M.votesHeldSet n vote.slot) vote.val_index = true) ∧
      (∀ a : Attestation V, NamedObject.attest a ∈ sent → a ∈ M.attestationsHeld n')
  /-- Lemma 50. For the node state `n`, the validator `v`, a source at the height `h_c` with the
      root `T_c`, and a head with the justification height `h_j`, the justified root `J` and the
      finalization height `h_F`: when `n`'s record holds no lock at `h_c`, or holds the lock `T_c`
      there and every attestation it sent at `h_c` names `T_c`; when `J = T_c` if `h_j = h_c`; and
      when every target the record holds was sent, every target it sent is recorded and every
      timeout it sent is recorded, then the validator client builds an attestation of `v` at `h_c`
      naming `T_c` (`AttestationFrom`), or builds none and the record already sent an attestation
      at `h_c` naming `T_c`. And when nothing the record sent is at `h_c`, and it holds no timeout
      and no target there, it builds a target.

      Read aloud: a validator whose record does not lock it onto another block at the source's
      height sends a vote for `(h_c, T_c)`, unless it already has; at a fresh height the vote is a
      target. -/
  attestation_sent_at_source : ∀ (n : M.N) (v : V) (h_c : Height) (T_c : BlockId) (h_j : Height)
      (J : BlockId) (h_F : Height),
    (n.sentLock h_c = none ∨
      (n.sentLock h_c = some T_c ∧ ∀ b ∈ n.sentAttestations, b.h = h_c → b.T = T_c)) →
    (h_j = h_c → J = T_c) →
    (∀ (h : Height) (T : BlockId), n.sentTarget h = some T →
      ∃ b ∈ n.sentAttestations, b.h = h ∧ b.T = T) →
    (∀ b ∈ n.sentAttestations, b.τ = false → n.sentTarget b.h ≠ none) →
    (∀ b ∈ n.sentAttestations, b.τ = true → n.sentTimeout b.h = true) →
    ((∃ a : Attestation V, AttestationFrom M n v h_c T_c h_j J h_F a ∧
        a.val_index = v ∧ a.h = h_c ∧ a.T = T_c) ∨
      ((∀ a : Attestation V, ¬ AttestationFrom M n v h_c T_c h_j J h_F a) ∧
        ∃ b ∈ n.sentAttestations, b.h = h_c ∧ b.T = T_c)) ∧
    ((∀ b ∈ n.sentAttestations, b.h ≠ h_c) → n.sentTimeout h_c = false →
      n.sentTarget h_c = none →
      ∃ a : Attestation V, AttestationFrom M n v h_c T_c h_j J h_F a ∧
        a.val_index = v ∧ a.h = h_c ∧ a.T = T_c ∧ a.τ = false)
  /-- Lemma 92. An attestation the validator client of `n` builds (`AttestationFrom`), from a head
      whose justification at `h_j` is not finalized (`h_F < h_j`), at a source height `h_c` greater
      than `h_j`, where `n`'s record holds at `h_j` no target or the target `J`, no timeout, and
      no lock or the lock `J`, is at `h_c` and carries the finality pair `(h_j, J)`.

      Read aloud: an attestation built from a record clean at the justification height carries
      the finality pair of the justification. -/
  attestation_carries_finality_pair : ∀ (n : M.N) (v : V) (h_c : Height) (T_c : BlockId)
      (h_j : Height) (J : BlockId) (h_F : Height) (a : Attestation V),
    AttestationFrom M n v h_c T_c h_j J h_F a → h_F < h_j → h_j < h_c →
    (n.sentTarget h_j = none ∨ n.sentTarget h_j = some J) → n.sentTimeout h_j = false →
    (n.sentLock h_j = none ∨ n.sentLock h_j = some J) →
      a.h = h_c ∧ a.finality_pair = some (FinalityPair.mk h_j J)

end GoldilocksCorrectness.Record
