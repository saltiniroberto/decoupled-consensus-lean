module
public import GoldilocksCorrectness.Record.Model
public import GoldilocksCorrectness.Record.SlotLayoutProbes
public import GoldilocksCorrectness.Statements.Routines.NodeDefs
public import GoldilocksCorrectness.Statements.Routines.NodeCoreDefs
public import GoldilocksCorrectness.Statements.Routines.HeightCacheAttainedDefs
public import GoldilocksCorrectness.Proofs.Routines.WalkEndBridge
import all GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-!
# The spec as a model of the record

`Model.goldilocks` fills every member of `GoldilocksModel V` with the spec's definition: the slot
layout `SlotLayout.goldilocks`, each type member the spec's structure, each reader of a node state
the spec's field of the node state's FG state `n.S`, AC state `n.A` or anti-slashing record `n.Λ`
(or of `n` itself), each derived reader the spec's reader applied to those parts of `n`, each
operation the spec's routine, and each duty that broadcasts the set of outcomes of the spec's duty
(`DREB.outcomes`). Three members are the library's definitions: `nodeInv` is `NodeInv` together
with `HeightCacheAttained` of the node's FG state (the stored greatest height `n.S.h_max` is the
chain-state height of a block of the tree), and `chainStateOf` is `chainStateOf`, all of
`Statements/Routines/`; and the tie-break `tieBreak` is `goldilocksTieBreak`
(`Proofs/Routines/WalkEndBridge.lean`), named here and not made an instance.

The simp set `record_goldilocks` holds the equations between a definition of the library or the
spec and its form over the record at `Model.goldilocks`, the landed form on the left. Each holds
by definition.
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Record

open DC (DRE)
open Goldilocks (Config Provisional External RootOrder Block Attestation AttestationContent
  GoldfishVote NamedObject Frame FinalityPair HeightPair BlockId Height Slot Time Stamp Occurrence
  ChainState PendingPair LockEntry NodeState DREB)
open GoldilocksCorrectness.Statements.Routines (TieBreak NodeInv NodeInvCore HeightCacheAttained)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The spec's model: every member is the spec's definition, and every duty that broadcasts is the
set of outcomes of the spec's duty.

Read aloud: Goldilocks, as a model of the record. -/
noncomputable def Model.goldilocks : GoldilocksModel V where
-- BEGIN GENERATED instance
  toSlotLayout := SlotLayout.goldilocks
  CS := ChainState V
  PP := PendingPair V
  LE := LockEntry V
  N := NodeState V
  initial C v := Goldilocks.initial C v
  wake n t := Goldilocks.wake n t
  tick C P X n t := (Goldilocks.tick C P X n t).outcomes
  receive C P X n o := Goldilocks.Sts.receive C P X n o
  relayedObjects o := Goldilocks.Sts.relayedObjects o
  validator n := n.v
  clock n := n.t
  awakeSince n := n.awakeSince
  tree n := n.S.T
  finalized n := n.S.F
  justified n := n.S.J
  justifiedHeight n := n.S.h_j
  attestationsHeld n := n.S.attestations
  votesHeld n s := n.A.gf_votes s
  voteStamp n vote := n.A.timestamp_vote vote
  blockStamp n B := n.A.timestamp_block B
  savedConfirmation n s := n.A.saved_confirmation s
  lockEntries n := n.A.lock_entries
  fastBlocks n := n.A.fast_blocks
  latestConfirmed n := n.A.latest_confirmed
  sentTarget n h := n.Λ.target h
  sentTimeout n h := n.Λ.timeout h
  sentLock n h := n.Λ.lock h
  sentAttestations n := n.Λ.sent
  nodeInv C P X n := (NodeInv C P X n ∧ HeightCacheAttained n.S)
  nodeInvCore C P X n := (NodeInvCore C P X n ∧ HeightCacheAttained n.S)
  chainStateOf C B := GoldilocksCorrectness.Statements.Routines.chainStateOf C B
  cs_L σ := Goldilocks.ChainState.L σ
  cs_s σ := Goldilocks.ChainState.s σ
  cs_h σ := Goldilocks.ChainState.h σ
  cs_T_h σ := Goldilocks.ChainState.T_h σ
  cs_target_participation σ := Goldilocks.ChainState.target_participation σ
  cs_progress σ := Goldilocks.ChainState.progress σ
  cs_pending_finality σ := Goldilocks.ChainState.pending_finality σ
  cs_finality_participation σ j := Goldilocks.ChainState.finality_participation σ j
  cs_J σ := Goldilocks.ChainState.J σ
  cs_h_j σ := Goldilocks.ChainState.h_j σ
  cs_F σ := Goldilocks.ChainState.F σ
  cs_h_F σ := Goldilocks.ChainState.h_F σ
  pp_j e := Goldilocks.PendingPair.j e
  pp_T e := Goldilocks.PendingPair.T e
  is_pending σ p := Goldilocks.is_pending σ p
  valid_attestation σ a := Goldilocks.valid_attestation σ a
  newest K_W l := Goldilocks.newest K_W l
  le_B e := Goldilocks.LockEntry.B e
  le_d e := Goldilocks.LockEntry.d e
  fg_contest n := Goldilocks.fg_contest n.S
  head_height_floor n := Goldilocks.head_height_floor n.S
  get_fc_root n := Goldilocks.get_fc_root n.S
  is_viable n B := Goldilocks.is_viable n.S B
  has_viable_descendant n B := Goldilocks.has_viable_descendant n.S B
  fg_to_ac n := Goldilocks.fg_to_ac n.S
  proposal_attestations n H := Goldilocks.proposal_attestations n.S H
  finality_pair n h_j J h_F := Goldilocks.finality_pair n.Λ h_j J h_F
  own_lock n h_c fp := Goldilocks.own_lock n.Λ h_c fp
  height_pair n fields fp := Goldilocks.height_pair n.Λ fields fp
  already_sent n h T τ := Goldilocks.already_sent n.Λ h T τ
  votesHeldSet n s := n.A.pool s
  is_live n t e := Goldilocks.is_live (Goldilocks.fg_to_ac n.S) t e
  is_locked n t B' := Goldilocks.is_locked n.A (Goldilocks.fg_to_ac n.S) t B'
  live_lock_vetoes n t C := Goldilocks.live_lock_vetoes n.A (Goldilocks.fg_to_ac n.S) t C
  get_anchor n t := Goldilocks.get_anchor n.A (Goldilocks.fg_to_ac n.S) t
  tieBreak := GoldilocksCorrectness.Proofs.Routines.goldilocksTieBreak
  live_entries n t := Goldilocks.live_entries n.A (Goldilocks.fg_to_ac n.S) t
  saved_extends n s'' B := Goldilocks.saved_extends n.A (Goldilocks.fg_to_ac n.S) s'' B
  slow_test C n s' B := Goldilocks.slow_test C n.A (Goldilocks.fg_to_ac n.S) s' B
  ac_confirmed n := Goldilocks.ac_confirmed n.A (Goldilocks.fg_to_ac n.S)
  awake_since n t₀ := n.awake_since t₀
  block_admissible C P X n B := Goldilocks.block_admissible C P X n B
  attestations_on_chain B := Goldilocks.attestations_on_chain B
  on_chain a H := Goldilocks.on_chain a H
  hp_height? p := Goldilocks.HeightPair.height? p
  hp_target? p := Goldilocks.HeightPair.target? p
  ac_valid_payload P B := Goldilocks.ac_valid_payload P B
  included_votes Φ s := Goldilocks.included_votes Φ s
  included_support_votes Φ s := Goldilocks.included_support_votes Φ s
  votes_by votes v := Goldilocks.votes_by votes v
  equivocates votes v := Goldilocks.equivocates votes v
  participates votes v := Goldilocks.participates votes v
  no_second_vote_in late vote := Goldilocks.no_second_vote_in late vote
  equivocators votes := Goldilocks.equivocators votes
  participants votes := Goldilocks.participants votes
  voters_count votes := Goldilocks.voters_count votes
  viable_tree Φ tree := Goldilocks.viable_tree Φ tree
  present S := Goldilocks.present S
  advance Φ old C? := Goldilocks.advance Φ old C?
  slots_before s' k := Goldilocks.slots_before s' k
  attestation_well_formed a := Goldilocks.attestation_well_formed a
  block_well_formed P X B := Goldilocks.block_well_formed P X B
-- END GENERATED instance

/-! ## The slot layout's equations -/

open GoldilocksCorrectness.Statements.Routines (slotStart) in
/-- At the spec's model, `slotStart S s` is the member `slotStart` at `S.C`.

Read aloud: the spec's model has the library's times. -/
@[record_goldilocks]
theorem goldilocks_slotStart (S : Goldilocks.Sts.Setup V) (s : ℕ) :
    slotStart S s = (Model.goldilocks (V := V)).slotStart S.C s := by rfl

open GoldilocksCorrectness.Statements.Routines (voteTime) in
/-- At the spec's model, `voteTime S s` is the member `voteTime` at `S.C`. -/
@[record_goldilocks]
theorem goldilocks_voteTime (S : Goldilocks.Sts.Setup V) (s : ℕ) :
    voteTime S s = (Model.goldilocks (V := V)).voteTime S.C s := by rfl

open GoldilocksCorrectness.Statements.Routines (supportCutoff) in
/-- At the spec's model, `supportCutoff S s` is the member `supportCutoff` at `S.C`. -/
@[record_goldilocks]
theorem goldilocks_supportCutoff (S : Goldilocks.Sts.Setup V) (s : ℕ) :
    supportCutoff S s = (Model.goldilocks (V := V)).supportCutoff S.C s := by rfl

open GoldilocksCorrectness.Statements.Routines (viewFreeze) in
/-- At the spec's model, `viewFreeze S s` is the member `viewFreeze` at `S.C`. -/
@[record_goldilocks]
theorem goldilocks_viewFreeze (S : Goldilocks.Sts.Setup V) (s : ℕ) :
    viewFreeze S s = (Model.goldilocks (V := V)).viewFreeze S.C s := by rfl

open GoldilocksCorrectness.Statements.Routines (lateVoteCutoff) in
/-- At the spec's model, `lateVoteCutoff S s` is the member `lateVoteCutoff` at `S.C`. -/
@[record_goldilocks]
theorem goldilocks_lateVoteCutoff (S : Goldilocks.Sts.Setup V) (s : ℕ) :
    lateVoteCutoff S s = (Model.goldilocks (V := V)).lateVoteCutoff S.C s := by rfl

open GoldilocksCorrectness.Statements.Routines (dutyWindowStart) in
/-- At the spec's model, `dutyWindowStart S s` is the member `dutyWindowStart` at `S.C`. -/
@[record_goldilocks]
theorem goldilocks_dutyWindowStart (S : Goldilocks.Sts.Setup V) (s : ℕ) :
    dutyWindowStart S s = (Model.goldilocks (V := V)).dutyWindowStart S.C s := by rfl

open GoldilocksCorrectness.Statements.Routines (proposalWindowStart) in
/-- At the spec's model, `proposalWindowStart S s` is the member `proposalWindowStart` at
`S.C`. -/
@[record_goldilocks]
theorem goldilocks_proposalWindowStart (S : Goldilocks.Sts.Setup V) (s : ℕ) :
    proposalWindowStart S s = (Model.goldilocks (V := V)).proposalWindowStart S.C s := by rfl

/-- At the spec's model, the slot of a natural-number time `t` is `S.C.slot (t : Int)`. -/
@[record_goldilocks]
theorem goldilocks_slot (S : Goldilocks.Sts.Setup V) (t : ℕ) :
    S.C.slot (t : Int) = (Model.goldilocks (V := V)).slot S.C t := rfl

/-- At the spec's model, every block's validator set is every validator. -/
@[record_goldilocks]
theorem goldilocks_validators (B : Block V) :
    (Finset.univ : Finset V) = (Model.goldilocks (V := V)).validators B := rfl

/-- At the spec's model, every block's quorum is `quorum V`. -/
@[record_goldilocks]
theorem goldilocks_quorumAt (B : Block V) :
    Goldilocks.quorum V = (Model.goldilocks (V := V)).quorumAt B := rfl

/-! ## The members' equations -/

-- BEGIN GENERATED equations
/-- At the spec's model, the member `initial` is `Goldilocks.initial`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_initial (C : Config) (v : V) :
    Goldilocks.initial C v =
      (Model.goldilocks (V := V)).initial C v := rfl

/-- At the spec's model, the member `wake` is `Goldilocks.wake`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_wake (n : NodeState V) (t : Time) :
    Goldilocks.wake n t =
      (Model.goldilocks (V := V)).wake n t := rfl

/-- At the spec's model, the member `relayedObjects` is `Goldilocks.Sts.relayedObjects`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_relayedObjects (o : NamedObject V) :
    Goldilocks.Sts.relayedObjects o =
      (Model.goldilocks (V := V)).relayedObjects o := rfl

/-- At the spec's model, the member `validator` is `Goldilocks.NodeState.v`, read on the node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_validator (n : NodeState V) :
    n.v =
      (Model.goldilocks (V := V)).validator n := rfl

/-- At the spec's model, the member `clock` is `Goldilocks.NodeState.t`, read on the node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_clock (n : NodeState V) :
    n.t =
      (Model.goldilocks (V := V)).clock n := rfl

/-- At the spec's model, the member `awakeSince` is `Goldilocks.NodeState.awakeSince`, read on the
node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_awakeSince (n : NodeState V) :
    n.awakeSince =
      (Model.goldilocks (V := V)).awakeSince n := rfl

/-- At the spec's model, the member `tree` is `Goldilocks.FGState.T`, read on the node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_tree (n : NodeState V) :
    n.S.T =
      (Model.goldilocks (V := V)).tree n := rfl

/-- At the spec's model, the member `finalized` is `Goldilocks.FGState.F`, read on the node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_finalized (n : NodeState V) :
    n.S.F =
      (Model.goldilocks (V := V)).finalized n := rfl

/-- At the spec's model, the member `justified` is `Goldilocks.FGState.J`, read on the node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_justified (n : NodeState V) :
    n.S.J =
      (Model.goldilocks (V := V)).justified n := rfl

/-- At the spec's model, the member `justifiedHeight` is `Goldilocks.FGState.h_j`, read on the node
state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_justifiedHeight (n : NodeState V) :
    n.S.h_j =
      (Model.goldilocks (V := V)).justifiedHeight n := rfl

/-- At the spec's model, the member `attestationsHeld` is `Goldilocks.FGState.attestations`, read on
the node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_attestationsHeld (n : NodeState V) :
    n.S.attestations =
      (Model.goldilocks (V := V)).attestationsHeld n := rfl

/-- At the spec's model, the member `votesHeld` is `Goldilocks.ACState.gf_votes`, read on the node
state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_votesHeld (n : NodeState V) (s : Slot) :
    n.A.gf_votes s =
      (Model.goldilocks (V := V)).votesHeld n s := rfl

/-- At the spec's model, the member `voteStamp` is `Goldilocks.ACState.timestamp_vote`, read on the
node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_voteStamp (n : NodeState V) (vote : GoldfishVote V) :
    n.A.timestamp_vote vote =
      (Model.goldilocks (V := V)).voteStamp n vote := rfl

/-- At the spec's model, the member `blockStamp` is `Goldilocks.ACState.timestamp_block`, read on
the node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_blockStamp (n : NodeState V) (B : Block V) :
    n.A.timestamp_block B =
      (Model.goldilocks (V := V)).blockStamp n B := rfl

/-- At the spec's model, the member `savedConfirmation` is `Goldilocks.ACState.saved_confirmation`,
read on the node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_savedConfirmation (n : NodeState V) (s : Slot) :
    n.A.saved_confirmation s =
      (Model.goldilocks (V := V)).savedConfirmation n s := rfl

/-- At the spec's model, the member `lockEntries` is `Goldilocks.ACState.lock_entries`, read on the
node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_lockEntries (n : NodeState V) :
    n.A.lock_entries =
      (Model.goldilocks (V := V)).lockEntries n := rfl

/-- At the spec's model, the member `fastBlocks` is `Goldilocks.ACState.fast_blocks`, read on the
node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_fastBlocks (n : NodeState V) :
    n.A.fast_blocks =
      (Model.goldilocks (V := V)).fastBlocks n := rfl

/-- At the spec's model, the member `latestConfirmed` is `Goldilocks.ACState.latest_confirmed`, read
on the node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_latestConfirmed (n : NodeState V) :
    n.A.latest_confirmed =
      (Model.goldilocks (V := V)).latestConfirmed n := rfl

/-- At the spec's model, the member `sentTarget` is `Goldilocks.SigningHistory.target`, read on the
node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_sentTarget (n : NodeState V) (h : Height) :
    n.Λ.target h =
      (Model.goldilocks (V := V)).sentTarget n h := rfl

/-- At the spec's model, the member `sentTimeout` is `Goldilocks.SigningHistory.timeout`, read on
the node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_sentTimeout (n : NodeState V) (h : Height) :
    n.Λ.timeout h =
      (Model.goldilocks (V := V)).sentTimeout n h := rfl

/-- At the spec's model, the member `sentLock` is `Goldilocks.SigningHistory.lock`, read on the node
state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_sentLock (n : NodeState V) (h : Height) :
    n.Λ.lock h =
      (Model.goldilocks (V := V)).sentLock n h := rfl

/-- At the spec's model, the member `sentAttestations` is `Goldilocks.SigningHistory.sent`, read on
the node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_sentAttestations (n : NodeState V) :
    n.Λ.sent =
      (Model.goldilocks (V := V)).sentAttestations n := rfl

/-- At the spec's model, the member `nodeInv` is the library's `NodeInv` together with the library's
`HeightCacheAttained` of the node's FG state, read on the node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_nodeInv (C : Config) (P : Provisional V) (X : External V) (n : NodeState V) :
    (NodeInv C P X n ∧ HeightCacheAttained n.S) =
      (Model.goldilocks (V := V)).nodeInv C P X n := rfl

/-- At the spec's model, the member `nodeInvCore` is the library's `NodeInvCore` together with the
library's `HeightCacheAttained` of the node's FG state, read on the node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_nodeInvCore (C : Config) (P : Provisional V) (X : External V) (n : NodeState V) :
    (NodeInvCore C P X n ∧ HeightCacheAttained n.S) =
      (Model.goldilocks (V := V)).nodeInvCore C P X n := rfl

/-- At the spec's model, the member `chainStateOf` is
`GoldilocksCorrectness.Statements.Routines.chainStateOf`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_chainStateOf (C : Config) (B : Block V) :
    GoldilocksCorrectness.Statements.Routines.chainStateOf C B =
      (Model.goldilocks (V := V)).chainStateOf C B := rfl

/-- At the spec's model, the member `cs_L` is `Goldilocks.ChainState.L`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_cs_L (σ : ChainState V) :
    Goldilocks.ChainState.L σ =
      (Model.goldilocks (V := V)).cs_L σ := rfl

/-- At the spec's model, the member `cs_s` is `Goldilocks.ChainState.s`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_cs_s (σ : ChainState V) :
    Goldilocks.ChainState.s σ =
      (Model.goldilocks (V := V)).cs_s σ := rfl

/-- At the spec's model, the member `cs_h` is `Goldilocks.ChainState.h`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_cs_h (σ : ChainState V) :
    Goldilocks.ChainState.h σ =
      (Model.goldilocks (V := V)).cs_h σ := rfl

/-- At the spec's model, the member `cs_T_h` is `Goldilocks.ChainState.T_h`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_cs_T_h (σ : ChainState V) :
    Goldilocks.ChainState.T_h σ =
      (Model.goldilocks (V := V)).cs_T_h σ := rfl

/-- At the spec's model, the member `cs_target_participation` is
`Goldilocks.ChainState.target_participation`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_cs_target_participation (σ : ChainState V) :
    Goldilocks.ChainState.target_participation σ =
      (Model.goldilocks (V := V)).cs_target_participation σ := rfl

/-- At the spec's model, the member `cs_progress` is `Goldilocks.ChainState.progress`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_cs_progress (σ : ChainState V) :
    Goldilocks.ChainState.progress σ =
      (Model.goldilocks (V := V)).cs_progress σ := rfl

/-- At the spec's model, the member `cs_pending_finality` is
`Goldilocks.ChainState.pending_finality`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_cs_pending_finality (σ : ChainState V) :
    Goldilocks.ChainState.pending_finality σ =
      (Model.goldilocks (V := V)).cs_pending_finality σ := rfl

/-- At the spec's model, the member `cs_finality_participation` is
`Goldilocks.ChainState.finality_participation`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_cs_finality_participation (σ : ChainState V) (j : Height) :
    Goldilocks.ChainState.finality_participation σ j =
      (Model.goldilocks (V := V)).cs_finality_participation σ j := rfl

/-- At the spec's model, the member `cs_J` is `Goldilocks.ChainState.J`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_cs_J (σ : ChainState V) :
    Goldilocks.ChainState.J σ =
      (Model.goldilocks (V := V)).cs_J σ := rfl

/-- At the spec's model, the member `cs_h_j` is `Goldilocks.ChainState.h_j`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_cs_h_j (σ : ChainState V) :
    Goldilocks.ChainState.h_j σ =
      (Model.goldilocks (V := V)).cs_h_j σ := rfl

/-- At the spec's model, the member `cs_F` is `Goldilocks.ChainState.F`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_cs_F (σ : ChainState V) :
    Goldilocks.ChainState.F σ =
      (Model.goldilocks (V := V)).cs_F σ := rfl

/-- At the spec's model, the member `cs_h_F` is `Goldilocks.ChainState.h_F`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_cs_h_F (σ : ChainState V) :
    Goldilocks.ChainState.h_F σ =
      (Model.goldilocks (V := V)).cs_h_F σ := rfl

/-- At the spec's model, the member `pp_j` is `Goldilocks.PendingPair.j`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_pp_j (e : PendingPair V) :
    Goldilocks.PendingPair.j e =
      (Model.goldilocks (V := V)).pp_j e := rfl

/-- At the spec's model, the member `pp_T` is `Goldilocks.PendingPair.T`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_pp_T (e : PendingPair V) :
    Goldilocks.PendingPair.T e =
      (Model.goldilocks (V := V)).pp_T e := rfl

/-- At the spec's model, the member `is_pending` is `Goldilocks.is_pending`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_is_pending (σ : ChainState V) (p : FinalityPair) :
    Goldilocks.is_pending σ p =
      (Model.goldilocks (V := V)).is_pending σ p := rfl

/-- At the spec's model, the member `valid_attestation` is `Goldilocks.valid_attestation`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_valid_attestation (σ : ChainState V) (a : Attestation V) :
    Goldilocks.valid_attestation σ a =
      (Model.goldilocks (V := V)).valid_attestation σ a := rfl

/-- At the spec's model, the member `newest` is `Goldilocks.newest`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_newest (K_W : ℕ) (l : List (PendingPair V)) :
    Goldilocks.newest K_W l =
      (Model.goldilocks (V := V)).newest K_W l := rfl

/-- At the spec's model, the member `le_B` is `Goldilocks.LockEntry.B`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_le_B (e : LockEntry V) :
    Goldilocks.LockEntry.B e =
      (Model.goldilocks (V := V)).le_B e := rfl

/-- At the spec's model, the member `le_d` is `Goldilocks.LockEntry.d`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_le_d (e : LockEntry V) :
    Goldilocks.LockEntry.d e =
      (Model.goldilocks (V := V)).le_d e := rfl

/-- At the spec's model, the member `fg_contest` is `Goldilocks.fg_contest`, read on the node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_fg_contest (n : NodeState V) :
    Goldilocks.fg_contest n.S =
      (Model.goldilocks (V := V)).fg_contest n := rfl

/-- At the spec's model, the member `head_height_floor` is `Goldilocks.head_height_floor`, read on
the node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_head_height_floor (n : NodeState V) :
    Goldilocks.head_height_floor n.S =
      (Model.goldilocks (V := V)).head_height_floor n := rfl

/-- At the spec's model, the member `get_fc_root` is `Goldilocks.get_fc_root`, read on the node
state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_get_fc_root (n : NodeState V) :
    Goldilocks.get_fc_root n.S =
      (Model.goldilocks (V := V)).get_fc_root n := rfl

/-- At the spec's model, the member `is_viable` is `Goldilocks.is_viable`, read on the node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_is_viable (n : NodeState V) (B : Block V) :
    Goldilocks.is_viable n.S B =
      (Model.goldilocks (V := V)).is_viable n B := rfl

/-- At the spec's model, the member `has_viable_descendant` is `Goldilocks.has_viable_descendant`,
read on the node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_has_viable_descendant (n : NodeState V) (B : Block V) :
    Goldilocks.has_viable_descendant n.S B =
      (Model.goldilocks (V := V)).has_viable_descendant n B := rfl

/-- At the spec's model, the member `fg_to_ac` is `Goldilocks.fg_to_ac`, read on the node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_fg_to_ac (n : NodeState V) :
    Goldilocks.fg_to_ac n.S =
      (Model.goldilocks (V := V)).fg_to_ac n := rfl

/-- At the spec's model, the member `proposal_attestations` is `Goldilocks.proposal_attestations`,
read on the node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_proposal_attestations (n : NodeState V) (H : Block V) :
    Goldilocks.proposal_attestations n.S H =
      (Model.goldilocks (V := V)).proposal_attestations n H := rfl

/-- At the spec's model, the member `finality_pair` is `Goldilocks.finality_pair`, read on the node
state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_finality_pair (n : NodeState V) (h_j : Height) (J : BlockId) (h_F : Height) :
    Goldilocks.finality_pair n.Λ h_j J h_F =
      (Model.goldilocks (V := V)).finality_pair n h_j J h_F := rfl

/-- At the spec's model, the member `own_lock` is `Goldilocks.own_lock`, read on the node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_own_lock (n : NodeState V) (h_c : Height) (fp : Option FinalityPair) :
    Goldilocks.own_lock n.Λ h_c fp =
      (Model.goldilocks (V := V)).own_lock n h_c fp := rfl

/-- At the spec's model, the member `height_pair` is `Goldilocks.height_pair`, read on the node
state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_height_pair (n : NodeState V) (fields : Option (Height × BlockId))
    (fp : Option FinalityPair) :
    Goldilocks.height_pair n.Λ fields fp =
      (Model.goldilocks (V := V)).height_pair n fields fp := rfl

/-- At the spec's model, the member `already_sent` is `Goldilocks.already_sent`, read on the node
state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_already_sent (n : NodeState V) (h : Height) (T : BlockId) (τ : Bool) :
    Goldilocks.already_sent n.Λ h T τ =
      (Model.goldilocks (V := V)).already_sent n h T τ := rfl

/-- At the spec's model, the member `votesHeldSet` is `Goldilocks.ACState.pool`, read on the node
state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_votesHeldSet (n : NodeState V) (s : Slot) :
    n.A.pool s =
      (Model.goldilocks (V := V)).votesHeldSet n s := rfl

/-- At the spec's model, the member `is_live` is `Goldilocks.is_live`, read on the node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_is_live (n : NodeState V) (t : Time) (e : LockEntry V) :
    Goldilocks.is_live (Goldilocks.fg_to_ac n.S) t e =
      (Model.goldilocks (V := V)).is_live n t e := rfl

/-- At the spec's model, the member `is_locked` is `Goldilocks.is_locked`, read on the node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_is_locked (n : NodeState V) (t : Time) (B' : Block V) :
    Goldilocks.is_locked n.A (Goldilocks.fg_to_ac n.S) t B' =
      (Model.goldilocks (V := V)).is_locked n t B' := rfl

/-- At the spec's model, the member `live_lock_vetoes` is `Goldilocks.live_lock_vetoes`, read on the
node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_live_lock_vetoes (n : NodeState V) (t : Time) (C : Block V) :
    Goldilocks.live_lock_vetoes n.A (Goldilocks.fg_to_ac n.S) t C =
      (Model.goldilocks (V := V)).live_lock_vetoes n t C := rfl

/-- At the spec's model, the member `live_entries` is `Goldilocks.live_entries`, read on the node
state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_live_entries (n : NodeState V) (t : Time) :
    Goldilocks.live_entries n.A (Goldilocks.fg_to_ac n.S) t =
      (Model.goldilocks (V := V)).live_entries n t := rfl

/-- At the spec's model, the member `saved_extends` is `Goldilocks.saved_extends`, read on the node
state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_saved_extends (n : NodeState V) (s'' : Slot) (B : Block V) :
    Goldilocks.saved_extends n.A (Goldilocks.fg_to_ac n.S) s'' B =
      (Model.goldilocks (V := V)).saved_extends n s'' B := rfl

/-- At the spec's model, the member `slow_test` is `Goldilocks.slow_test`, read on the node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_slow_test (C : Config) (n : NodeState V) (s' : Slot) (B : Block V) :
    Goldilocks.slow_test C n.A (Goldilocks.fg_to_ac n.S) s' B =
      (Model.goldilocks (V := V)).slow_test C n s' B := rfl

/-- At the spec's model, the member `ac_confirmed` is `Goldilocks.ac_confirmed`, read on the node
state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_ac_confirmed (n : NodeState V) :
    Goldilocks.ac_confirmed n.A (Goldilocks.fg_to_ac n.S) =
      (Model.goldilocks (V := V)).ac_confirmed n := rfl

/-- At the spec's model, the member `awake_since` is `Goldilocks.NodeState.awake_since`, read on the
node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_awake_since (n : NodeState V) (t₀ : Time) :
    n.awake_since t₀ =
      (Model.goldilocks (V := V)).awake_since n t₀ := rfl

/-- At the spec's model, the member `block_admissible` is `Goldilocks.block_admissible`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_block_admissible (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (B : Block V) :
    Goldilocks.block_admissible C P X n B =
      (Model.goldilocks (V := V)).block_admissible C P X n B := rfl

/-- At the spec's model, the member `attestations_on_chain` is `Goldilocks.attestations_on_chain`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_attestations_on_chain (B : Block V) :
    Goldilocks.attestations_on_chain B =
      (Model.goldilocks (V := V)).attestations_on_chain B := rfl

/-- At the spec's model, the member `on_chain` is `Goldilocks.on_chain`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_on_chain (a : Attestation V) (H : Block V) :
    Goldilocks.on_chain a H =
      (Model.goldilocks (V := V)).on_chain a H := rfl

/-- At the spec's model, the member `hp_height?` is `Goldilocks.HeightPair.height?`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_hp_height? (p : HeightPair) :
    Goldilocks.HeightPair.height? p =
      (Model.goldilocks (V := V)).hp_height? p := rfl

/-- At the spec's model, the member `hp_target?` is `Goldilocks.HeightPair.target?`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_hp_target? (p : HeightPair) :
    Goldilocks.HeightPair.target? p =
      (Model.goldilocks (V := V)).hp_target? p := rfl

/-- At the spec's model, the member `ac_valid_payload` is `Goldilocks.ac_valid_payload`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_ac_valid_payload (P : Provisional V) (B : Block V) :
    Goldilocks.ac_valid_payload P B =
      (Model.goldilocks (V := V)).ac_valid_payload P B := rfl

/-- At the spec's model, the member `included_votes` is `Goldilocks.included_votes`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_included_votes (Φ : Frame V) (s : Slot) :
    Goldilocks.included_votes Φ s =
      (Model.goldilocks (V := V)).included_votes Φ s := rfl

/-- At the spec's model, the member `included_support_votes` is `Goldilocks.included_support_votes`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_included_support_votes (Φ : Frame V) (s : Slot) :
    Goldilocks.included_support_votes Φ s =
      (Model.goldilocks (V := V)).included_support_votes Φ s := rfl

/-- At the spec's model, the member `votes_by` is `Goldilocks.votes_by`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_votes_by (votes : Finset (GoldfishVote V)) (v : V) :
    Goldilocks.votes_by votes v =
      (Model.goldilocks (V := V)).votes_by votes v := rfl

/-- At the spec's model, the member `equivocates` is `Goldilocks.equivocates`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_equivocates (votes : Finset (GoldfishVote V)) (v : V) :
    Goldilocks.equivocates votes v =
      (Model.goldilocks (V := V)).equivocates votes v := rfl

/-- At the spec's model, the member `participates` is `Goldilocks.participates`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_participates (votes : Finset (GoldfishVote V)) (v : V) :
    Goldilocks.participates votes v =
      (Model.goldilocks (V := V)).participates votes v := rfl

/-- At the spec's model, the member `no_second_vote_in` is `Goldilocks.no_second_vote_in`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_no_second_vote_in (late : Finset (GoldfishVote V)) (vote : GoldfishVote V) :
    Goldilocks.no_second_vote_in late vote =
      (Model.goldilocks (V := V)).no_second_vote_in late vote := rfl

/-- At the spec's model, the member `equivocators` is `Goldilocks.equivocators`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_equivocators (votes : Finset (GoldfishVote V)) :
    Goldilocks.equivocators votes =
      (Model.goldilocks (V := V)).equivocators votes := rfl

/-- At the spec's model, the member `participants` is `Goldilocks.participants`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_participants (votes : Finset (GoldfishVote V)) :
    Goldilocks.participants votes =
      (Model.goldilocks (V := V)).participants votes := rfl

/-- At the spec's model, the member `voters_count` is `Goldilocks.voters_count`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_voters_count (votes : Finset (GoldfishVote V)) :
    Goldilocks.voters_count votes =
      (Model.goldilocks (V := V)).voters_count votes := rfl

/-- At the spec's model, the member `viable_tree` is `Goldilocks.viable_tree`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_viable_tree (Φ : Frame V) (tree : Finset (Block V)) :
    Goldilocks.viable_tree Φ tree =
      (Model.goldilocks (V := V)).viable_tree Φ tree := rfl

/-- At the spec's model, the member `present` is `Goldilocks.present`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_present {α : Type} [DecidableEq α] (S : Finset (Option α)) :
    Goldilocks.present S =
      (Model.goldilocks (V := V)).present S := rfl

/-- At the spec's model, the member `advance` is `Goldilocks.advance`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_advance (Φ : Frame V) (old : Block V) (C? : Option (Block V)) :
    Goldilocks.advance Φ old C? =
      (Model.goldilocks (V := V)).advance Φ old C? := rfl

/-- At the spec's model, the member `slots_before` is `Goldilocks.slots_before`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_slots_before (s' : Slot) (k : ℕ) :
    Goldilocks.slots_before s' k =
      (Model.goldilocks (V := V)).slots_before s' k := rfl

/-- At the spec's model, the member `attestation_well_formed` is
`Goldilocks.attestation_well_formed`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_attestation_well_formed (a : Attestation V) :
    Goldilocks.attestation_well_formed a =
      (Model.goldilocks (V := V)).attestation_well_formed a := rfl

/-- At the spec's model, the member `block_well_formed` is `Goldilocks.block_well_formed`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_block_well_formed (P : Provisional V) (X : External V) (B : Block V) :
    Goldilocks.block_well_formed P X B =
      (Model.goldilocks (V := V)).block_well_formed P X B := rfl
-- END GENERATED equations

section RootOrderMembers

variable [RootOrder]

-- BEGIN GENERATED equations_ro
/-- At the spec's model, the member `tick` is `Goldilocks.tick`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_tick (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) :
    (Goldilocks.tick C P X n t).outcomes =
      (Model.goldilocks (V := V)).tick C P X n t := rfl

/-- At the spec's model, the member `receive` is `Goldilocks.Sts.receive`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_receive (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (o : NamedObject V) :
    Goldilocks.Sts.receive C P X n o =
      (Model.goldilocks (V := V)).receive C P X n o := rfl

/-- At the spec's model, the member `get_anchor` is `Goldilocks.get_anchor`, read on the node state.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_get_anchor (n : NodeState V) (t : Time) :
    Goldilocks.get_anchor n.A (Goldilocks.fg_to_ac n.S) t =
      (Model.goldilocks (V := V)).get_anchor n t := rfl

/-- At the spec's model, the member `tieBreak` is
`GoldilocksCorrectness.Proofs.Routines.goldilocksTieBreak`.

Read aloud: the spec's model has the spec's routine. -/
@[record_goldilocks]
theorem goldilocks_tieBreak :
    (GoldilocksCorrectness.Proofs.Routines.goldilocksTieBreak : TieBreak V) =
      (Model.goldilocks (V := V)).tieBreak := rfl
-- END GENERATED equations_ro

end RootOrderMembers

end GoldilocksCorrectness.Record
