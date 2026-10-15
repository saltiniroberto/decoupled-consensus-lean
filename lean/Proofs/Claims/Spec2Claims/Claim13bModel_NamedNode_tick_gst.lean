module
public import Proofs.Claims.ModelIrreducible
public import Proofs.Claims.Spec2Claims.Claim13bModel_Env_committee_gst
public import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAdmission_on_block_with_gst

@[expose] public section

/-!
# `NamedNode.tick` does not read the GST

A node's tick and the routines it calls (`TickScheduler.runWith`, `NamedTick.namedOps`,
`onPhaseTick`, `NamedProfile.tick`) are each the same at a setup and at that setup with its GST
replaced (`setupWithGST`).
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

section RunWith

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.TickScheduler.runWith
  DecoupledConsensusModel.Protocol.HealConfig.round_of DecoupledConsensusModel.Protocol.HealConfig.a
  DecoupledConsensusModel.Protocol.HealConfig.opening_slot DecoupledConsensusModel.slotStart
  DecoupledConsensusModel.Protocol.support_cutoff DecoupledConsensusModel.Env.t
  DecoupledConsensusModel.Protocol.vote_time DecoupledConsensusModel.Protocol.proposal_time
  DecoupledConsensusModel.Env.slotOf DecoupledConsensusModel.slotOfTime

/-- `TickScheduler.runWith` with the same operations gives the same result at `S` and at `S` with
    its GST replaced. -/
theorem runWith_setupWithGST {State Record BlockOut VoteOut AttOut Out Result : Type}
    (S : Setup V) (g : Int) (hg : 0 ≤ g) (nd : Protocol.Node V)
    (ops : TickScheduler.TickOps State Record BlockOut VoteOut AttOut)
    (blockOut : BlockOut → Out) (voteOut : VoteOut → Out) (attOut : AttOut → Out)
    (finish : State → Record → List Out → Result) (st : State) (record : Record) (t : Int) :
    TickScheduler.runWith (setupWithGST S g hg).E S.hc nd ops blockOut voteOut attOut finish
        st record t =
      TickScheduler.runWith S.E S.hc nd ops blockOut voteOut attOut finish st record t := rfl

end RunWith

section NamedOps

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedTick.namedOps
  DecoupledConsensusModel.Protocol.NamedDuties.attest_with
  DecoupledConsensusModel.Protocol.NamedAdmission.admit_row
  DecoupledConsensusModel.Protocol.Store.sg_pool DecoupledConsensusModel.NamedAttestation.erase
  DecoupledConsensusModel.NamedHeightPair.erase DecoupledConsensusModel.Protocol.on_sg_vote
  DecoupledConsensusModel.Protocol.sgVote DecoupledConsensusModel.Protocol.round_votes
  DecoupledConsensusModel.Protocol.HealConfig.round_of
  DecoupledConsensusModel.Protocol.Store.toHealing
  DecoupledConsensusModel.Protocol.NamedActions.round_action_with
  DecoupledConsensusModel.Protocol.NamedActions.creatorInput
  DecoupledConsensusModel.Protocol.NamedRecord.create
  DecoupledConsensusModel.Protocol.NamedRecord.rememberTimeout
  DecoupledConsensusModel.Protocol.NamedRecord.encodeRow
  DecoupledConsensusModel.Protocol.NamedRecord.encodeHeight
  DecoupledConsensusModel.Protocol.NamedRecord.legacyCreate
  DecoupledConsensusModel.Protocol.create_attestation
  DecoupledConsensusModel.Protocol.record_attestation
  DecoupledConsensusModel.Protocol.Record.with_target
  DecoupledConsensusModel.Protocol.Record.with_timeout
  DecoupledConsensusModel.Protocol.Record.with_lock DecoupledConsensusModel.Protocol.height_pair
  DecoupledConsensusModel.Protocol.own_lock DecoupledConsensusModel.Protocol.finality_pair
  DecoupledConsensusModel.Protocol.with_attestation_input
  DecoupledConsensusModel.Protocol.get_sg_vote_with DecoupledConsensusModel.Block.root
  DecoupledConsensusModel.genesisRoot DecoupledConsensusModel.Protocol.get_fg_vote_with
  DecoupledConsensusModel.Protocol.fg_source_with DecoupledConsensusModel.Protocol.deepest_clear
  DecoupledConsensusModel.Protocol.chain_of DecoupledConsensusModel.Block.depth
  DecoupledConsensusModel.Protocol.chain_up DecoupledConsensusModel.Block.parent?
  DecoupledConsensusModel.Block.preceq DecoupledConsensusModel.Block.deepest?
  DecoupledConsensusModel.Block.isDeepestIn DecoupledConsensusModel.Block.deeper
  DecoupledConsensusModel.pickUnique? DecoupledConsensusModel.Protocol.get_head_with
  DecoupledConsensusModel.Protocol.get_filtered_block_tree
  DecoupledConsensusModel.Protocol.get_filtered_block_tree_from
  DecoupledConsensusModel.Protocol.viable_tree
  DecoupledConsensusModel.Protocol.finalized_descendants DecoupledConsensusModel.Protocol.viable
  DecoupledConsensusModel.Block.Preceq DecoupledConsensusModel.Protocol.get_fg_root
  DecoupledConsensusModel.Protocol.get_head_in_tree_with_layer
  DecoupledConsensusModel.Protocol.goldfish_fork_choice
  DecoupledConsensusModel.Protocol.goldfish_eligible DecoupledConsensusModel.Block.slot
  DecoupledConsensusModel.Protocol.goldfish_score
  DecoupledConsensusModel.Protocol.raw_goldfish_score
  DecoupledConsensusModel.Protocol.raw_supporters DecoupledConsensusModel.Protocol.targets_under
  DecoupledConsensusModel.Block.find? DecoupledConsensusModel.Protocol.votes_by
  DecoupledConsensusModel.Protocol.equivocates DecoupledConsensusModel.Protocol.raw_equivocators
  DecoupledConsensusModel.Protocol.voters_count DecoupledConsensusModel.Protocol.raw_voters_count
  DecoupledConsensusModel.Protocol.raw_participants DecoupledConsensusModel.Protocol.participates
  DecoupledConsensusModel.Block.parent DecoupledConsensusModel.Protocol.ghost
  DecoupledConsensusModel.Protocol.ghost_walk DecoupledConsensusModel.Protocol.ghost_step
  DecoupledConsensusModel.Protocol.ghost_children DecoupledConsensusModel.Protocol.argmax?
  DecoupledConsensusModel.Protocol.is_best_in DecoupledConsensusModel.Protocol.outranks
  DecoupledConsensusModel.Protocol.get_sg_root_with DecoupledConsensusModel.Protocol.resolved
  DecoupledConsensusModel.Protocol.GoldfishStore.pool
  DecoupledConsensusModel.Protocol.grade2_block_with
  DecoupledConsensusModel.Protocol.NamedDuties.update_confirmation_with
  DecoupledConsensusModel.Protocol.update_confirmation_with
  DecoupledConsensusModel.Protocol.advance_confirmed
  DecoupledConsensusModel.Protocol.floor_on_stable
  DecoupledConsensusModel.Protocol.no_second_vote_in
  DecoupledConsensusModel.Protocol.confirmation_time DecoupledConsensusModel.Env.t
  DecoupledConsensusModel.slotStart DecoupledConsensusModel.Protocol.Store.pool
  DecoupledConsensusModel.Protocol.support_cutoff DecoupledConsensusModel.Protocol.Store.tau
  DecoupledConsensusModel.Protocol.resolution_time DecoupledConsensusModel.occurrenceMax
  DecoupledConsensusModel.beforeCutoff DecoupledConsensusModel.stampedBefore
  DecoupledConsensusModel.Protocol.NamedDuties.goldfish_vote_with
  DecoupledConsensusModel.Protocol.goldfish_vote_with
  DecoupledConsensusModel.Protocol.on_goldfish_vote_checked
  DecoupledConsensusModel.Protocol.on_goldfish_vote DecoupledConsensusModel.Env.committee
  DecoupledConsensusModel.Protocol.get_head_in_tree_with
  DecoupledConsensusModel.Protocol.voter_filtered_block_tree
  DecoupledConsensusModel.Protocol.voter_processed_block_tree
  DecoupledConsensusModel.Protocol.view_freeze DecoupledConsensusModel.Protocol.voter_support_view
  DecoupledConsensusModel.Block.gf_support_votes DecoupledConsensusModel.Protocol.GoldfishStore.tau
  DecoupledConsensusModel.Protocol.voter_view DecoupledConsensusModel.Block.gf_votes
  DecoupledConsensusModel.Protocol.NamedDuties.propose_block_with
  DecoupledConsensusModel.Protocol.NamedStore.process_block_core
  DecoupledConsensusModel.Protocol.NamedStore.commitBlock DecoupledConsensusModel.NamedBlock.erase
  DecoupledConsensusModel.Protocol.on_block_using DecoupledConsensusModel.Protocol.update_finality
  DecoupledConsensusModel.Block.prec DecoupledConsensusModel.Block.proposer?
  DecoupledConsensusModel.Protocol.on_block_checked_using
  DecoupledConsensusModel.Protocol.carried_attestations_admissible
  DecoupledConsensusModel.Block.attestations DecoupledConsensusModel.NamedBlock.parent
  DecoupledConsensusModel.Protocol.NamedAdmission.admit_carried
  DecoupledConsensusModel.NamedBlock.attestations
  DecoupledConsensusModel.Protocol.NamedAdmission.admit_rows
  DecoupledConsensusModel.Protocol.NamedActions.proposal_with
  DecoupledConsensusModel.Protocol.NamedActions.parentBody?
  DecoupledConsensusModel.Protocol.NamedProposalRows.select
  DecoupledConsensusModel.Protocol.NamedProposalRows.carriedRows
  DecoupledConsensusModel.Protocol.NamedProposalRows.orderedBodies
  DecoupledConsensusModel.Protocol.NamedProposalRows.orderedRoots
  DecoupledConsensusModel.NamedBlock.root DecoupledConsensusModel.Protocol.ProposalRows.inWindow
  DecoupledConsensusModel.Protocol.NamedProposalRows.eligibleBody
  DecoupledConsensusModel.NamedBlock.slot
  DecoupledConsensusModel.Protocol.NamedProposalRows.poolRows
  DecoupledConsensusModel.Protocol.NamedProposalRows.processedRows
  DecoupledConsensusModel.Protocol.NamedProposalRows.proposalRows
  DecoupledConsensusModel.Protocol.NamedProposalRows.excludeOnChain
  DecoupledConsensusModel.Protocol.NamedProposalRows.chainRows
  DecoupledConsensusModel.Protocol.NamedProposalRows.capPerSigner
  DecoupledConsensusModel.Protocol.with_proposal_input
  DecoupledConsensusModel.Protocol.proposer_support_view
  DecoupledConsensusModel.Protocol.proposer_view DecoupledConsensusModel.Protocol.frameContract
  DecoupledConsensusModel.Protocol.frameStableRoot DecoupledConsensusModel.Protocol.activePrefix
  DecoupledConsensusModel.Protocol.readFrame DecoupledConsensusModel.Protocol.cacheAtRound
  DecoupledConsensusModel.Protocol.pendingFrame DecoupledConsensusModel.Protocol.clipFrame
  DecoupledConsensusModel.Protocol.clipResult DecoupledConsensusModel.Protocol.clipGrade
  DecoupledConsensusModel.Block.compatible DecoupledConsensusModel.Protocol.frameSGCandidate
  DecoupledConsensusModel.Protocol.currentSGVote DecoupledConsensusModel.Protocol.frameGradeRead
  DecoupledConsensusModel.Protocol.clear DecoupledConsensusModel.Protocol.grade2Block
  DecoupledConsensusModel.Protocol.allClosed DecoupledConsensusModel.Protocol.anchor

/-- The operation record `NamedTick.namedOps` is the same at `S` and at `setupWithGST S g hg`. -/
theorem namedOps_setupWithGST (S : Setup V) (g : Int) (hg : 0 ≤ g) (c : Cache V)
    (nd : Protocol.Node V) :
    NamedTick.namedOps (frameContract c) (setupWithGST S g hg).E S.hc S.cfg nd =
      NamedTick.namedOps (frameContract c) S.E S.hc S.cfg nd := by
  unfold NamedTick.namedOps NamedDuties.propose_block_with
  rw [onBlockWith_setupWithGST]
  rfl

end NamedOps

section OnPhaseTick

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.onPhaseTick
  DecoupledConsensusModel.Protocol.completeFrame DecoupledConsensusModel.Protocol.completeOne
  DecoupledConsensusModel.Protocol.late DecoupledConsensusModel.Protocol.Phase.lateOffset
  DecoupledConsensusModel.Protocol.opening DecoupledConsensusModel.Protocol.HealConfig.opening_slot
  DecoupledConsensusModel.Protocol.proposal_time DecoupledConsensusModel.Env.t
  DecoupledConsensusModel.slotStart DecoupledConsensusModel.Protocol.early
  DecoupledConsensusModel.Protocol.Phase.earlyOffset
  DecoupledConsensusModel.Protocol.HealingStore.gradeView
  DecoupledConsensusModel.Protocol.get_filtered_block_tree
  DecoupledConsensusModel.Protocol.get_filtered_block_tree_from
  DecoupledConsensusModel.Protocol.viable_tree
  DecoupledConsensusModel.Protocol.finalized_descendants DecoupledConsensusModel.Block.preceq
  DecoupledConsensusModel.Protocol.viable DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Protocol.get_fg_root DecoupledConsensusModel.Protocol.freezeRoot
  DecoupledConsensusModel.Protocol.gradeBool DecoupledConsensusModel.Protocol.positive
  DecoupledConsensusModel.Protocol.CleanFrom DecoupledConsensusModel.Protocol.Supports
  DecoupledConsensusModel.Protocol.rawView DecoupledConsensusModel.Protocol.rawInputs
  DecoupledConsensusModel.Protocol.latest_window DecoupledConsensusModel.occurrenceBefore
  DecoupledConsensusModel.Protocol.token DecoupledConsensusModel.Protocol.readyView
  DecoupledConsensusModel.Protocol.interpretedInputs DecoupledConsensusModel.Protocol.bodyReady
  DecoupledConsensusModel.Block.compatible DecoupledConsensusModel.stampedBefore
  DecoupledConsensusModel.Block.find? DecoupledConsensusModel.Block.root
  DecoupledConsensusModel.genesisRoot DecoupledConsensusModel.pickUnique?
  DecoupledConsensusModel.Protocol.localCovers DecoupledConsensusModel.Protocol.head_covers
  DecoupledConsensusModel.Protocol.opposing DecoupledConsensusModel.Protocol.Opposes
  DecoupledConsensusModel.Electorate.weightOf DecoupledConsensusModel.Block.deepest?
  DecoupledConsensusModel.Block.isDeepestIn DecoupledConsensusModel.Block.deeper
  DecoupledConsensusModel.Block.depth DecoupledConsensusModel.Protocol.putPhase
  DecoupledConsensusModel.Protocol.domain DecoupledConsensusModel.Protocol.Phase.domainOffset
  DecoupledConsensusModel.Protocol.phaseResult DecoupledConsensusModel.Protocol.clipCache
  DecoupledConsensusModel.Protocol.clipFrame DecoupledConsensusModel.Protocol.clipResult
  DecoupledConsensusModel.Protocol.clipGrade DecoupledConsensusModel.Env.slotOf
  DecoupledConsensusModel.slotOfTime DecoupledConsensusModel.Protocol.HealConfig.round_of
  DecoupledConsensusModel.Protocol.alignRound DecoupledConsensusModel.Protocol.pendingFrame

/-- `onPhaseTick` computes the same cache at `S` and at `setupWithGST S g hg`. -/
theorem onPhaseTick_setupWithGST (S : Setup V) (g : Int) (hg : 0 ≤ g)
    (st : Protocol.HealingStore V) (t : Int) (c : Cache V) :
    onPhaseTick (setupWithGST S g hg).E (setupWithGST S g hg).hc st t c =
      onPhaseTick S.E S.hc st t c := rfl

end OnPhaseTick

section ProfileTick

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Execution.NamedProfile.tick
  DecoupledConsensusModel.Execution.NamedProfile.gradeContract
  DecoupledConsensusModel.Protocol.NamedTick.tick

/-- A validator's tick with a given cache is the same at `S` and at `setupWithGST S g hg`. -/
theorem namedProfileTick_setupWithGST (S : Setup V) (g : Int) (hg : 0 ≤ g) (c : Cache V)
    (v : V) (st : NamedStore V) (record : Protocol.NamedRecord) (t : Int) :
    NamedProfile.tick (setupWithGST S g hg) c v st record t = NamedProfile.tick S c v st record t := by
  show TickScheduler.runWith (setupWithGST S g hg).E S.hc (S.node v)
      (NamedTick.namedOps (frameContract c) (setupWithGST S g hg).E S.hc S.cfg (S.node v))
      NamedObject.block NamedObject.gfVote NamedObject.attest
      (fun st record emitted => (st, record, emitted)) st record t =
    TickScheduler.runWith S.E S.hc (S.node v)
      (NamedTick.namedOps (frameContract c) S.E S.hc S.cfg (S.node v))
      NamedObject.block NamedObject.gfVote NamedObject.attest
      (fun st record emitted => (st, record, emitted)) st record t
  rw [namedOps_setupWithGST]
  exact runWith_setupWithGST S g hg _ _ _ _ _ _ st record t

end ProfileTick

section NodeTick

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Execution.NamedNode.tick

/-- A node's tick, cache computation included, is the same at `S` and at `setupWithGST S g hg`. -/
theorem namedNodeTick_setupWithGST (S : Setup V) (g : Int) (hg : 0 ≤ g) (v : V)
    (n : NamedNodeState V) (t : Int) :
    NamedNode.tick (setupWithGST S g hg) v n t = NamedNode.tick S v n t := by
  simp only [NamedNode.tick]
  rw [namedProfileTick_setupWithGST, onPhaseTick_setupWithGST]

end NodeTick

end DecoupledConsensusModel.Sts
