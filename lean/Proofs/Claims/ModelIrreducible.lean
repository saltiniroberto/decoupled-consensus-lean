module

public import Proofs.Claims.ChainStateIrreducible
public meta import Lean.Meta.Eqns
public import Model.Vocabulary.Execution.Node
public import Model.Vocabulary.Execution.Objects
public import Model.Vocabulary.Execution.Run
public import Model.Vocabulary.Execution.Setup
public import Model.Vocabulary.Objects.Blocks
public import Model.Vocabulary.Objects.Identifiers
public import Model.Vocabulary.Objects.NamedBlocks
public import Model.Vocabulary.Objects.Parameters
public import Model.Vocabulary.Objects.Time
public import Model.Vocabulary.Objects.Weights
public import Model.Vocabulary.Protocol.Duties.Inputs
public import Model.Vocabulary.Protocol.Duties.Proposals
public import Model.Vocabulary.Protocol.Evidence
public import Model.Vocabulary.Protocol.ForkChoice.Goldfish
public import Model.Vocabulary.Protocol.ForkChoice.Head
public import Model.Vocabulary.Protocol.ForkChoice.Views
public import Model.Vocabulary.Protocol.Grades
public import Model.Vocabulary.Protocol.Handlers
public import Model.Vocabulary.Protocol.Schedule
public import Model.Vocabulary.Protocol.Store
public import Model.Vocabulary.Protocol.StoreBase
public import Model.Vocabulary.Protocol.Tick
public import Model.Vocabulary.Protocol.ValidatorClient

@[expose] public section

/-!
# The model definitions marked `irreducible`

Marks `irreducible` the model definitions outside the chain-state family, and imports the module
that marks the chain-state family, so that a proof reads them through facts stated about them, and
`rfl`, `change` and `show` no longer see through them. The kernel ignores the attribute, and
`allowUnsafeReducibility` adds no axiom.
-/

/-- The recursive definitions marked here, whose equation theorems are generated before the marking. -/
meta def markedDefs : List Lean.Name := [
  `DecoupledConsensusModel.Block.depth,
  `DecoupledConsensusModel.Block.preceq,
  `DecoupledConsensusModel.NamedBlock.erase,
  `DecoupledConsensusModel.NamedBlock.preceq,
  `DecoupledConsensusModel.Protocol.NamedProposalRows.chainRows,
  `DecoupledConsensusModel.Protocol.chain_up,
  `DecoupledConsensusModel.Protocol.clipGrade,
  `DecoupledConsensusModel.Protocol.ghost_walk,
  `DecoupledConsensusModel.chain_attestations]

run_meta do
  for n in markedDefs do
    discard <| Lean.Meta.getEqnsFor? n
    discard <| Lean.Meta.getUnfoldEqnFor? n (nonRec := true)

-- DecoupledConsensusModel.Objects.Blocks
set_option allowUnsafeReducibility true in
attribute [irreducible]
  DecoupledConsensusModel.Block.Compatible
  DecoupledConsensusModel.Block.Prec
  DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Block.attestations
  DecoupledConsensusModel.Block.compatible
  DecoupledConsensusModel.Block.deeper
  DecoupledConsensusModel.Block.deepest?
  DecoupledConsensusModel.Block.depth
  DecoupledConsensusModel.Block.find?
  DecoupledConsensusModel.Block.gf_support_votes
  DecoupledConsensusModel.Block.gf_votes
  DecoupledConsensusModel.Block.isDeepestIn
  DecoupledConsensusModel.Block.parent
  DecoupledConsensusModel.Block.parent?
  DecoupledConsensusModel.Block.prec
  DecoupledConsensusModel.Block.preceq
  DecoupledConsensusModel.Block.proposer?
  DecoupledConsensusModel.Block.root
  DecoupledConsensusModel.Block.slot
  DecoupledConsensusModel.pickUnique?

-- DecoupledConsensusModel.Objects.Weights
set_option allowUnsafeReducibility true in
attribute [irreducible]
  DecoupledConsensusModel.Electorate.finalityThreshold
  DecoupledConsensusModel.Electorate.quorumCheck
  DecoupledConsensusModel.Electorate.totalWeight
  DecoupledConsensusModel.Electorate.weightOf

-- DecoupledConsensusModel.Objects.Parameters
set_option allowUnsafeReducibility true in
attribute [irreducible]
  DecoupledConsensusModel.Env.W
  DecoupledConsensusModel.Env.committee
  DecoupledConsensusModel.Env.q
  DecoupledConsensusModel.Env.slotOf
  DecoupledConsensusModel.Env.t

-- DecoupledConsensusModel.Execution.Run
set_option allowUnsafeReducibility true in
attribute [irreducible]
  DecoupledConsensusModel.Execution.NamedActionReads.confirmationReadFrom
  DecoupledConsensusModel.Execution.NamedActionReads.preparedCache
  DecoupledConsensusModel.Execution.NamedReceiptCalls.postCore

-- DecoupledConsensusModel.Execution.Node
set_option allowUnsafeReducibility true in
attribute [irreducible]
  DecoupledConsensusModel.Execution.NamedNode.initial
  DecoupledConsensusModel.Execution.NamedNode.process
  DecoupledConsensusModel.Execution.NamedNode.tick
  DecoupledConsensusModel.Execution.NamedProfile.gradeContract
  DecoupledConsensusModel.Execution.NamedProfile.tick
  DecoupledConsensusModel.Execution.NamedReceipt.depsPresent
  DecoupledConsensusModel.Execution.NamedReceipt.excludes
  DecoupledConsensusModel.Execution.NamedReceipt.process
  DecoupledConsensusModel.Execution.NamedReceipt.processed
  DecoupledConsensusModel.Execution.NamedReceipt.wellFormed

-- DecoupledConsensusModel.Execution.Objects
set_option allowUnsafeReducibility true in
attribute [irreducible]
  DecoupledConsensusModel.Execution.NamedObject.author

-- DecoupledConsensusModel.Execution.Setup
set_option allowUnsafeReducibility true in
attribute [irreducible]
  DecoupledConsensusModel.Execution.RootInjectiveBelow
  DecoupledConsensusModel.Execution.RootInjectiveOnAncestors

-- DecoupledConsensusModel.Protocol.Evidence
set_option allowUnsafeReducibility true in
attribute [irreducible]
  DecoupledConsensusModel.HasIntersectionWeight
  DecoupledConsensusModel.HasSlashableWeightBetween
  DecoupledConsensusModel.SlashableBetween
  DecoupledConsensusModel.chain_attestations
  DecoupledConsensusModel.store_attestations

-- DecoupledConsensusModel.Objects.NamedBlocks
set_option allowUnsafeReducibility true in
attribute [irreducible]
  DecoupledConsensusModel.NamedAttestation.erase
  DecoupledConsensusModel.NamedBlock.Preceq
  DecoupledConsensusModel.NamedBlock.attestations
  DecoupledConsensusModel.NamedBlock.erase
  DecoupledConsensusModel.NamedBlock.gf_votes
  DecoupledConsensusModel.NamedBlock.parent
  DecoupledConsensusModel.NamedBlock.preceq
  DecoupledConsensusModel.NamedBlock.proposer?
  DecoupledConsensusModel.NamedBlock.root
  DecoupledConsensusModel.NamedBlock.slot
  DecoupledConsensusModel.NamedHeightPair.erase
  DecoupledConsensusModel.NamedHeightPair.matchesEntry

-- DecoupledConsensusModel.Protocol.Grades
set_option allowUnsafeReducibility true in
attribute [irreducible]
  DecoupledConsensusModel.Protocol.CleanFrom
  DecoupledConsensusModel.Protocol.HealConfig.a
  DecoupledConsensusModel.Protocol.HealConfig.opening_slot
  DecoupledConsensusModel.Protocol.HealConfig.round_of
  DecoupledConsensusModel.Protocol.HealingStore.gradeView
  DecoupledConsensusModel.Protocol.Opposes
  DecoupledConsensusModel.Protocol.Phase.domainOffset
  DecoupledConsensusModel.Protocol.Phase.earlyOffset
  DecoupledConsensusModel.Protocol.Phase.lateOffset
  DecoupledConsensusModel.Protocol.Supports
  DecoupledConsensusModel.Protocol.activePrefix
  DecoupledConsensusModel.Protocol.alignRound
  DecoupledConsensusModel.Protocol.allClosed
  DecoupledConsensusModel.Protocol.anchor
  DecoupledConsensusModel.Protocol.bodyReady
  DecoupledConsensusModel.Protocol.cacheAtRound
  DecoupledConsensusModel.Protocol.chain_of
  DecoupledConsensusModel.Protocol.chain_up
  DecoupledConsensusModel.Protocol.clear
  DecoupledConsensusModel.Protocol.clipCache
  DecoupledConsensusModel.Protocol.clipFrame
  DecoupledConsensusModel.Protocol.clipGrade
  DecoupledConsensusModel.Protocol.clipResult
  DecoupledConsensusModel.Protocol.completeFrame
  DecoupledConsensusModel.Protocol.completeOne
  DecoupledConsensusModel.Protocol.currentSGVote
  DecoupledConsensusModel.Protocol.deepest_clear
  DecoupledConsensusModel.Protocol.domain
  DecoupledConsensusModel.Protocol.early
  DecoupledConsensusModel.Protocol.emptyFrame
  DecoupledConsensusModel.Protocol.frameContract
  DecoupledConsensusModel.Protocol.frameGradeRead
  DecoupledConsensusModel.Protocol.frameSGCandidate
  DecoupledConsensusModel.Protocol.frameStableRoot
  DecoupledConsensusModel.Protocol.freezeRoot
  DecoupledConsensusModel.Protocol.grade2Block
  DecoupledConsensusModel.Protocol.gradeBool
  DecoupledConsensusModel.Protocol.head_covers
  DecoupledConsensusModel.Protocol.initialCache
  DecoupledConsensusModel.Protocol.interpretedInputs
  DecoupledConsensusModel.Protocol.late
  DecoupledConsensusModel.Protocol.localCovers
  DecoupledConsensusModel.Protocol.onPhaseTick
  DecoupledConsensusModel.Protocol.opening
  DecoupledConsensusModel.Protocol.opposing
  DecoupledConsensusModel.Protocol.pendingFrame
  DecoupledConsensusModel.Protocol.phaseResult
  DecoupledConsensusModel.Protocol.positive
  DecoupledConsensusModel.Protocol.putPhase
  DecoupledConsensusModel.Protocol.rawInputs
  DecoupledConsensusModel.Protocol.rawView
  DecoupledConsensusModel.Protocol.readFrame
  DecoupledConsensusModel.Protocol.readyView
  DecoupledConsensusModel.Protocol.token

-- DecoupledConsensusModel.Protocol.StoreBase
set_option allowUnsafeReducibility true in
attribute [irreducible]
  DecoupledConsensusModel.Protocol.GoldfishStore.pool
  DecoupledConsensusModel.Protocol.GoldfishStore.tau
  DecoupledConsensusModel.Protocol.resolution_time
  DecoupledConsensusModel.Protocol.resolved

-- DecoupledConsensusModel.Protocol.Duties.Proposals
set_option allowUnsafeReducibility true in
attribute [irreducible]
  DecoupledConsensusModel.Protocol.NamedActions.creatorInput
  DecoupledConsensusModel.Protocol.NamedActions.parentBody?
  DecoupledConsensusModel.Protocol.NamedActions.proposal_with
  DecoupledConsensusModel.Protocol.NamedActions.round_action_with
  DecoupledConsensusModel.Protocol.NamedDuties.attest_with
  DecoupledConsensusModel.Protocol.NamedDuties.goldfish_vote_with
  DecoupledConsensusModel.Protocol.NamedDuties.propose_block_with
  DecoupledConsensusModel.Protocol.NamedDuties.update_confirmation_with
  DecoupledConsensusModel.Protocol.NamedProposalRows.capPerSigner
  DecoupledConsensusModel.Protocol.NamedProposalRows.carriedRows
  DecoupledConsensusModel.Protocol.NamedProposalRows.chainRows
  DecoupledConsensusModel.Protocol.NamedProposalRows.eligibleBody
  DecoupledConsensusModel.Protocol.NamedProposalRows.excludeOnChain
  DecoupledConsensusModel.Protocol.NamedProposalRows.orderedBodies
  DecoupledConsensusModel.Protocol.NamedProposalRows.orderedRoots
  DecoupledConsensusModel.Protocol.NamedProposalRows.poolRows
  DecoupledConsensusModel.Protocol.NamedProposalRows.processedRows
  DecoupledConsensusModel.Protocol.NamedProposalRows.proposalRows
  DecoupledConsensusModel.Protocol.NamedProposalRows.select
  DecoupledConsensusModel.Protocol.ProposalRows.inWindow

-- DecoupledConsensusModel.Protocol.Handlers
set_option allowUnsafeReducibility true in
attribute [irreducible]
  DecoupledConsensusModel.Protocol.NamedAdmission.admit_carried
  DecoupledConsensusModel.Protocol.NamedAdmission.admit_row
  DecoupledConsensusModel.Protocol.NamedAdmission.admit_rows
  DecoupledConsensusModel.Protocol.NamedAdmission.on_block_with
  DecoupledConsensusModel.Protocol.NamedStore.commitBlock
  DecoupledConsensusModel.Protocol.NamedStore.initial
  DecoupledConsensusModel.Protocol.NamedStore.process_block_core
  DecoupledConsensusModel.Protocol.NamedStore.setClock
  DecoupledConsensusModel.Protocol.TickScheduler.runWith
  DecoupledConsensusModel.Protocol.advance_confirmed
  DecoupledConsensusModel.Protocol.carried_attestations_admissible
  DecoupledConsensusModel.Protocol.floor_on_stable
  DecoupledConsensusModel.Protocol.get_confirmed
  DecoupledConsensusModel.Protocol.get_head_in_tree_with
  DecoupledConsensusModel.Protocol.get_stable
  DecoupledConsensusModel.Protocol.goldfish_vote_with
  DecoupledConsensusModel.Protocol.on_block
  DecoupledConsensusModel.Protocol.on_block_checked
  DecoupledConsensusModel.Protocol.on_block_checked_using
  DecoupledConsensusModel.Protocol.on_block_using
  DecoupledConsensusModel.Protocol.on_goldfish_vote
  DecoupledConsensusModel.Protocol.on_goldfish_vote_checked
  DecoupledConsensusModel.Protocol.on_sg_vote
  DecoupledConsensusModel.Protocol.round_votes
  DecoupledConsensusModel.Protocol.state_transition
  DecoupledConsensusModel.Protocol.update_confirmation_with
  DecoupledConsensusModel.Protocol.update_finality
  DecoupledConsensusModel.Protocol.voter_filtered_block_tree

-- DecoupledConsensusModel.Protocol.ValidatorClient
set_option allowUnsafeReducibility true in
attribute [irreducible]
  DecoupledConsensusModel.Protocol.NamedRecord.create
  DecoupledConsensusModel.Protocol.NamedRecord.encodeHeight
  DecoupledConsensusModel.Protocol.NamedRecord.encodeRow
  DecoupledConsensusModel.Protocol.NamedRecord.initial
  DecoupledConsensusModel.Protocol.NamedRecord.legacyCreate
  DecoupledConsensusModel.Protocol.NamedRecord.rememberTimeout
  DecoupledConsensusModel.Protocol.Record.initial
  DecoupledConsensusModel.Protocol.Record.with_lock
  DecoupledConsensusModel.Protocol.Record.with_target
  DecoupledConsensusModel.Protocol.Record.with_timeout
  DecoupledConsensusModel.Protocol.create_attestation
  DecoupledConsensusModel.Protocol.finality_pair
  DecoupledConsensusModel.Protocol.height_pair
  DecoupledConsensusModel.Protocol.own_lock
  DecoupledConsensusModel.Protocol.record_attestation

-- DecoupledConsensusModel.Protocol.Tick
set_option allowUnsafeReducibility true in
attribute [irreducible]
  DecoupledConsensusModel.Protocol.NamedTick.namedOps
  DecoupledConsensusModel.Protocol.NamedTick.tick

-- DecoupledConsensusModel.Protocol.Store
set_option allowUnsafeReducibility true in
attribute [irreducible]
  DecoupledConsensusModel.Protocol.Store.init
  DecoupledConsensusModel.Protocol.Store.pool
  DecoupledConsensusModel.Protocol.Store.sg_pool
  DecoupledConsensusModel.Protocol.Store.tau
  DecoupledConsensusModel.Protocol.Store.toHealing
  DecoupledConsensusModel.Protocol.sgVote

-- DecoupledConsensusModel.Protocol.ForkChoice.Goldfish
set_option allowUnsafeReducibility true in
attribute [irreducible]
  DecoupledConsensusModel.Protocol.argmax?
  DecoupledConsensusModel.Protocol.finalized_descendants
  DecoupledConsensusModel.Protocol.get_fg_root
  DecoupledConsensusModel.Protocol.get_filtered_block_tree
  DecoupledConsensusModel.Protocol.get_filtered_block_tree_from
  DecoupledConsensusModel.Protocol.ghost
  DecoupledConsensusModel.Protocol.ghost_children
  DecoupledConsensusModel.Protocol.ghost_step
  DecoupledConsensusModel.Protocol.ghost_walk
  DecoupledConsensusModel.Protocol.goldfish_eligible
  DecoupledConsensusModel.Protocol.goldfish_fork_choice
  DecoupledConsensusModel.Protocol.goldfish_score
  DecoupledConsensusModel.Protocol.is_best_in
  DecoupledConsensusModel.Protocol.latest_window
  DecoupledConsensusModel.Protocol.no_second_vote_in
  DecoupledConsensusModel.Protocol.outranks
  DecoupledConsensusModel.Protocol.raw_equivocators
  DecoupledConsensusModel.Protocol.raw_goldfish_score
  DecoupledConsensusModel.Protocol.raw_participants
  DecoupledConsensusModel.Protocol.raw_supporters
  DecoupledConsensusModel.Protocol.raw_voters_count
  DecoupledConsensusModel.Protocol.targets_under
  DecoupledConsensusModel.Protocol.viable
  DecoupledConsensusModel.Protocol.viable_tree
  DecoupledConsensusModel.Protocol.voters_count

-- DecoupledConsensusModel.Protocol.Schedule
set_option allowUnsafeReducibility true in
attribute [irreducible]
  DecoupledConsensusModel.Protocol.carried_support_well_formed
  DecoupledConsensusModel.Protocol.carried_votes_well_formed
  DecoupledConsensusModel.Protocol.confirmation_time
  DecoupledConsensusModel.Protocol.equivocates
  DecoupledConsensusModel.Protocol.participates
  DecoupledConsensusModel.Protocol.proposal_time
  DecoupledConsensusModel.Protocol.support_cutoff
  DecoupledConsensusModel.Protocol.view_freeze
  DecoupledConsensusModel.Protocol.vote_time
  DecoupledConsensusModel.Protocol.vote_well_formed
  DecoupledConsensusModel.Protocol.votes_by

-- DecoupledConsensusModel.Protocol.Duties.Inputs
set_option allowUnsafeReducibility true in
attribute [irreducible]
  DecoupledConsensusModel.Protocol.fg_source_with
  DecoupledConsensusModel.Protocol.get_fg_vote_with
  DecoupledConsensusModel.Protocol.get_sg_vote_with
  DecoupledConsensusModel.Protocol.grade2_block_with
  DecoupledConsensusModel.Protocol.with_attestation_input
  DecoupledConsensusModel.Protocol.with_proposal_input

-- DecoupledConsensusModel.Protocol.ForkChoice.Head
set_option allowUnsafeReducibility true in
attribute [irreducible]
  DecoupledConsensusModel.Protocol.get_head_in_tree_with_layer
  DecoupledConsensusModel.Protocol.get_head_with
  DecoupledConsensusModel.Protocol.get_sg_root_with

-- DecoupledConsensusModel.Protocol.ForkChoice.Views
set_option allowUnsafeReducibility true in
attribute [irreducible]
  DecoupledConsensusModel.Protocol.proposer_support_view
  DecoupledConsensusModel.Protocol.proposer_view
  DecoupledConsensusModel.Protocol.voter_processed_block_tree
  DecoupledConsensusModel.Protocol.voter_support_view
  DecoupledConsensusModel.Protocol.voter_view

-- DecoupledConsensusModel.Objects.Time
set_option allowUnsafeReducibility true in
attribute [irreducible]
  DecoupledConsensusModel.beforeCutoff
  DecoupledConsensusModel.genesisStamp
  DecoupledConsensusModel.occurrenceBefore
  DecoupledConsensusModel.occurrenceMax
  DecoupledConsensusModel.slotOfTime
  DecoupledConsensusModel.slotStart
  DecoupledConsensusModel.stampedBefore

-- DecoupledConsensusModel.Objects.Identifiers
set_option allowUnsafeReducibility true in
attribute [irreducible]
  DecoupledConsensusModel.genesisRoot
