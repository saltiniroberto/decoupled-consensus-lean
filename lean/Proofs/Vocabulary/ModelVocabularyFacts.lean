import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Facts
import Proofs.Vocabulary.ChainStateVocabulary
import Proofs.Claims.Spec2Claims.Claim13beRoute3_85
import Proofs.Claims.Spec2Claims.Claim13beRoute3_85d
import Proofs.Claims.Spec2Claims.Claim13bK_FinalityStepWindow
import Proofs.Claims.Spec2Claims.Claim13bK_HjMono
import Proofs.Claims.Spec2Claims.Claim13bModel_derive_named
import Proofs.Claims.Spec2Claims.Claim13bStepFin
import Proofs.Claims.Spec2Claims.Claim13bModel_Slashable
import Proofs.Claims.Spec2Claims.Claim13bModel_e1Fields
import Proofs.Claims.Spec2Claims.Claim13bModel_ChainState_initial
import Proofs.Claims.Spec2Claims.ClaimAsyncK_SecondHealing

import Proofs.Vocabulary.Execution.W4FKChainAdvanceFold
import Proofs.Vocabulary.ModelProperties.NamedAdmission_admit_carried
import Proofs.Vocabulary.ModelProperties.NamedAdmission_on_block_with
import Proofs.Vocabulary.ModelProperties.NamedStore_commitBlock
import Proofs.Vocabulary.ModelProperties.NamedStore_initial
import Proofs.Vocabulary.ModelProperties.NamedStore_process_block_core
import Proofs.Vocabulary.ModelProperties.NamedStore_setClock
import Proofs.Vocabulary.ModelProperties.carried_attestations_admissible
import Proofs.Vocabulary.ModelProperties.on_block_checked_using
import Proofs.Vocabulary.ModelProperties.on_block_using
import Proofs.Vocabulary.ModelProperties.on_goldfish_vote_checked
import Proofs.Vocabulary.ModelProperties.voter_filtered_block_tree
import Proofs.Vocabulary.Protocol.Handlers.Admission
import Proofs.Vocabulary.Protocol.Handlers.BlockProcessingDefaults
import Proofs.Vocabulary.Protocol.Handlers.Blocks
import Proofs.Vocabulary.Protocol.Handlers.Execution
import Proofs.Vocabulary.Protocol.Handlers.FinalityMonotone
import Proofs.Vocabulary.Protocol.Handlers.FinalityMonotoneCore
import Proofs.Vocabulary.Protocol.Handlers.HMaxCore
import Proofs.Vocabulary.Protocol.Handlers.HMaxMonotone
import Proofs.Vocabulary.Protocol.Handlers.Invariants
import Proofs.Vocabulary.Protocol.Handlers.Invariants2
import Proofs.Vocabulary.Protocol.Handlers.JustificationBound
import Proofs.Vocabulary.Protocol.Handlers.NamedStore
import Proofs.Vocabulary.Protocol.Handlers.NestedOutputs
import Proofs.Vocabulary.Protocol.Handlers.Pool
import Proofs.Vocabulary.Protocol.Handlers.TickBridges
import Proofs.Vocabulary.Protocol.Schedule.Alignment
import Proofs.Vocabulary.Protocol.Schedule.ReceiptCallsF1
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedAgree
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedSettle
import Proofs.Claims.Spec2Claims.Claim13bK_StableRecord
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAdmission_on_block_with
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedStore_commitBlock
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedStore_initial
import Proofs.Claims.Spec2Claims.Claim13bModel_advance_confirmed
import Proofs.Claims.Spec2Claims.Claim13bModel_advance_confirmed_incl
import Proofs.Claims.Spec2Claims.Claim13bModel_advance_confirmed_phase
import Proofs.Claims.Spec2Claims.Claim13bModel_floor_on_stable
import Proofs.Claims.Spec2Claims.Claim13bModel_floor_on_stable_incl
import Proofs.Claims.Spec2Claims.Claim13bModel_floor_on_stable_phase
import Proofs.Claims.Spec2Claims.Claim13bModel_get_confirmed
import Proofs.Claims.Spec2Claims.Claim13bModel_get_head_in_tree_with
import Proofs.Claims.Spec2Claims.Claim13bModel_get_stable
import Proofs.Claims.Spec2Claims.Claim13bModel_on_sg_vote
import Proofs.Claims.Spec2Claims.Claim13bModel_round_votes
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_incl
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG1
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG2
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG2b
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG5
import Proofs.Claims.Spec2Claims.Claim13bModel_update_confirmation_with_phase
import Proofs.Claims.Spec2Claims.Claim13bModel_voter_filtered_block_tree
import Proofs.Claims.Spec2Claims.Claim13beRoute3_24
import Proofs.Claims.Spec2Claims.Claim13beRoute3_5
import Proofs.Claims.Spec2Claims.ClaimAsyncK_StableRecord
import Proofs.Vocabulary.ModelProperties.NamedNode_initial
import Proofs.Vocabulary.ModelProperties.NamedNode_process
import Proofs.Vocabulary.ModelProperties.NamedNode_tick
import Proofs.Vocabulary.ModelProperties.NamedProfile_gradeContract
import Proofs.Vocabulary.ModelProperties.NamedReceiptCalls_postCore
import Proofs.Vocabulary.ModelProperties.NamedReceipt_excludes
import Proofs.Vocabulary.ModelProperties.NamedReceipt_process
import Proofs.Vocabulary.ModelProperties.NamedReceipt_processed
import Proofs.Vocabulary.ModelProperties.confirmationReadFrom
import Proofs.Vocabulary.Protocol.Grades.NamedNode
import Proofs.Vocabulary.Protocol.Handlers.FrozenRootOrder
import Proofs.Vocabulary.Protocol.Handlers.Receipt
import Proofs.Vocabulary.Protocol.Handlers.RetentionNamed
import Proofs.Vocabulary.Protocol.ValidatorClient.Bridge
import Proofs.Claims.ProcessedFlip
import Proofs.Claims.Spec2Claims.Claim13bK_CrossTransport
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedNode_tick
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedReceiptCalls_postCore
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedStore_initial_stamp
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmationReadFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_grade2Block
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeContract
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeContract_inclG1
import Proofs.Claims.Spec2Claims.Claim13bModel_initial
import Proofs.Claims.Spec2Claims.Claim13bModel_initial_inclG2
import Proofs.Claims.Spec2Claims.Claim13bModel_onPhaseTick
import Proofs.Claims.Spec2Claims.Claim13bModel_postCore
import Proofs.Claims.Spec2Claims.ClaimAsyncK_GstShift
import Proofs.Vocabulary.Execution.HealthyLocalFacts
import Proofs.Vocabulary.Generic.EvaluationStore
import Proofs.Vocabulary.ModelVocabulary.Goldfish.Objects
import Proofs.Vocabulary.Objects.ActionRound
import Proofs.Vocabulary.Objects.Final
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Confirmation
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ProposalSnapshotBridge
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ProposalVoteDuty
import Proofs.Vocabulary.Protocol.Grades.GSTZeroSelectionSafety
import Proofs.Vocabulary.Protocol.Schedule.AdoptionTransport
import Proofs.Vocabulary.Protocol.Schedule.CrossView
import Proofs.Vocabulary.Protocol.Schedule.GSTZeroReorgResilience
import Proofs.Vocabulary.Protocol.Schedule.ProposalCanonicality
import Proofs.Vocabulary.Protocol.Schedule.ProposalTransportCore
import Proofs.Vocabulary.Protocol.Schedule.SlotInduction
import Proofs.Claims.Spec2Claims.Claim13bAnchor
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedSettleEarlier
import Proofs.Claims.Spec2Claims.Claim13bK_HeadsNewAnchor
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmation_time
import Proofs.Claims.Spec2Claims.Claim13bModel_equivocates
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time_inclG1
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time_inclX
import Proofs.Claims.Spec2Claims.Claim13bModel_support_cutoff
import Proofs.Claims.Spec2Claims.Claim13bModel_view_freeze
import Proofs.Claims.Spec2Claims.Claim13bModel_vote_time
import Proofs.Claims.Spec2Claims.Claim13bModel_votes_by
import Proofs.Claims.Spec2Claims.Claim13bSGCompatible
import Proofs.Claims.Spec2Claims.Claim13bStepCone
import Proofs.Claims.Spec2Claims.Claim13beRoute3_26
import Proofs.Claims.Spec2Claims.Claim13beRoute3_47
import Proofs.Claims.Spec2Claims.Claim13beRoute3_55
import Proofs.Claims.Spec2Claims.Claim13beRoute3_78
import Proofs.Claims.Spec2Claims.Claim13beRoute3_86d
import Proofs.Claims.TransferH
import Proofs.Vocabulary.Protocol.Schedule.ConfirmationHistoryProducer
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.RecoveryProposalCapInputs
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25
import Proofs.Vocabulary.ModelProperties.NamedDuties_goldfish_vote_with
import Proofs.Vocabulary.ModelProperties.get_fg_root
import Proofs.Vocabulary.ModelProperties.get_filtered_block_tree
import Proofs.Vocabulary.ModelProperties.get_head_in_tree_with_layer
import Proofs.Vocabulary.ModelProperties.get_head_with
import Proofs.Vocabulary.ModelProperties.get_sg_root_with
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Agreement
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Records
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Walk
import Proofs.Vocabulary.Protocol.Grades.Inclusions
import Proofs.Vocabulary.Protocol.Grades.Q10Frame
import Proofs.Claims.Spec2Claims.Claim13bK_ConeAnchor
import Proofs.Claims.Spec2Claims.Claim13bK_ProposalVotesWalk
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedDuties_goldfish_vote_with
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedDuties_goldfish_vote_with_some
import Proofs.Claims.Spec2Claims.Claim13bModel_get_fg_root
import Proofs.Claims.Spec2Claims.Claim13bModel_get_filtered_block_tree
import Proofs.Claims.Spec2Claims.Claim13bModel_get_filtered_block_tree_inclG5
import Proofs.Claims.Spec2Claims.Claim13bModel_get_head_in_tree_with_layer
import Proofs.Claims.Spec2Claims.Claim13bModel_get_head_with
import Proofs.Claims.Spec2Claims.Claim13bModel_goldfish_fork_choice
import Proofs.Claims.Spec2Claims.Claim13bModel_goldfish_score
import Proofs.Claims.Spec2Claims.Claim13bModel_proposer_view
import Proofs.Claims.Spec2Claims.Claim13bModel_targets_under
import Proofs.Claims.Spec2Claims.Claim13bModel_voter_processed_block_tree
import Proofs.Claims.Spec2Claims.Claim13bModel_voter_view
import Proofs.Claims.Spec2Claims.Claim13bModel_voters_count
import Proofs.Claims.Spec2Claims.Claim13bStepKitStore
import Proofs.Claims.Spec2Claims.Claim13bStepSG
import Proofs.Claims.Spec2Claims.Claim13bStepSGMove
import Proofs.Vocabulary.ModelProperties.HealingStore_gradeView
import Proofs.Vocabulary.ModelProperties.anchor
import Proofs.Vocabulary.ModelProperties.currentSGVote
import Proofs.Vocabulary.ModelProperties.deepest_clear
import Proofs.Vocabulary.ModelProperties.grade2Block
import Proofs.Vocabulary.ModelProperties.gradeBool
import Proofs.Vocabulary.ModelProperties.phaseResult
import Proofs.Vocabulary.ModelProperties.readFrame
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.RecoveryProposalWindow
import Proofs.Vocabulary.Protocol.Grades.GradeCutoffMono
import Proofs.Vocabulary.Protocol.Grades.GradeFormsBridge
import Proofs.Vocabulary.Protocol.Grades.Grades
import Proofs.Vocabulary.Protocol.Grades.GuardedGradeHelpers
import Proofs.Vocabulary.Protocol.Grades.Interpolation
import Proofs.Vocabulary.Protocol.Grades.LifecycleActionSource
import Proofs.Vocabulary.Protocol.Grades.ProposalParent
import Proofs.Vocabulary.Protocol.Grades.RecoveryCapturedSlotInterval
import Proofs.Vocabulary.Protocol.Handlers.ConfirmationMembership
import Proofs.Vocabulary.Protocol.Store.BoundaryRows
import Proofs.Vocabulary.Protocol.ValidatorClient.Engine
import Proofs.Claims.Spec2Claims.Claim13bK_GradeDescendant
import Proofs.Claims.Spec2Claims.Claim13bK_GradeOldHeads
import Proofs.Claims.Spec2Claims.Claim13bK_HeadsPersist
import Proofs.Claims.Spec2Claims.Claim13bK_LiveConfirmedSlots
import Proofs.Claims.Spec2Claims.Claim13bK_LiveConfirmedSlotsUpTo
import Proofs.Claims.Spec2Claims.Claim13bModel_a
import Proofs.Claims.Spec2Claims.Claim13bModel_activePrefix
import Proofs.Claims.Spec2Claims.Claim13bModel_anchor
import Proofs.Claims.Spec2Claims.Claim13bModel_clipGrade
import Proofs.Claims.Spec2Claims.Claim13bModel_clipResult
import Proofs.Claims.Spec2Claims.Claim13bModel_currentSGVote
import Proofs.Claims.Spec2Claims.Claim13bModel_currentSGVote_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_deepest_clear
import Proofs.Claims.Spec2Claims.Claim13bModel_domain_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_early
import Proofs.Claims.Spec2Claims.Claim13bModel_frameSGCandidate
import Proofs.Claims.Spec2Claims.Claim13bModel_frameStableRoot
import Proofs.Claims.Spec2Claims.Claim13bModel_frameStableRoot_cs
import Proofs.Claims.Spec2Claims.Claim13bModel_freezeRoot
import Proofs.Claims.Spec2Claims.Claim13bModel_grade2Block_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeBool
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeBool_against
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeBool_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeBool_cs
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeView
import Proofs.Claims.Spec2Claims.Claim13bModel_head_covers
import Proofs.Claims.Spec2Claims.Claim13bModel_late
import Proofs.Claims.Spec2Claims.Claim13bModel_localCovers
import Proofs.Claims.Spec2Claims.Claim13bModel_onPhaseTick_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_opening
import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot
import Proofs.Claims.Spec2Claims.Claim13bModel_rawInputs
import Proofs.Claims.Spec2Claims.Claim13bModel_rawView
import Proofs.Claims.Spec2Claims.Claim13bModel_readFrame
import Proofs.Claims.Spec2Claims.Claim13bModel_readFrame_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_readFrame_cs
import Proofs.Claims.Spec2Claims.Claim13bModel_readFrame_incl
import Proofs.Claims.Spec2Claims.Claim13bModel_readyView
import Proofs.Claims.Spec2Claims.Claim13bModel_readyView_find
import Proofs.Claims.Spec2Claims.Claim13bModel_round_of
import Proofs.Claims.Spec2Claims.Claim13bModel_token
import Proofs.Claims.Spec2Claims.Claim13bStepAnchor
import Proofs.Claims.Spec2Claims.Claim13bStepConeIter
import Proofs.Claims.Spec2Claims.Claim13bStepKitDelivery
import Proofs.Claims.Spec2Claims.Claim13bStepKitRelay
import Proofs.Claims.Spec2Claims.Claim13beRoute3_29
import Proofs.Claims.Spec2Claims.Claim13beRoute3_34
import Proofs.Claims.Spec2Claims.Claim13beRoute3_48b
import Proofs.Claims.Spec2Claims.Claim13beRoute3_53
import Proofs.Claims.Spec2Claims.Claim13beRoute3_53b
import Proofs.Claims.Spec2Claims.Claim13beRoute3_58
import Proofs.Claims.Spec2Claims.Claim13beRoute3_67b
import Proofs.Claims.Spec2Claims.Claim13beRoute3_86e
import Proofs.Claims.Spec2Claims.Claim13beRoute3_86f
import Proofs.Claims.Spec2Claims.Claim13beRoute3_88
import Proofs.Vocabulary.ModelProperties.Store_pool
import Proofs.Vocabulary.ModelProperties.Store_sg_pool
import Proofs.Vocabulary.ModelProperties.Store_toHealing
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.RetainedRows
import Proofs.Claims.Spec2Claims.Claim13bModel_GoldfishStore_pool
import Proofs.Claims.Spec2Claims.Claim13bModel_GoldfishStore_tau
import Proofs.Claims.Spec2Claims.Claim13bModel_Store_pool
import Proofs.Claims.Spec2Claims.Claim13bModel_Store_sg_pool
import Proofs.Claims.Spec2Claims.Claim13bModel_Store_tau
import Proofs.Claims.Spec2Claims.Claim13bModel_resolved
import Proofs.Claims.Spec2Claims.Claim13bModel_sgVote
import Proofs.Claims.Spec2Claims.Claim13bModel_toHealing
import Proofs.Vocabulary.ModelProperties.NamedActions_proposal_with_slot
import Proofs.Vocabulary.ModelProperties.NamedDuties_attest_with
import Proofs.Vocabulary.ModelProperties.NamedDuties_update_confirmation_with
import Proofs.Vocabulary.ModelProperties.ProposalRows_inWindow
import Proofs.Vocabulary.ModelProperties.fg_source_with
import Proofs.Vocabulary.ModelProperties.get_sg_vote_with
import Proofs.Vocabulary.ModelProperties.grade2_block_with
import Proofs.Vocabulary.ModelProperties.propose_block_with
import Proofs.Vocabulary.ModelProperties.round_action_with
import Proofs.Vocabulary.ModelProperties.update_confirmation_with
import Proofs.Vocabulary.Protocol.Duties.Proposals.Actions
import Proofs.Vocabulary.Protocol.Grades.NamedDuties
import Proofs.Vocabulary.Protocol.ValidatorClient.BlockEmission
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedDuties_attest_with
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedDuties_update_confirmation_with
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedTick_tick
import Proofs.Claims.Spec2Claims.Claim13bModel_fg_source_with
import Proofs.Claims.Spec2Claims.Claim13bModel_inWindow
import Proofs.Claims.Spec2Claims.Claim13bModel_processedRows
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_with
import Proofs.Claims.Spec2Claims.Claim13bModel_propose_block_with_inclG2
import Proofs.Claims.Spec2Claims.Claim13bModel_propose_block_with_snd
import Proofs.Claims.Spec2Claims.Claim13bModel_round_action_with
import Proofs.Claims.Spec2Claims.Claim13bModel_select
import Proofs.Claims.Spec2Claims.Claim13bModel_update_confirmation_with
import Proofs.Claims.Spec2Claims.Claim13bModel_update_confirmation_with_incl
import Proofs.Claims.Spec2Claims.Claim13bStepKitConfirm
import Proofs.Claims.Spec2Claims.Claim13beRoute3_7
import Proofs.Vocabulary.ModelProperties.store_attestations
import Proofs.Vocabulary.Protocol.ChainState.Chain
import Proofs.Vocabulary.Protocol.ChainState.Main
import Proofs.Vocabulary.Protocol.Evidence.ProvenanceBridge
import Proofs.Claims.Spec2Claims.Claim13beRoute3_21
import Proofs.Vocabulary.ModelProperties.create_attestation
import Proofs.Vocabulary.ModelProperties.own_lock
import Proofs.Vocabulary.Protocol.ValidatorClient.Divergence
import Proofs.Vocabulary.Protocol.ValidatorClient.FinalityPairCore
import Proofs.Vocabulary.Protocol.ValidatorClient.HeightPairCases
import Proofs.Vocabulary.Protocol.ValidatorClient.RecordClean
import Proofs.Claims.Spec2Claims.Claim13bModel_encodeHeight
import Proofs.Claims.Spec2Claims.Claim13bModel_own_lock
import Proofs.Claims.Spec2Claims.Claim13beRoute3_85c
import Proofs.Vocabulary.Protocol.Grades.VoteBelowSource
import Proofs.Vocabulary.ModelProperties.onPhaseTick
import Proofs.Claims.Spec2Claims.Claim13bModel_anchor_mk
import Proofs.Claims.Spec2Claims.Claim13bModel_bodyReady
import Proofs.Claims.Spec2Claims.Claim13bModel_bodyReady_mk
import Proofs.Claims.Spec2Claims.Claim13bModel_CleanFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_clear
import Proofs.Claims.Spec2Claims.Claim13bModel_currentSGVote_mk
import Proofs.Claims.Spec2Claims.Claim13bModel_rawView_mk
import Proofs.Claims.Spec2Claims.Claim13bModel_frameGradeRead_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_interpretedInputs
import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot_mk
import Proofs.Claims.Spec2Claims.Claim13bModel_Opposes
import Proofs.Claims.Spec2Claims.Claim13bModel_opposing
import Proofs.Claims.Spec2Claims.Claim13bModel_Supports
import Proofs.Claims.Spec2Claims.Claim13bModel_positive
import Proofs.Vocabulary.ModelProperties.update_finality
import Proofs.Claims.Spec2Claims.Claim13bModel_on_block_checked_using_s2
import Proofs.Vocabulary.ModelProperties.viable_tree
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ProposalWalkTransportCore
import Proofs.Claims.Spec2Claims.Claim13bModel_get_filtered_block_tree_from
import Proofs.Claims.Spec2Claims.Claim13bModel_voter_view_mk
import Proofs.Claims.Spec2Claims.Claim13bModel_no_second_vote_in
import Proofs.Claims.Spec2Claims.Claim13bModel_no_second_vote_in_mk
import Proofs.Vocabulary.ModelProperties.HasSlashableWeightBetween
import Proofs.Vocabulary.ModelProperties.NamedActionReads_preparedCache
import Proofs.Vocabulary.ModelProperties.NamedActions_proposal_with
import Proofs.Vocabulary.ModelProperties.SlashableBetween
import Proofs.Vocabulary.ModelProperties.with_attestation_input
import Proofs.Vocabulary.ModelProperties.with_proposal_input
import Proofs.Vocabulary.Protocol.ChainState.AlignedRoundLemmas
import Proofs.Vocabulary.Protocol.ChainState.Evidence
import Proofs.Vocabulary.Protocol.Duties.Proposals.ProposalRows
import Proofs.Claims.Spec2Claims.Claim13bModel_HasIntersectionWeight
import Proofs.Claims.Spec2Claims.Claim13bModel_HasSlashableWeightBetween
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedDuties_goldfish_vote_with_mk
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedNode_process
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedNode_process_gst
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedNode_tick_gst
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedReceipt_process
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedReceipt_processed
import Proofs.Claims.Spec2Claims.Claim13bModel_poolRows
import Proofs.Claims.Spec2Claims.Claim13bModel_propose_block_with_mk
import Proofs.Claims.Spec2Claims.Claim13bModel_SlashableBetween
import Proofs.Vocabulary.ModelVocabulary.Healing.Schedule
import Proofs.Vocabulary.Protocol.ValidatorClient.Schedule
import Proofs.Vocabulary.Protocol.Grades.Main
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ReaderLocalCone
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Adoption
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
import Proofs.Vocabulary.Protocol.Handlers.CarriedAdmissionChecks
import Proofs.Claims.Spec2Claims.Claim13bModel_on_goldfish_vote_checked
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedStore_process_block_core
import Proofs.Vocabulary.Protocol.Handlers.ReceiptCallsGF
import Proofs.Vocabulary.Protocol.Handlers.StableOutputSeed
import Proofs.Vocabulary.Protocol.ChainState.JustificationCertificates
import Proofs.Vocabulary.Protocol.ChainState.FinalityCertificates
import Proofs.Vocabulary.Protocol.Handlers.CommitteePools
import Proofs.Vocabulary.Protocol.ChainState.CheckpointAlgebra
import Proofs.Vocabulary.Protocol.ValidatorClient.RecoveryTimeout
import Model.Record.Model
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Proofs.Claims.Spec2Claims.Claim13bModel_domain
import Proofs.Vocabulary.Protocol.Handlers.FinalizationBridge
import Proofs.Vocabulary.Protocol.Duties.Inputs.ActionSources
import Proofs.Vocabulary.Execution.BodyRetention
import Proofs.Vocabulary.Protocol.Store.RawSource
import Proofs.Vocabulary.Protocol.Handlers.NumericStore
import Proofs.Vocabulary.Protocol.Handlers.JustificationCarrier
import Proofs.Vocabulary.Protocol.Handlers.Proposer
import Proofs.Claims.Spec2Claims.Claim13bK_GradeOld
import Proofs.Vocabulary.Protocol.ChainState.FinalityComparison
import Proofs.Vocabulary.Protocol.Handlers.BlockAdmission
import Proofs.Vocabulary.Protocol.Handlers.AdoptionConstructor
import Proofs.Vocabulary.Execution.ReceiptCalls
import Proofs.Vocabulary.Protocol.Handlers.BlockStamp
import Proofs.Vocabulary.Protocol.Handlers.HandlerAdmissionGuards
import Proofs.Vocabulary.Protocol.Schedule.HeldSkipProducers
import Proofs.Vocabulary.Execution.OutageActionInputs
import Proofs.Vocabulary.Protocol.ValidatorClient.RecordFresh
import Proofs.Vocabulary.Protocol.ValidatorClient.RecordTargetHistory
import Proofs.Claims.Spec2Claims.Claim13bModel_early_mk
import Proofs.Vocabulary.Protocol.Grades.CacheProvenance
import Proofs.Vocabulary.Protocol.Handlers.SGArrival
import Proofs.Vocabulary.Protocol.Grades.JointHistoryProducers
import Proofs.Vocabulary.Protocol.Handlers.RawRelay
import Proofs.Vocabulary.Protocol.ChainState.DerivationGeometry
import Proofs.Vocabulary.Protocol.ValidatorClient.SlashableBound
import Proofs.Vocabulary.Protocol.Handlers.StoreBridge
import Proofs.Claims.Spec2Claims.Claim13bModel_domain_mk_s4
import Proofs.Vocabulary.Protocol.ChainState.ProposalBridge
import Proofs.Vocabulary.Protocol.Handlers.GoldfishVotePool
import Proofs.Vocabulary.Protocol.ChainState.W4FKChainFinalityWrite
import Proofs.Vocabulary.Protocol.ChainState.W4FKChainJustification
import Proofs.Vocabulary.Protocol.ValidatorClient.W4FKChainFinalityRows
import Proofs.Vocabulary.Execution.FinalizedViable
import Proofs.Claims.Spec2Claims.Claim13beRoute3_23
import Proofs.Vocabulary.Protocol.Handlers.AcceptanceTiming
import Proofs.Claims.Spec2Claims.Claim13beRoute3_4
import Proofs.Vocabulary.Protocol.Handlers.SGArrivalStampCarrier
import Proofs.Claims.Spec2Claims.Claim13bModel_Store_tau_mk
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.HeightProgressClosurescoreEq
import Proofs.Vocabulary.Protocol.Store.PublicCutSG
import Proofs.Vocabulary.Protocol.Grades.FrameCompleted
import Proofs.Vocabulary.Protocol.ChainState.RawHeightCoverage
/-!
# Facts of the instance `Model.vocabulary`

The erasure of a record run's wake events, the worlds the wiring reaches at the instance
`Model.vocabulary`, and the proofs that `Model.vocabulary` satisfies the level-1 facts of every family.
-/

set_option autoImplicit false

section
open DecoupledConsensusModel DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Execution DecoupledConsensusModel.Protocol
open scoped DecoupledConsensusModel.Sts.Record

namespace DecoupledConsensusModel
namespace Proofs
namespace Optimistic
open Internal
open Execution
open Protocol

/-- At the instance `Model.vocabulary`, for every outcome `out` of `v`'s tick at slot `s`'s vote time
    from the node state `n`, with `s > 0`: if `out` sends the slot-`s` vote `u`, the pool of `n`'s
    core store is well stamped, `n`'s clock is at most the vote time, and `u`'s sender does not
    equivocate in `n`'s slot-`s` pool, then `u` is in the slot-`s` list of `out.1`'s core store with
    a stamp at most the vote time. -/
theorem record_vocabulary_tick_vote_pooled {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (S : Setup V) (v : V) (n : (Sts.Record.Model.vocabulary (V := V)).N) (s : Slot) (u : GoldfishVote V)
      (out : (Sts.Record.Model.vocabulary (V := V)).N × List (NamedObject V)),
      (Sts.Record.Model.vocabulary (V := V)).tick S v n ((Sts.Record.Model.vocabulary (V := V)).vote_time S.E s) ⇢ out →
      0 < s → NamedObject.gfVote u ∈ out.2 → u.slot = s →
      (∀ (k : Slot) (x : GoldfishVote V), x ∈ n.st.core.gf_votes k → x.slot = k) →
      (∀ (k : Slot) (x : GoldfishVote V), x ∈ n.st.core.gf_votes k →
        (n.st.core.timestamp_vote x).isSome = true) →
      (∀ x : GoldfishVote V, (n.st.core.timestamp_vote x).isSome = true → x ∈ n.st.core.gf_votes x.slot) →
      (∀ (x : GoldfishVote V) (c : Stamp), n.st.core.timestamp_vote x = some c → c ≤ (n.st.core.t : Stamp)) →
      n.st.core.t ≤ (Sts.Record.Model.vocabulary (V := V)).vote_time S.E s →
      (Sts.Record.Model.vocabulary (V := V)).equivocates
          ((Sts.Record.Model.vocabulary (V := V)).store_pool n.st.core s) u.val_index = false →
      u ∈ out.1.st.core.gf_votes s ∧
        ∃ c : Stamp, out.1.st.core.timestamp_vote u = some c ∧
          c ≤ ((Sts.Record.Model.vocabulary (V := V)).vote_time S.E s : Stamp) := by
  intro S w n s u out hout hs ho hus hslotP hstampedP hpooledP hboundedP hclockle hequivN
  simp only [Sts.Record.Model.vocabulary, Sts.Record.returns_pure] at hout
  subst hout
  set t := Protocol.vote_time S.E s with htdef
  obtain ⟨-, -, hduty, -, -⟩ := Proofs.Optimistic.gfVote_emitted_shape S w n t ho
  set gc := NamedProfile.gradeContract
      (NamedActionReads.confirmationReadFrom S n t).cache with hgcdef
  have hreadSteq : (NamedActionReads.confirmationReadFrom S n t).st =
      Protocol.NamedStore.setClock S.E n.st t := Sts.confirmationReadFrom_st S n t
  set st0 := Protocol.NamedStore.setClock S.E n.st t with hst0def
  have hduty' : (Protocol.goldfish_vote_with gc S.E S.hc (S.node w) st0.core).2 = some u := by
    rw [← hreadSteq, ← Sts.namedDuties_goldfish_vote_with_snd]
    exact hduty
  have hfst := (priv% Proofs.Vocabulary.Protocol.Handlers.GoldfishVotePool
    DecoupledConsensusModel.Proofs.Optimistic.goldfish_vote_with_fst_of_snd)
    gc S.E S.hc (S.node w) st0.core hduty'
  have hslot0 : st0.core.s = s := by
    rw [hst0def, Sts.setClock_core_s, htdef]; exact slotOf_vote_time S.E s
  have hclock0 : st0.core.t = t := by rw [hst0def, Sts.setClock_core_t]
  have hpoolEq : st0.core.pool s = n.st.core.pool s := by
    rw [hst0def]
    exact Sts.setClock_core_pool _ _ _ _
  have hstamps0 : Protocol.PoolStamps st0.core := by
    exact Sts.poolStamps_setClock S.E n.st t hclockle
      ⟨hslotP, hstampedP, hpooledP, hboundedP⟩
  have hfresh : ¬ u.slot < st0.core.s - 1 := by
    rw [hslot0, hus]; exact Nat.not_lt.mpr (Nat.sub_le s 1)
  have hfuture : ¬ st0.core.s < u.slot := by
    rw [hslot0, hus]; exact lt_irrefl s
  have hequiv : Protocol.equivocates (st0.core.pool u.slot) u.val_index = false := by
    rw [hus, hpoolEq]
    exact hequivN
  obtain ⟨hmem, c, hc, hle⟩ :=
    Protocol.mem_and_stamp_of_process st0.core u hstamps0 hfresh hfuture hequiv
  rw [hus] at hmem
  set s' := S.E.slotOf t with hs'def
  set proposed := Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg (S.node w) st0
    with hproposeddef
  set proposalDue := 0 < s' ∧ t = Protocol.proposal_time S.E s' ∧
    S.E.proposer s' = (S.node w).val_index with hproposalDuedef
  set st1 := if proposalDue then proposed.1 else st0 with hst1def
  set voted := Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc (S.node w) st1
    with hvoteddef
  set voteDue := 0 < s' ∧ t = Protocol.vote_time S.E s' with hvoteDuedef
  set st2 := if voteDue then voted.1 else st1 with hst2def
  set st3 := if 0 < s' ∧ t = Protocol.support_cutoff S.E s' then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s' - 1) else st2
    with hst3def
  have hs'eq : s' = s := by rw [hs'def, htdef]; exact slotOf_vote_time S.E s
  have hpne : ¬ proposalDue := by
    rw [hproposalDuedef]
    rintro ⟨-, hteq, -⟩
    exact Proofs.Optimistic.vote_time_ne_proposal_time S.E s' (by rw [← hteq, htdef, hs'eq])
  have hst1eq : st1 = st0 := by rw [hst1def, if_neg hpne]
  have hvd : voteDue := by rw [hvoteDuedef, hs'eq]; exact ⟨hs, htdef⟩
  have hst2eq : st2.core = Protocol.on_goldfish_vote st0.core u := by
    rw [hst2def, if_pos hvd, hvoteddef, hst1eq, Sts.namedDuties_goldfish_vote_with_fst_core]
    exact hfst
  have hst3fields : st3.core.gf_votes = st2.core.gf_votes ∧
      st3.core.timestamp_vote = st2.core.timestamp_vote := by
    rw [hst3def]
    split_ifs
    · rw [Proofs.ModelProperties.named_update_confirmation_with_core]
      exact ⟨Sts.update_confirmation_with_gf_votes _ _ _ _ _,
        Sts.update_confirmation_with_timestamp_vote _ _ _ _ _⟩
    · exact ⟨rfl, rfl⟩
  have htick1eq : (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node w) n.st n.record t).1 =
      if t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧
          (S.node w).awake (S.hc.round_of st3.core.s) = true then
        (Protocol.NamedDuties.attest_with gc S.E S.hc (S.node w) st3 n.record).1
      else st3 := by
    rw [Proofs.NamedTick.tick_computed_duties]
    dsimp only [st3, st2, voted, voteDue, st1, proposed, proposalDue, s']
    split_ifs <;> rfl
  have hfinalfields :
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node w) n.st n.record t).1.core.gf_votes =
        st3.core.gf_votes ∧
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node w) n.st n.record t).1.core.timestamp_vote =
        st3.core.timestamp_vote := by
    rw [htick1eq]
    split_ifs
    · rw [Sts.namedDuties_attest_with_fst]
      obtain ⟨-, -, -, -, hgfv, htsv⟩ := NamedAdmission.admit_row_fixed_fields S.hc st3
        (Protocol.NamedDuties.attest_with gc S.E S.hc (S.node w) st3 n.record).2.2
      exact ⟨hgfv, htsv⟩
    · exact ⟨rfl, rfl⟩
  have hgcstep : (NamedNode.tick S w n t).1.st =
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node w) n.st n.record t).1 := by
    rw [Sts.namedNode_tick_st, hgcdef, Sts.confirmationReadFrom_cache]
    exact rfl
  refine ⟨?_, c, ?_, ?_⟩
  · show u ∈ (NamedNode.tick S w n t).1.st.core.gf_votes s
    rw [hgcstep, hfinalfields.1, hst3fields.1, hst2eq]
    exact hmem
  · show (NamedNode.tick S w n t).1.st.core.timestamp_vote u = _
    rw [hgcstep, hfinalfields.2, hst3fields.2, hst2eq]
    exact hc
  · rw [hclock0] at hle
    exact hle


end Optimistic
end Proofs
end DecoupledConsensusModel
end


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- For a coherent store `before` that does not hold `B`: if `postCore` adds `B`, `B`'s derived
    finalized block is a descendant of `before`'s finalized block, and the justification and
    maximum-height conditions hold, then `B`'s derived finalized block is an ancestor of the
    finalized block of the store `postCore` leaves. -/
theorem postCore_absorbs_finality_r58a (S : Setup V) (before : Protocol.NamedStore V)
    (B : NamedBlock V)
    (hco : Proofs.NamedStore.Coherent S.E S.cfg before)
    (hnew : B.erase ∉ before.core.T)
    (hpost : B.erase ∈ (Execution.NamedReceiptCalls.postCore S before B).core.T)
    (hfloorBefore : Block.Preceq before.core.F (Protocol.derive_named S.E S.cfg B).F)
    (hupg : ∀ A ∈ before.bodies,
      (Protocol.derive_named S.E S.cfg A).J = (Protocol.derive_named S.E S.cfg B).F →
      (Protocol.derive_named S.E S.cfg A).h_j = (Protocol.derive_named S.E S.cfg B).h_F →
      Block.Preceq (Protocol.derive_named S.E S.cfg B).F before.core.J)
    (hmax : ∃ D ∈ before.bodies, (Protocol.derive_named S.E S.cfg D).h = before.core.h_max)
    (hbelow : ∀ D ∈ before.bodies,
      (Protocol.derive_named S.E S.cfg B).h_F < (Protocol.derive_named S.E S.cfg D).h →
      Block.Preceq (Protocol.derive_named S.E S.cfg B).F D.erase) :
    Block.Preceq (Protocol.derive_named S.E S.cfg B).F
      (Execution.NamedReceiptCalls.postCore S before B).core.F := by
  open Execution.NamedReceiptCalls in
  let sigma := Protocol.derive_named S.E S.cfg B
  rcases (rcr% finalized_justification_ancestor) S.E S.cfg B with
    ⟨A, hAB, hAcase, hAJ, hAh⟩
  rcases hAcase with hgen | hAparent
  · subst B
    rw [derive_named_genesis_F]
    exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _)
  · have hparent : B.parent ∈ before.bodies := by
      by_contra hn
      have hsame :
          (Execution.NamedReceiptCalls.postCore S before B).core =
            before.core := by
        rw [Sts.postCore_of_parent_not_mem S hn]
      exact hnew (hsame ▸ hpost)
    have hAheld : A ∈ before.bodies :=
      NamedOutageHistory.ViabilityHistoryTime.ancestor_body_mem
        hco.2.2.1 hparent hAparent
    let stored : Protocol.Store V := { before.core with
      σ := fun X => if X = B.erase then
        Protocol.named_transition S.E S.cfg
          (before.core.σ B.erase.parent) B
        else before.core.σ X
      T := insert B.erase before.core.T
      timestamp_block := fun X => if X = B.erase then
        some (before.core.t : Stamp) else before.core.timestamp_block X }
    let U := B.gf_votes.foldl
      (Protocol.on_goldfish_vote_checked S.E) stored
    let afterMax : Protocol.Store V :=
      { U with h_max := max U.h_max sigma.h }
    let afterJ : Protocol.Store V :=
      if Block.preceq afterMax.F sigma.J &&
          decide (Protocol.HeightId.mk afterMax.h_j afterMax.J.root <
            Protocol.HeightId.mk sigma.h_j sigma.J.root) then
        { afterMax with J := sigma.J, h_j := sigma.h_j }
      else afterMax
    have hderived :=
      NamedOutageHistory.GuardProofsTime.fresh_receipt_derived_and_admitted
        S before B hco hnew hpost
    change U.σ B.erase = sigma ∧ Block.Preceq U.F B.erase at hderived
    have hfields := (rcr% gf_fold_fields) S.E stored B.gf_votes
    have hUT : U.T = insert B.erase before.core.T := hfields.1
    have hUsigma : U.σ = stored.σ := hfields.2.1
    have hUF : U.F = before.core.F := hfields.2.2.1
    have hUJ : U.J = before.core.J := hfields.2.2.2.1
    have hUhj : U.h_j = before.core.h_j := hfields.2.2.2.2.1
    have hUmax : U.h_max = before.core.h_max := hfields.2.2.2.2.2
    have hpostEq :
        (Execution.NamedReceiptCalls.postCore S before B).core =
          Protocol.update_finality U (U.σ B.erase) :=
      NamedReceiptCallsGF.post_core_stored S before B hnew hpost
    have htreeA : A.erase ∈ before.core.T := by
      rw [hco.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hAheld
    have hFmemBefore : sigma.F ∈ before.core.T := by
      rw [← hAJ]
      exact NamedDerivationGeometry.core_ancestor_mem S.E S.cfg before hco
        htreeA
        (NamedDerivationGeometry.derive_named_anchors_preceq
          S.E S.cfg A).2
    have hFmemU : sigma.F ∈ U.T := by
      rw [hUT]
      exact Finset.mem_insert_of_mem hFmemBefore
    have hfloorU : Block.Preceq U.F sigma.F := by
      rw [hUF]
      exact hfloorBefore
    have hupgrade : Block.Preceq sigma.F before.core.J :=
      hupg A hAheld hAJ hAh
    have hafterJ : Block.Preceq sigma.F afterJ.J := by
      by_cases hg :
          (Block.preceq afterMax.F sigma.J &&
            decide (Protocol.HeightId.mk afterMax.h_j afterMax.J.root <
              Protocol.HeightId.mk sigma.h_j sigma.J.root)) = true
      · have horder :=
          NamedDerivationGeometry.chainOrder_derive_named S.E S.cfg B
        have hFJ := horder.finalized_preceq_justified
        have e : afterJ.J = sigma.J := by simp only [afterJ, hg, if_true]
        rw [e]
        exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp hFJ
      · have hgFalse :
            (Block.preceq afterMax.F sigma.J &&
              decide (Protocol.HeightId.mk afterMax.h_j afterMax.J.root <
                Protocol.HeightId.mk sigma.h_j sigma.J.root)) = false :=
          Bool.eq_false_of_not_eq_true hg
        have hafter : afterJ.J = afterMax.J := by
          simp only [afterJ, hgFalse, Bool.false_eq_true, if_false]
        rw [hafter]
        change Block.Preceq sigma.F U.J
        rw [hUJ]
        exact hupgrade
    have hviable : sigma.F ∈ Protocol.viable_tree U.σ U.F
        (max U.h_max sigma.h) U.T := by
      rw [Proofs.ModelProperties.mem_viable_tree_iff]
      refine ⟨⟨hFmemU, hfloorU⟩, ?_⟩
      by_cases hlow : max U.h_max sigma.h - 1 ≤ sigma.h
      · refine ⟨B.erase, ?_, ?_, ?_⟩
        · rw [hUT]
          exact Finset.mem_insert_self _ _
        · exact
            (NamedDerivationGeometry.derive_named_anchors_preceq
              S.E S.cfg B).1
        · rw [hderived.1]
          exact hlow
      · obtain ⟨M, hMheld, hMheight⟩ := hmax
        have hMraw : M.erase ∈ before.core.T := by
          rw [hco.1]
          exact Finset.mem_image_of_mem NamedBlock.erase hMheld
        have hMne : M.erase ≠ B.erase := by
          intro heq
          exact hnew (heq ▸ hMraw)
        have hmaxEq : max U.h_max sigma.h = U.h_max := by
          by_cases hle : sigma.h ≤ U.h_max
          · exact Nat.max_eq_left hle
          · exfalso
            apply hlow
            rw [Nat.max_eq_right (Nat.le_of_not_ge hle)]
            exact Nat.sub_le _ _
        have hheight : sigma.h_F <
            (Protocol.derive_named S.E S.cfg M).h := by
          have hchain :=
            NamedDerivationGeometry.chainOrder_derive_named S.E S.cfg B
          have horder := hchain.finalized_below_height
          change sigma.h_F < sigma.h at horder
          have hs : sigma.h < max U.h_max sigma.h - 1 :=
            Nat.lt_of_not_ge hlow
          have hout : sigma.h_F < U.h_max := by
            rw [hmaxEq] at hs
            exact lt_of_lt_of_le (lt_trans horder hs) (Nat.sub_le _ _)
          rw [hMheight, ← hUmax]
          exact hout
        have hFM : Block.Preceq sigma.F M.erase :=
          hbelow M hMheld hheight
        refine ⟨M.erase, ?_, hFM, ?_⟩
        · rw [hUT]
          exact Finset.mem_insert_of_mem hMraw
        · rw [hUsigma]
          change max U.h_max sigma.h - 1 ≤
            (if M.erase = B.erase then
              Protocol.named_transition S.E S.cfg
                (before.core.σ B.erase.parent) B
            else before.core.σ M.erase).h
          rw [if_neg hMne, hco.2.2.2.2 M hMheld, hMheight, ← hUmax,
            hmaxEq]
          exact Nat.sub_le _ _
    have hviableAfter : sigma.F ∈
        Protocol.viable_tree afterJ.σ afterJ.F
          afterJ.h_max afterJ.T := by
      dsimp only [afterJ, afterMax]
      split_ifs <;> exact hviable
    rw [hpostEq, hderived.1]
    change Block.Preceq sigma.F (Protocol.update_finality U sigma).F
    by_cases halready : Block.Preceq sigma.F U.F
    · exact Proofs.ModelProperties.Preceq_trans halready
        (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp (update_finality_F U sigma))
    · have hprec : Block.prec U.F sigma.F = true :=
        Proofs.ModelProperties.prec_eq_true_of_ne_of_Preceq
          (fun h => halready (by rw [h]; exact Proofs.ModelProperties.Preceq_self _)) hfloorU
      have hJ' : Block.preceq sigma.F
          (if Block.preceq U.F sigma.J && decide (Protocol.HeightId.mk U.h_j U.J.root <
              Protocol.HeightId.mk sigma.h_j sigma.J.root) then sigma.J else U.J) = true := by
        have e : afterJ.J =
            (if Block.preceq U.F sigma.J && decide (Protocol.HeightId.mk U.h_j U.J.root <
              Protocol.HeightId.mk sigma.h_j sigma.J.root) then sigma.J else U.J) := by
          dsimp only [afterJ, afterMax]
          split_ifs <;> rfl
        rw [← e]
        exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hafterJ
      rw [Proofs.ModelProperties.update_finality_F_of_conditions U sigma hprec hJ' hviable]
      exact Proofs.ModelProperties.Preceq_self _

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts.Record

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open scoped DC

/-! ## The erasure of a record run's wake events -/

section Erase

variable {V : Type}

/-- The `NamedEvent` a record event stands for: none for a wake, the same tick or delivery
    otherwise. -/
def Event.toVocabulary? : Record.Event V → Option (NamedEvent V)
  | .wake _ _ => none
  | .tick v t => some (Generic.Event.tick v t)
  | .deliver v o t => some (Generic.Event.deliver v o t)

/-- A record run with its wake events erased: the same honest set and horizon, and its ticks and
    deliveries in order. -/
def Run.toVocabulary (rho : Record.Run V) : NamedRun V :=
  { honest := rho.honest, horizon := rho.horizon,
    events := rho.events.filterMap Record.Event.toVocabulary? }

/-- Erasing an embedded event gives the event back. -/
theorem Event.toVocabulary?_ofVocabulary (e : NamedEvent V) :
    (Record.Event.ofVocabulary e).toVocabulary? = some e := by
  cases e <;> rfl

/-- A record event erases to `e'` exactly when it is the embedding of `e'`. -/
theorem Event.toVocabulary?_eq_some_iff (e : Record.Event V) (e' : NamedEvent V) :
    e.toVocabulary? = some e' ↔ e = Record.Event.ofVocabulary e' := by
  cases e <;> cases e' <;> simp [Record.Event.toVocabulary?, Record.Event.ofVocabulary]

/-- A record event is a wake or the embedding of a `NamedEvent`. -/
theorem Event.eq_wake_or_ofVocabulary (e : Record.Event V) :
    (∃ (v : V) (t : DecoupledConsensusModel.Time), e = Record.Event.wake v t) ∨
      ∃ e' : NamedEvent V, e = Record.Event.ofVocabulary e' := by
  cases e with
  | wake v t => exact Or.inl ⟨v, t, rfl⟩
  | tick v t => exact Or.inr ⟨Generic.Event.tick v t, rfl⟩
  | deliver v o t => exact Or.inr ⟨Generic.Event.deliver v o t, rfl⟩

/-- An event and its erasure have the same time. -/
theorem Event.time_of_toVocabulary? {e : Record.Event V} {e' : NamedEvent V}
    (h : e.toVocabulary? = some e') : NamedEvent.time e' = e.time := by
  rw [Event.toVocabulary?_eq_some_iff] at h
  subst h
  cases e' <;> rfl

/-- Erasing an embedded list of events gives the list back. -/
theorem Event.filterMap_toVocabulary?_map_ofVocabulary (l : List (NamedEvent V)) :
    (l.map Record.Event.ofVocabulary).filterMap Record.Event.toVocabulary? = l := by
  rw [List.filterMap_map]
  have : (Record.Event.toVocabulary? ∘ Record.Event.ofVocabulary : NamedEvent V → _) = some := by
    funext e; exact Event.toVocabulary?_ofVocabulary e
  rw [this, List.filterMap_some]

/-- Erasing an embedded run gives the run back. -/
theorem Run.toVocabulary_ofVocabulary (rho : NamedRun V) : (Run.ofVocabulary rho).toVocabulary = rho := by
  simp only [Run.toVocabulary, Run.ofVocabulary, Event.filterMap_toVocabulary?_map_ofVocabulary]

/-- Keeping the events before time `t` and erasing the wakes, in either order, gives the same list. -/
theorem Event.filterMap_filter_time_lt (l : List (Record.Event V))
    (t : DecoupledConsensusModel.Time) :
    (l.filter (fun e => decide (e.time < t))).filterMap Record.Event.toVocabulary? =
      (l.filterMap Record.Event.toVocabulary?).filter (fun e => decide (NamedEvent.time e < t)) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
      cases hx : e.toVocabulary? with
      | none =>
          by_cases h : e.time < t
          · simp only [List.filter_cons, List.filterMap_cons, hx, h, decide_true, ↓reduceIte, ih]
          · simp only [List.filter_cons, List.filterMap_cons, hx, h, decide_false, ↓reduceIte,
              Bool.false_eq_true, ih]
      | some e' =>
          have ht := Event.time_of_toVocabulary? hx
          by_cases h : e.time < t
          · simp only [List.filter_cons, List.filterMap_cons, hx, ht, h, decide_true, ↓reduceIte,
              ih]
          · simp only [List.filter_cons, List.filterMap_cons, hx, ht, h, decide_false, ↓reduceIte,
              Bool.false_eq_true, ih]

end Erase

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The worlds reached at the instance `Model.vocabulary` -/

/-- At the instance `Model.vocabulary`, the embedded event `e` leads from `w` to exactly one world,
    `NamedWorld.step S w e`. -/
theorem worldStepOf_vocabulary (S : Setup V) (w : V → (Model.vocabulary (V := V)).N)
    (e : NamedEvent V) :
    worldStepOf (Model.vocabulary (V := V)) S w (Record.Event.ofVocabulary e) =
      {NamedWorld.step S w e} := by
  cases e with
  | tick v t =>
      ext w'
      simp only [Record.Event.ofVocabulary, worldStepOf, NamedWorld.step, Set.mem_setOf_eq]
      have hr : ∀ out, Model.vocabulary.tick S v (w v) t ⇢ out ↔
          out = NamedNode.tick S v (w v) t := fun out => returns_pure _ out
      constructor
      · rintro (⟨out, hout, rfl⟩ | ⟨hno, -⟩)
        · rw [(hr out).1 hout]; rfl
        · exact absurd ((hr _).2 rfl) (hno _)
      · rintro rfl; exact Or.inl ⟨_, (hr _).2 rfl, rfl⟩
  | deliver v o t =>
      ext w'
      simp only [Record.Event.ofVocabulary, worldStepOf, NamedWorld.step, Set.mem_setOf_eq]
      have hr : ∀ n', Model.vocabulary.process S (w v) o ⇢ n' ↔
          n' = NamedNode.process S (w v) o := fun n' => returns_pure _ n'
      constructor
      · rintro (⟨n', hn', rfl⟩ | ⟨hno, -⟩)
        · rw [(hr n').1 hn']; rfl
        · exact absurd ((hr _).2 rfl) (hno _)
      · rintro rfl; exact Or.inl ⟨_, (hr _).2 rfl, rfl⟩

/-- At the instance `Model.vocabulary`, a wake event leads from `w` to exactly `w`. -/
theorem worldStepOf_vocabulary_wake (S : Setup V) (w : V → (Model.vocabulary (V := V)).N) (v : V)
    (t : DecoupledConsensusModel.Time) :
    worldStepOf (Model.vocabulary (V := V)) S w (Record.Event.wake v t) = {w} := by
  show ({Function.update w v (w v)} : Set _) = {w}
  rw [Function.update_eq_self]

/-- At the instance `Model.vocabulary`, folding the list `l` of record events from `w` reaches exactly
    one world, the fold of `NamedWorld.step S` over the ticks and deliveries of `l`. -/
theorem foldlM_worldStepOf_vocabulary_erase (S : Setup V) (l : List (Record.Event V))
    (w : V → (Model.vocabulary (V := V)).N) :
    l.foldlM (worldStepOf (Model.vocabulary (V := V)) S) w =
      {(l.filterMap Record.Event.toVocabulary?).foldl (NamedWorld.step S) w} := by
  induction l generalizing w with
  | nil => rfl
  | cons e l ih =>
      rw [List.foldlM_cons, Set.bind_def]
      have hstep : worldStepOf (Model.vocabulary (V := V)) S w e =
          {match e.toVocabulary? with
            | none => w
            | some e' => NamedWorld.step S w e'} := by
        cases e with
        | wake v t => exact worldStepOf_vocabulary_wake S w v t
        | tick v t => exact worldStepOf_vocabulary S w (Generic.Event.tick v t)
        | deliver v o t => exact worldStepOf_vocabulary S w (Generic.Event.deliver v o t)
      rw [hstep, Set.biUnion_singleton, List.filterMap_cons]
      cases e.toVocabulary? with
      | none => exact ih w
      | some e' => exact ih (NamedWorld.step S w e')

/-- At the instance `Model.vocabulary`, folding the embedding of the list `l` from `w` reaches exactly
    one world, the fold of `NamedWorld.step S` over `l`. -/
theorem foldlM_worldStepOf_vocabulary (S : Setup V) (l : List (NamedEvent V))
    (w : V → (Model.vocabulary (V := V)).N) :
    (l.map Record.Event.ofVocabulary).foldlM (worldStepOf (Model.vocabulary (V := V)) S) w =
      {l.foldl (NamedWorld.step S) w} := by
  rw [foldlM_worldStepOf_vocabulary_erase, Event.filterMap_toVocabulary?_map_ofVocabulary]

/-- At the instance `Model.vocabulary`, the embedding of the run `rho` reaches before index `i`
    exactly the world `NamedRun.stateBefore S rho i`. -/
@[record_ofVocabulary] theorem stateBeforeOf_vocabulary (S : Setup V) (rho : NamedRun V) (i : Nat) :
    stateBeforeOf (Model.vocabulary (V := V)) S (Run.ofVocabulary rho) i =
      {NamedRun.stateBefore S rho i} := by
  unfold stateBeforeOf
  rw [Run.ofVocabulary_events, ← List.map_take]
  exact foldlM_worldStepOf_vocabulary S (rho.events.take i) NamedWorld.init

/-- At the instance `Model.vocabulary`, the events of the record run `rho` timed before `t` lead from
    the initial world to exactly one world, `NamedRun.stateBeforeTime S rho.toVocabulary t`. -/
theorem stateBeforeTime_vocabulary_erase (S : Setup V) (rho : Record.Run V)
    (t : DecoupledConsensusModel.Time) :
    (rho.events.filter (fun e => decide (e.time < t))).foldlM
        (worldStepOf (Model.vocabulary (V := V)) S) (fun u => (Model.vocabulary (V := V)).initial S u) =
      {NamedRun.stateBeforeTime S rho.toVocabulary t} := by
  rw [foldlM_worldStepOf_vocabulary_erase, Event.filterMap_filter_time_lt]
  rfl

/-! ## The chain state's added facts at `Model.vocabulary` -/

/-- `Model.vocabulary` satisfies `ChainStateAddedFacts`. -/
theorem Model.vocabulary_facts_csAdded : ChainStateAddedFacts (Model.vocabulary (V := V)) where
  namedFinalizedAt_of_finalityQuorumCoveredByChild := fun E cfg _ _ _ hne hcov hdebt =>
    _root_.DecoupledConsensusModel.Proofs.HealingSurface.namedFinalizedAt_of_finalityQuorumCoveredByChild E cfg hne hcov hdebt
  namedJustifiedAt_of_targetQuorumCoveredByChild := fun E cfg _ hne hcov hnj =>
    _root_.DecoupledConsensusModel.Proofs.HealingSurface.namedJustifiedAt_of_targetQuorumCoveredByChild E cfg hne hcov hnj
  derive_named_finalized_preceq_justified := fun E cfg B =>
    (_root_.DecoupledConsensusModel.Proofs.NamedDerivationGeometry.chainOrder_derive_named E cfg B).finalized_preceq_justified
  confirmation_phaseGrade_mono := by
    intro E hc gv F r p A B hAB bB hbB hB bA hbA
    obtain rfl := (returns_pure _ _).1 hbB; obtain rfl := (returns_pure _ _).1 hbA
    exact _root_.DecoupledConsensusModel.Proofs.HealingSurface.confirmation_phaseGrade_mono E hc gv F r p hAB hB
  matching_finality_e1 := fun a b h entry finalized hv hm hf hne =>
    (priv% Proofs.Vocabulary.Protocol.ChainState.FinalityComparison
      DecoupledConsensusModel.Proofs.NamedFinalizationBridge.matching_finality_e1)
      a b h entry finalized hv hm hf hne
  njEntry_derive_named := _root_.DecoupledConsensusModel.Proofs.NjGap.njEntry_derive_named
  namedJustification_ancestor_data := _root_.DecoupledConsensusModel.Proofs.NamedCheckpointAlgebra.namedJustification_ancestor_data
  justification_certificate := _root_.DecoupledConsensusModel.Proofs.NamedJustificationCertificates.justification_certificate
  finality_certificate := _root_.DecoupledConsensusModel.Proofs.NamedFinalityCertificates.finality_certificate
  cs_with_F_h_F_fields := fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  mem_finalize_process_attestation := fun _ _ _ h => _root_.DecoupledConsensusModel.Protocol.mem_finalize_process_attestation h
  derive_named_node := _root_.DecoupledConsensusModel.Proofs.BlockProcessingDefaults.derive_named_node
  derive_named_of_not_genesis := _root_.DecoupledConsensusModel.Proofs.BlockProcessingDefaults.derive_named_of_not_genesis
  namedJustification_strict_or_eq_of_preceq :=
    _root_.DecoupledConsensusModel.Proofs.HealingSurface.namedJustification_strict_or_eq_of_preceq
  ModelProperties_derive_named_genesis_h_j :=
    _root_.DecoupledConsensusModel.Proofs.ModelProperties.derive_named_genesis_h_j
  namedNj_eq_of_preceq_sameHeight :=
    _root_.DecoupledConsensusModel.Proofs.NamedCheckpointAlgebra.namedNj_eq_of_preceq_sameHeight
  finalized_ancestor_height :=
    _root_.DecoupledConsensusModel.Proofs.NamedCheckpointHeights.finalized_ancestor_height
  transition_height_entry_cases :=
    _root_.DecoupledConsensusModel.Proofs.NamedEntryHeight.transition_height_entry_cases
  crossing_matching_quorum :=
    _root_.DecoupledConsensusModel.Proofs.NamedMatchingProgress.crossing_matching_quorum
  h_j_ne_recovery_height_named :=
    _root_.DecoupledConsensusModel.Proofs.NjGap.h_j_ne_recovery_height_named
  derive_named_T_h_preceq := _root_.DecoupledConsensusModel.Proofs.Optimistic.derive_named_T_h_preceq
  conflictsWithFinality_erase_of_matchesEntry :=
    _root_.DecoupledConsensusModel.Protocol.conflictsWithFinality_erase_of_matchesEntry
  isQuorum_of_targetReady := _root_.DecoupledConsensusModel.Protocol.isQuorum_of_targetReady
  climb_entryYoung_l85 := _root_.DecoupledConsensusModel.Sts.climb_entryYoung_l85
  derive_named_F_cases := _root_.DecoupledConsensusModel.Sts.derive_named_F_cases
  derive_named_genesis_F := _root_.DecoupledConsensusModel.Sts.derive_named_genesis_F
  Sts_derive_named_genesis_h_j := _root_.DecoupledConsensusModel.Sts.derive_named_genesis_h_j
  derive_named_h_j_mono := _root_.DecoupledConsensusModel.Sts.derive_named_h_j_mono
  exists_crossing_ancestor := _root_.DecoupledConsensusModel.Sts.exists_crossing_ancestor
  finalized_entry_quorum := _root_.DecoupledConsensusModel.Sts.finalized_entry_quorum
  finalized_is_entry := _root_.DecoupledConsensusModel.Sts.finalized_is_entry
  justified_preceq_finalized_of_le_f1b1 :=
    _root_.DecoupledConsensusModel.Sts.justified_preceq_finalized_of_le_f1b1
  nj_eq_on_plateau_l85 := _root_.DecoupledConsensusModel.Sts.nj_eq_on_plateau_l85
  nj_false_of_not_dvd_l85 := _root_.DecoupledConsensusModel.Sts.nj_false_of_not_dvd_l85
  progress_spacing_l85 := _root_.DecoupledConsensusModel.Sts.progress_spacing_l85
  windowJustified_l85d := fun E cfg => _root_.DecoupledConsensusModel.Sts.windowJustified_l85d E cfg
  named_transition_latest :=
    _root_.DecoupledConsensusModel.Proofs.NamedDerivationGeometry.named_transition_latest
  process_finality_eq :=
    _root_.DecoupledConsensusModel.Proofs.TargetedTimeoutBinding.process_finality_eq
  process_context_fields :=
    _root_.DecoupledConsensusModel.Proofs.TimeoutBindingDefaults.process_context_fields
  isQuorum_of_finalityReady := _root_.DecoupledConsensusModel.Protocol.isQuorum_of_finalityReady
  advance_height_J := _root_.DecoupledConsensusModel.Protocol.advance_height_J
  advance_height_h_j := _root_.DecoupledConsensusModel.Protocol.advance_height_h_j
  not_Slashable_iff := _root_.DecoupledConsensusModel.Sts.not_Slashable_iff
  Slashable_iff := _root_.DecoupledConsensusModel.Proofs.ModelProperties.Slashable_iff
  nonjustifiable_of := _root_.DecoupledConsensusModel.Proofs.NjGap.nonjustifiable_of
  nonjustifiable_of_le := _root_.DecoupledConsensusModel.Proofs.NjGap.nonjustifiable_of_le
  e1Fields_eq_false_of := _root_.DecoupledConsensusModel.Sts.e1Fields_eq_false_of
  slashable_eq_false_of_fields := _root_.DecoupledConsensusModel.Sts.slashable_eq_false_of_fields
  chainState_initial_h := _root_.DecoupledConsensusModel.Sts.chainState_initial_h
  derive_named_setupWithGST := _root_.DecoupledConsensusModel.Sts.derive_named_setupWithGST
  advance_height_h := _root_.DecoupledConsensusModel.Protocol.advance_height_h
  namedPair_mem_progress_of_suffix_same_height := fun E cfg {_ _ _} hCP haP haC hh hpair => (priv% Proofs.Vocabulary.Protocol.ChainState.RawHeightCoverage DecoupledConsensusModel.Proofs.HealingSurface.namedPair_mem_progress_of_suffix_same_height) E cfg hCP haP haC hh hpair
  namedTarget_mem_of_suffix_same_height := fun E cfg {_ _ _} hCP haP haC hh hpair => (priv% Proofs.Vocabulary.Protocol.ChainState.RawHeightCoverage DecoupledConsensusModel.Proofs.HealingSurface.namedTarget_mem_of_suffix_same_height) E cfg hCP haP haC hh hpair

/-! ## The level-1 facts of each family at `Model.vocabulary` -/

/-- `Model.vocabulary` satisfies `ScheduleFacts`. -/
theorem Model.vocabulary_facts_schedule : ScheduleFacts (Model.vocabulary (V := V)) where
  support_cutoff_mono := fun E _ _ h =>
    _root_.DecoupledConsensusModel.Proofs.Optimistic.support_cutoff_mono E h
  round_of_slotOf_a := by intro S r; exact _root_.DecoupledConsensusModel.Proofs.HealingLemmas.round_of_slotOf_a S r
  slotStart_add_six_delta_eq_confirmation_time := fun E s => _root_.DecoupledConsensusModel.Sts.slotStart_add_six_delta_eq_confirmation_time E s
  slotStart_add_delta_eq_vote_time := fun E s => _root_.DecoupledConsensusModel.Sts.slotStart_add_delta_eq_vote_time E s
  vote_time_succ_add_delta_le_confirmation_time := fun E s => (_root_.DecoupledConsensusModel.Protocol.vote_time_succ_add_delta_eq_confirmation_time E s).le
  a_add_delta_eq_view_freeze := _root_.DecoupledConsensusModel.Proofs.HealingLemmas.a_add_delta_eq_view_freeze (V := V)
  Γ_0_eq_proposal_time := _root_.DecoupledConsensusModel.Protocol.Γ_0_eq_proposal_time (V := V)
  Γ_1_eq_vote_time := _root_.DecoupledConsensusModel.Protocol.Γ_1_eq_vote_time (V := V)
  a_eq_confirmation_time := _root_.DecoupledConsensusModel.Protocol.a_eq_confirmation_time (V := V)
  confirmation_time_eq_support_cutoff_succ := _root_.DecoupledConsensusModel.Protocol.confirmation_time_eq_support_cutoff_succ (V := V)
  publicTime_iff := _root_.DecoupledConsensusModel.Execution.publicTime_iff
  ActionRound_slotOf_confirmation_time := _root_.DecoupledConsensusModel.Proofs.HealingLemmas.ActionRound.slotOf_confirmation_time
  slotOf_of_between' := _root_.DecoupledConsensusModel.Proofs.HealingLemmas.slotOf_of_between'
  Optimistic_proposal_time_nonneg := _root_.DecoupledConsensusModel.Proofs.Optimistic.proposal_time_nonneg
  Optimistic_slotOf_confirmation_time := _root_.DecoupledConsensusModel.Proofs.Optimistic.slotOf_confirmation_time
  slotOf_of_between := _root_.DecoupledConsensusModel.Proofs.Optimistic.slotOf_of_between
  slotOf_proposal_time := _root_.DecoupledConsensusModel.Proofs.Optimistic.slotOf_proposal_time
  slotOf_support_cutoff := _root_.DecoupledConsensusModel.Proofs.Optimistic.slotOf_support_cutoff
  slotOf_vote_time := _root_.DecoupledConsensusModel.Proofs.Optimistic.slotOf_vote_time
  support_cutoff_le_vote_time_succ := _root_.DecoupledConsensusModel.Proofs.Optimistic.support_cutoff_le_vote_time_succ
  Optimistic_support_cutoff_lt_view_freeze := _root_.DecoupledConsensusModel.Proofs.Optimistic.support_cutoff_lt_view_freeze
  support_cutoff_ne_proposal_time := _root_.DecoupledConsensusModel.Proofs.Optimistic.support_cutoff_ne_proposal_time
  support_cutoff_ne_vote_time := _root_.DecoupledConsensusModel.Proofs.Optimistic.support_cutoff_ne_vote_time
  vote_time_ne_proposal_time := _root_.DecoupledConsensusModel.Proofs.Optimistic.vote_time_ne_proposal_time
  equivocates_mono := _root_.DecoupledConsensusModel.Protocol.equivocates_mono
  proposal_time_le_confirmation_time := _root_.DecoupledConsensusModel.Protocol.proposal_time_le_confirmation_time
  proposal_time_lt_vote_time := _root_.DecoupledConsensusModel.Protocol.proposal_time_lt_vote_time
  proposal_time_mono := _root_.DecoupledConsensusModel.Protocol.proposal_time_mono
  proposal_time_mono_local := _root_.DecoupledConsensusModel.Protocol.proposal_time_mono_local
  proposal_time_pos_of_slot_pos := _root_.DecoupledConsensusModel.Protocol.proposal_time_pos_of_slot_pos
  proposal_time_slotOf_le := _root_.DecoupledConsensusModel.Protocol.proposal_time_slotOf_le
  proposal_time_succ_lt_confirmation_time := _root_.DecoupledConsensusModel.Protocol.proposal_time_succ_lt_confirmation_time
  slotOf_of_proposal_before_confirmation := _root_.DecoupledConsensusModel.Protocol.slotOf_of_proposal_before_confirmation
  slotOf_of_proposal_before_freeze := _root_.DecoupledConsensusModel.Protocol.slotOf_of_proposal_before_freeze
  slot_le_slotOf_of_proposal_time_le := _root_.DecoupledConsensusModel.Protocol.slot_le_slotOf_of_proposal_time_le
  Protocol_support_cutoff_le_confirmation_time := _root_.DecoupledConsensusModel.Protocol.support_cutoff_le_confirmation_time
  support_cutoff_le_proposal_time_succ := _root_.DecoupledConsensusModel.Protocol.support_cutoff_le_proposal_time_succ
  support_cutoff_lt_proposal_time_succ := _root_.DecoupledConsensusModel.Protocol.support_cutoff_lt_proposal_time_succ
  view_freeze_add_delta_lt_confirmation_time := _root_.DecoupledConsensusModel.Protocol.view_freeze_add_delta_lt_confirmation_time
  view_freeze_lt_confirmation_time := _root_.DecoupledConsensusModel.Protocol.view_freeze_lt_confirmation_time
  view_freeze_lt_vote_time_succ := _root_.DecoupledConsensusModel.Protocol.view_freeze_lt_vote_time_succ
  Protocol_vote_time_le_confirmation_time := _root_.DecoupledConsensusModel.Protocol.vote_time_le_confirmation_time
  vote_time_mono_slots := _root_.DecoupledConsensusModel.Protocol.vote_time_mono_slots
  confirmation_time_eq_of_delta_eq := _root_.DecoupledConsensusModel.Sts.confirmation_time_eq_of_delta_eq
  confirmation_time_mono := _root_.DecoupledConsensusModel.Sts.confirmation_time_mono
  confirmation_time_mono_l78 := _root_.DecoupledConsensusModel.Sts.confirmation_time_mono_l78
  equivocates_eq_false_of_card_le_one := _root_.DecoupledConsensusModel.Sts.equivocates_eq_false_of_card_le_one
  equivocates_eq_true_iff := _root_.DecoupledConsensusModel.Sts.equivocates_eq_true_iff
  equivocates_mono_of_subset := _root_.DecoupledConsensusModel.Sts.equivocates_mono_of_subset
  exists_confirmation_time_ge := _root_.DecoupledConsensusModel.Sts.exists_confirmation_time_ge
  mem_votes_by_iff := _root_.DecoupledConsensusModel.Sts.mem_votes_by_iff
  participates_eq_true_iff := _root_.DecoupledConsensusModel.Sts.participates_eq_true_iff
  participates_of_equivocates := _root_.DecoupledConsensusModel.Sts.participates_of_equivocates
  proposal_time_emod_delta_inclX := _root_.DecoupledConsensusModel.Sts.proposal_time_emod_delta_inclX
  proposal_time_eq_of_delta_eq := _root_.DecoupledConsensusModel.Sts.proposal_time_eq_of_delta_eq
  Sts_proposal_time_nonneg := _root_.DecoupledConsensusModel.Sts.proposal_time_nonneg
  proposal_wake_start_le_proposal_time := fun S s => by
    show Protocol.proposal_time S.E s - S.E.Δ ≤ Protocol.proposal_time S.E s
    linarith [S.E.Δ_pos]
  proposal_wake_start_lt_proposal_time := fun S s => by
    show Protocol.proposal_time S.E s - S.E.Δ < Protocol.proposal_time S.E s
    linarith [S.E.Δ_pos]
  slot_pos_of_proposal_time_pos_inclX := _root_.DecoupledConsensusModel.Sts.slot_pos_of_proposal_time_pos_inclX
  support_cutoff_emod_delta := _root_.DecoupledConsensusModel.Sts.support_cutoff_emod_delta
  Sts_support_cutoff_le_confirmation_time := _root_.DecoupledConsensusModel.Sts.support_cutoff_le_confirmation_time
  Sts_support_cutoff_lt_view_freeze := _root_.DecoupledConsensusModel.Sts.support_cutoff_lt_view_freeze
  support_cutoff_pos := _root_.DecoupledConsensusModel.Sts.support_cutoff_pos
  voteTime_lt_nextProposal_l86d := _root_.DecoupledConsensusModel.Sts.voteTime_lt_nextProposal_l86d
  voteWindow_prev_inPhase := _root_.DecoupledConsensusModel.Sts.voteWindow_prev_inPhase
  vote_time_add_delta_le_confirmation_time := _root_.DecoupledConsensusModel.Sts.vote_time_add_delta_le_confirmation_time
  vote_time_emod_delta := _root_.DecoupledConsensusModel.Sts.vote_time_emod_delta
  Sts_vote_time_le_confirmation_time := _root_.DecoupledConsensusModel.Sts.vote_time_le_confirmation_time
  vote_time_mono := _root_.DecoupledConsensusModel.Sts.vote_time_mono
  vote_time_pos := _root_.DecoupledConsensusModel.Sts.vote_time_pos
  support_cutoff_lt_vote_time_imp_lt_proposal_time := _root_.DecoupledConsensusModel.Protocol.support_cutoff_lt_vote_time_imp_lt_proposal_time
  slotOf_of_proposal_before_next_proposal := fun E s {_} hlo hhi => (priv% Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.RecoveryProposalCapInputs DecoupledConsensusModel.Proofs.HealingSurface.slotOf_of_proposal_before_next_proposal) E s hlo hhi
  confirmationTime_lt_proposalTime_of_two_le := fun E {_ _} h => (priv% Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep DecoupledConsensusModel.Proofs.HealingSurface.confirmationTime_lt_proposalTime_of_two_le) E h
  on_goldfish_vote_insert := _root_.DecoupledConsensusModel.Protocol.on_goldfish_vote_insert
  mem_voter_support_view_of_pool := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.mem_voter_support_view_of_pool
  action_round_le_of_lt_proposal := _root_.DecoupledConsensusModel.Protocol.action_round_le_of_lt_proposal
  view_freeze_add_delta_le_proposal_time_succ := fun E s => le_of_eq (_root_.DecoupledConsensusModel.Protocol.view_freeze_add_delta_eq_proposal_time_succ E s)
  vote_time_le_view_freeze := fun E s => by have h1 := _root_.DecoupledConsensusModel.Sts.slotStart_add_delta_eq_vote_time E s; have h2 := _root_.DecoupledConsensusModel.Sts.slotStart_eq_proposal_time E s; have h3 := _root_.DecoupledConsensusModel.Sts.proposal_time_add_three_delta_eq_view_freeze E s; have hΔ := E.Δ_pos; simp only [Record.Model.vocabulary]; linarith
  slot_instants_l55 := fun E s => _root_.DecoupledConsensusModel.Sts.slot_instants_l55 E s

/-- `Model.vocabulary` satisfies `StoreFacts`. -/
theorem Model.vocabulary_facts_store : StoreFacts (Model.vocabulary (V := V)) where
  tau_eq_of_fields := fun hT hb hv => congrArg pure (_root_.DecoupledConsensusModel.Sts.tau_eq_of_fields hT hb hv)
  store_with_t_s_timestamp_vote := fun _ _ _ => rfl
  store_with_σ_T_timestamp_block_T := fun _ _ _ _ _ _ _ _ => rfl
  store_with_σ_T_timestamp_block_h_max := fun _ _ _ _ => rfl
  store_with_σ_T_timestamp_block_J := fun _ _ _ _ => rfl
  store_with_σ_T_timestamp_block_h_j := fun _ _ _ _ => rfl
  pool_view_mem := by intro st h row hrow; exact _root_.DecoupledConsensusModel.Proofs.NamedAdmission.pool_view_mem st h row hrow
  store_with_σ_T_timestamp_block_σ := fun _ _ _ _ => rfl
  store_with_σ_T_timestamp_block_F := fun _ _ _ _ => rfl
  store_with_t_s_s := fun _ _ _ => rfl
  committeePools_init := fun E => _root_.DecoupledConsensusModel.Protocol.CommitteePools.init E
  poolStep_tickStore := fun st t s hle h => let r := _root_.DecoupledConsensusModel.Protocol.poolStep_tickStore st t s hle ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩; ⟨⟨r.1.mem, r.1.stamp⟩, r.2.slot, r.2.stamped, r.2.pooled, r.2.bounded⟩
  pool_set_clock_slot := _root_.DecoupledConsensusModel.Sts.pool_set_clock_slot
  mem_pool_iff := _root_.DecoupledConsensusModel.Proofs.ModelProperties.mem_pool_iff
  ModelProperties_mem_sg_pool_iff := _root_.DecoupledConsensusModel.Proofs.ModelProperties.mem_sg_pool_iff
  ModelProperties_toHealing_F := _root_.DecoupledConsensusModel.Proofs.ModelProperties.toHealing_F
  ModelProperties_toHealing_J := _root_.DecoupledConsensusModel.Proofs.ModelProperties.toHealing_J
  toHealing_T := _root_.DecoupledConsensusModel.Proofs.ModelProperties.toHealing_T
  ModelProperties_toHealing_h_max := _root_.DecoupledConsensusModel.Proofs.ModelProperties.toHealing_h_max
  toHealing_live_confirmed := _root_.DecoupledConsensusModel.Proofs.ModelProperties.toHealing_live_confirmed
  toHealing_s := _root_.DecoupledConsensusModel.Proofs.ModelProperties.toHealing_s
  ModelProperties_toHealing_sg_votes := _root_.DecoupledConsensusModel.Proofs.ModelProperties.toHealing_sg_votes
  ModelProperties_toHealing_σ := _root_.DecoupledConsensusModel.Proofs.ModelProperties.toHealing_σ
  sgVote_confirmed := _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.sgVote_confirmed
  sgVote_round := _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.sgVote_round
  sgVote_val := _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.sgVote_val
  toHealing_slot := _root_.DecoupledConsensusModel.Proofs.Optimistic.toHealing_slot
  head_slot_le_of_tau := by
    intro st Γ u H hfind tm htm h; obtain rfl := (returns_pure _ _).1 htm
    exact _root_.DecoupledConsensusModel.Sts.head_slot_le_of_tau st hfind h
  mem_goldfishStore_pool_iff := _root_.DecoupledConsensusModel.Sts.mem_goldfishStore_pool_iff
  Sts_mem_sg_pool_iff := _root_.DecoupledConsensusModel.Sts.mem_sg_pool_iff
  mem_store_pool_iff := _root_.DecoupledConsensusModel.Sts.mem_store_pool_iff
  pool_eq_of_gf_votes_eq := _root_.DecoupledConsensusModel.Sts.pool_eq_of_gf_votes_eq
  resolved_eq_true_iff := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.resolved_eq_true_iff
  sgVote_confirmed_eq := _root_.DecoupledConsensusModel.Sts.sgVote_confirmed_eq
  sgVote_eq_of_fields := _root_.DecoupledConsensusModel.Sts.sgVote_eq_of_fields
  sgVote_erase_eq_of_fields := _root_.DecoupledConsensusModel.Sts.sgVote_erase_eq_of_fields
  sgVote_round_eq_round := _root_.DecoupledConsensusModel.Sts.sgVote_round_eq_round
  sgVote_val_index_eq_val_index := _root_.DecoupledConsensusModel.Sts.sgVote_val_index_eq_val_index
  stampedBefore_block_of_tau := by
    intro st Γ u H hfind tm htm h; obtain rfl := (returns_pure _ _).1 htm
    exact _root_.DecoupledConsensusModel.Sts.stampedBefore_block_of_tau st hfind h
  stampedBefore_store_tau_of := by
    intro st Γ u H hfind hslot hv hH tm htm; obtain rfl := (returns_pure _ _).1 htm
    exact _root_.DecoupledConsensusModel.Sts.stampedBefore_store_tau_of st hfind hslot hv hH
  stampedBefore_tau_of := by
    intro gs Γ u H hfind hslot hv hH tm htm; obtain rfl := (returns_pure _ _).1 htm
    exact _root_.DecoupledConsensusModel.Sts.stampedBefore_tau_of gs hfind hslot hv hH
  stampedBefore_vote_of_tau := by
    intro st Γ u tm htm h; obtain rfl := (returns_pure _ _).1 htm
    exact _root_.DecoupledConsensusModel.Sts.stampedBefore_vote_of_tau st h
  tau_eq_max := by
    intro st u X hX hXs τ σ hτ hσ tm htm; obtain rfl := (returns_pure _ _).1 htm
    exact _root_.DecoupledConsensusModel.Sts.tau_eq_max st hX hXs hτ hσ
  tau_eq_max_gf := by
    intro gs u X hX hXs τ σ hτ hσ tm htm; obtain rfl := (returns_pure _ _).1 htm
    exact _root_.DecoupledConsensusModel.Sts.tau_eq_max_gf gs hX hXs hτ hσ
  Sts_toHealing_F := _root_.DecoupledConsensusModel.Sts.toHealing_F
  Sts_toHealing_J := _root_.DecoupledConsensusModel.Sts.toHealing_J
  toHealing_gs_T := _root_.DecoupledConsensusModel.Sts.toHealing_gs_T
  toHealing_gs_gf_votes := _root_.DecoupledConsensusModel.Sts.toHealing_gs_gf_votes
  toHealing_gs_pool := _root_.DecoupledConsensusModel.Sts.toHealing_gs_pool
  toHealing_gs_s := _root_.DecoupledConsensusModel.Sts.toHealing_gs_s
  toHealing_gs_timestamp_block := _root_.DecoupledConsensusModel.Sts.toHealing_gs_timestamp_block
  toHealing_gs_timestamp_vote := _root_.DecoupledConsensusModel.Sts.toHealing_gs_timestamp_vote
  toHealing_h_j := _root_.DecoupledConsensusModel.Sts.toHealing_h_j
  Sts_toHealing_h_max := _root_.DecoupledConsensusModel.Sts.toHealing_h_max
  Sts_toHealing_sg_votes := _root_.DecoupledConsensusModel.Sts.toHealing_sg_votes
  Sts_toHealing_σ := _root_.DecoupledConsensusModel.Sts.toHealing_σ
  resolved_nonempty := fun _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  tau_nonempty := fun _ => ⟨_, (returns_pure _ _).2 rfl⟩
  reachedStore_setClock := by intros; trivial
  rootFresh_of_distinct := by intros; trivial

/-- `Model.vocabulary` satisfies `ForkChoiceFacts`. -/
theorem Model.vocabulary_facts_forkChoice : ForkChoiceFacts (Model.vocabulary (V := V)) where
  goldfish_passes_cone := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    intro E σ h_max T tree cur votes support k Hon A B hmaj hcounted hsub hno hvote hvalid hAB hpath
    exact _root_.DecoupledConsensusModel.Proofs.Optimistic.goldfish_passes_cone E σ h_max T tree cur votes support k Hon ⟨hmaj, hcounted, hsub, hno, hvote⟩ hvalid hAB hpath
  ghost_passes_cone := by
    intro E T tree votes support late s Hon A B hmaj hcounted hsub hno hvote hvalid hAB hpath score hscore X hX
    have h1 : score = Protocol.goldfish_score E T votes support s :=
      funext fun C => (returns_pure _ _).1 (hscore C)
    subst h1
    obtain rfl := (returns_pure _ _).1 hX
    exact _root_.DecoupledConsensusModel.Proofs.Optimistic.ghost_passes_cone E T tree votes support late s Hon ⟨hmaj, hcounted, hsub, hno, hvote⟩ hvalid hAB hpath
  eligible_compatible := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact fun hNv1 hNv2 hNw1 hNw2 ht1 hr1 ht2 hr2 hC hD => _root_.DecoupledConsensusModel.Protocol.eligible_compatible ⟨hNv1, hNv2⟩ ⟨hNw1, hNw2⟩ ⟨ht1, hr1⟩ ⟨ht2, hr2⟩ hC hD
  fg_root_preceq_get_sg_root_with_frame := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.HealingSurface.fg_root_preceq_get_sg_root_with_frame
  Optimistic_mem_voter_support_view_of_pool := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact fun E gst s _ h =>
      _root_.DecoupledConsensusModel.Proofs.Optimistic.mem_voter_support_view_of_pool E gst s h
  get_head_in_tree_split_with := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    intro contract E hc st tree votes support_votes k X
    exact Iff.of_eq (congrArg (X = ·) (_root_.DecoupledConsensusModel.Proofs.Optimistic.get_head_in_tree_split_with contract E hc st tree votes support_votes k))
  voter_candidate_tree_eq_protocol_voter_filtered_block_tree := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact fun E st => _root_.DecoupledConsensusModel.Proofs.Optimistic.voter_candidate_tree_eq_protocol_voter_filtered_block_tree E st
  confirmation_adoption := by
    intro E sourceTree targetTree sourceEarly sourceLate sourceVotes targetVotes targetSupport s B h1 h2 tS htS tT htT hf hb g hg he sS hsS sT hsT
    have e1 : tS = Protocol.targets_under sourceTree B := funext fun u => (returns_pure _ _).1 (htS u)
    have e2 : tT = Protocol.targets_under targetTree B := funext fun u => (returns_pure _ _).1 (htT u)
    subst e1 e2
    obtain rfl := (returns_pure _ _).1 hg
    obtain rfl := (returns_pure _ _).1 hsS
    obtain rfl := (returns_pure _ _).1 hsT
    exact _root_.DecoupledConsensusModel.Protocol.confirmation_adoption ⟨h1, h2⟩ ⟨hf, hb⟩ he
  canonicalConeSegment_mem_filtered_of_root_preceq := _root_.DecoupledConsensusModel.Proofs.HealingSurface.canonicalConeSegment_mem_filtered_of_root_preceq (V := V)
  goldfish_fork_choice_captures_supporter_majority := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Protocol.goldfish_fork_choice_captures_supporter_majority
  mem_supporters_iff := by
    intro E T votes support_votes s B x R hR t ht
    have e1 : t = Protocol.targets_under T B := funext fun u => (returns_pure _ _).1 (ht u)
    subst e1
    obtain rfl := (returns_pure _ _).1 hR
    exact _root_.DecoupledConsensusModel.Protocol.mem_supporters_iff (V := V) (E := E)
  get_fg_root_toHealing_clock := _root_.DecoupledConsensusModel.Proofs.ModelProperties.get_fg_root_toHealing_clock
  get_filtered_block_tree_toHealing_clock := _root_.DecoupledConsensusModel.Proofs.ModelProperties.get_filtered_block_tree_toHealing_clock
  mem_viable_tree_iff := _root_.DecoupledConsensusModel.Proofs.ModelProperties.mem_viable_tree_iff
  get_filtered_block_tree_from_subset := _root_.DecoupledConsensusModel.Proofs.Records.get_filtered_block_tree_from_subset
  ghost_step_child := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Protocol.ghost_step_child
  ghost_transport_via_bridge_of_target_passes := by
    intro sourceTree targetTree sourceScore targetScore sourceEligible targetEligible sourceAnchor targetAnchor bridge H h1 h2 G hG hGH h3 h4 h5 h6 G' hG' h7 step hstep h8 h9 h10
    have e1 : step = Protocol.ghost_step sourceTree sourceScore sourceEligible :=
      funext fun X => (returns_pure _ _).1 (hstep X)
    subst e1
    obtain rfl := (returns_pure _ _).1 hG
    obtain rfl := (returns_pure _ _).1 hG'
    exact _root_.DecoupledConsensusModel.Protocol.ghost_transport_via_bridge_of_target_passes h1 h2 hGH h3 h4 h5 h6 h7 h8 h9 h10
  get_fg_root_set_clock_slot := _root_.DecoupledConsensusModel.Sts.get_fg_root_set_clock_slot
  get_filtered_block_tree_set_clock_slot := _root_.DecoupledConsensusModel.Sts.get_filtered_block_tree_set_clock_slot
  mem_get_filtered_block_tree_from_of_parts_explicit := _root_.DecoupledConsensusModel.Sts.mem_get_filtered_block_tree_from_of_parts_explicit
  mem_get_filtered_block_tree_from_parts := _root_.DecoupledConsensusModel.Sts.mem_get_filtered_block_tree_from_parts
  mem_voter_view_of_pool := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.mem_voter_view_of_pool
  no_second_vote_in_eq_true_iff := _root_.DecoupledConsensusModel.Sts.no_second_vote_in_eq_true_iff
  no_second_vote_in_of_forall := _root_.DecoupledConsensusModel.Sts.no_second_vote_in_of_forall
  parts_of_mem_get_filtered_block_tree_from := _root_.DecoupledConsensusModel.Sts.parts_of_mem_get_filtered_block_tree_from
  proposer_view_set_clock_slot := _root_.DecoupledConsensusModel.Sts.proposer_view_set_clock_slot
  voter_view_set_clock_slot := by
    simp only [Model.vocabulary, returns_pure]
    intro E st t s k Y
    exact Iff.of_eq (congrArg (Y = ·) (_root_.DecoupledConsensusModel.Sts.voter_view_set_clock_slot E st t s k))
  fg_root_Preceq_get_sg_root_with_gradeContract := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.fg_root_Preceq_get_sg_root_with_gradeContract
  finalized_preceq_of_mem_get_filtered_block_tree := _root_.DecoupledConsensusModel.Proofs.ModelProperties.finalized_preceq_of_mem_get_filtered_block_tree
  get_fg_root_toHealing_eq_of_fields := _root_.DecoupledConsensusModel.Proofs.ModelProperties.get_fg_root_toHealing_eq_of_fields
  get_fg_root_toHealing_of_eq := _root_.DecoupledConsensusModel.Proofs.ModelProperties.get_fg_root_toHealing_of_eq
  get_fg_root_toHealing_of_ne := _root_.DecoupledConsensusModel.Proofs.ModelProperties.get_fg_root_toHealing_of_ne
  ModelProperties_get_head_in_tree_with_layer_mem := by
    simp only [Model.vocabulary, Model.Contract.read, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.get_head_in_tree_with_layer_mem
  get_head_with_mem_filtered := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.get_head_with_mem_filtered
  get_sg_root_with_eq_read_anchor := by
    simp only [Model.vocabulary, Model.Contract.read, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.get_sg_root_with_eq_read_anchor
  get_sg_root_with_gradeContract_mem_filtered := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.get_sg_root_with_gradeContract_mem_filtered
  goldfish_vote_with_snd_of_mem_committee := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.goldfish_vote_with_snd_of_mem_committee
  read_anchor_preceq_get_head_in_tree_with_layer := by
    simp only [Model.vocabulary, Model.Contract.read, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.read_anchor_preceq_get_head_in_tree_with_layer
  mem_latest_window := _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.mem_latest_window
  q10_filtered_F := _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.q10_filtered_F
  window_bounds := _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.window_bounds
  ghost_eq_of_compatible_anchor_and_terminal := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.Optimistic.ghost_eq_of_compatible_anchor_and_terminal
  ghost_insert_eq := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.Optimistic.ghost_insert_eq
  goldfish_eligible_iff := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.Optimistic.goldfish_eligible_iff
  get_filtered_block_tree_subset := _root_.DecoupledConsensusModel.Proofs.Records.get_filtered_block_tree_subset
  ghost_mem := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.Records.ghost_mem
  mem_filtered_of_preceq := _root_.DecoupledConsensusModel.Proofs.Records.mem_filtered_of_preceq
  preceq_get_fg_root_of_F := _root_.DecoupledConsensusModel.Proofs.Records.preceq_get_fg_root_of_F
  preceq_get_fg_root_of_mem_filtered := _root_.DecoupledConsensusModel.Proofs.Records.preceq_get_fg_root_of_mem_filtered
  carried_raw_subset_voter_view := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Protocol.carried_raw_subset_voter_view
  ghost_eligible := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Protocol.ghost_eligible
  ghost_preceq := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Protocol.ghost_preceq
  pred_mem_latest_window := _root_.DecoupledConsensusModel.Protocol.pred_mem_latest_window
  targets_under_iff := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Protocol.targets_under_iff
  voter_support_view_subset := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Protocol.voter_support_view_subset
  voters_count_le_committee := _root_.DecoupledConsensusModel.Protocol.voters_count_le_committee
  card_le_voters_count_of_participates := _root_.DecoupledConsensusModel.Sts.card_le_voters_count_of_participates
  fgRoot_Preceq_get_head_in_tree_with_layer_gradeContract := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.fgRoot_Preceq_get_head_in_tree_with_layer_gradeContract
  fgRoot_compatible_ofJustifiedBranch := _root_.DecoupledConsensusModel.Sts.fgRoot_compatible_ofJustifiedBranch
  fgRoot_compatible_of_compatible := _root_.DecoupledConsensusModel.Sts.fgRoot_compatible_of_compatible
  fgRoot_preceq := _root_.DecoupledConsensusModel.Sts.fgRoot_preceq
  fgRoot_preceq_ofJustifiedBranch := _root_.DecoupledConsensusModel.Sts.fgRoot_preceq_ofJustifiedBranch
  finalized_preceq_get_fg_root := _root_.DecoupledConsensusModel.Sts.finalized_preceq_get_fg_root
  get_fg_root_eq_J_or_F := _root_.DecoupledConsensusModel.Sts.get_fg_root_eq_J_or_F
  get_head_in_tree_with_layer_anchor_or_mem := by
    simp only [Model.vocabulary, Model.Contract.read, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.get_head_in_tree_with_layer_anchor_or_mem
  Sts_get_head_in_tree_with_layer_mem := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.get_head_in_tree_with_layer_mem
  get_head_with_gradeContract_mem := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.get_head_with_gradeContract_mem
  goldfish_eligible_eq_false_of_parent_fork_choice := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.goldfish_eligible_eq_false_of_parent_fork_choice
  goldfish_eligible_false_of_parent_head := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.goldfish_eligible_false_of_parent_head
  goldfish_fork_choice_eq_child_of_pivot := by
    intro E σp σv hp hv TPs TVs Tp Tv cur votesP supportP votesV supportV s' Ap Av Y P B hrootP hrootV GP hGP hsource hApY hAvY hYP GV hGV hpasses hhP hhV scV hscV scP hscP hscore hcount hpathV hchildV hBonly hB hBpar hBslot hfresh
    have e1 : scV = Protocol.goldfish_score E TVs votesV supportV s' :=
      funext fun C => (returns_pure _ _).1 (hscV C)
    have e2 : scP = Protocol.goldfish_score E TPs votesP supportP s' :=
      funext fun C => (returns_pure _ _).1 (hscP C)
    subst e1 e2
    obtain rfl := (returns_pure _ _).1 hGP
    obtain rfl := (returns_pure _ _).1 hGV
    exact _root_.DecoupledConsensusModel.Sts.goldfish_fork_choice_eq_child_of_pivot E hrootP hrootV hsource hApY hAvY hYP hpasses hhP hhV hscore hcount hpathV hchildV hBonly hB hBpar hBslot hfresh
  goldfish_fork_choice_eq_ghost := by
    intro E σ h_max T cur A tree votes support s score hscore elig helig X
    have e1 : score = Protocol.goldfish_score E T votes support s :=
      funext fun B => (returns_pure _ _).1 (hscore B)
    have e2 : elig = Protocol.goldfish_eligible E σ h_max T cur votes support s :=
      funext fun B => (returns_pure _ _).1 (helig B)
    subst e1 e2
    exact Iff.of_eq (congrArg (· ⇢ X) (congrArg pure (_root_.DecoupledConsensusModel.Sts.goldfish_fork_choice_eq_ghost E σ h_max T cur A tree votes support s)))
  goldfish_score_eq_of_iff := by
    intro E T T' votes support votes' support' s C heq t ht t' ht' hsup g hg g' hg'
    have h1 : t = Protocol.targets_under T C := funext fun u => (returns_pure _ _).1 (ht u)
    have h2 : t' = Protocol.targets_under T' C := funext fun u => (returns_pure _ _).1 (ht' u)
    subst h1 h2
    obtain rfl := (returns_pure _ _).1 hg
    obtain rfl := (returns_pure _ _).1 hg'
    exact _root_.DecoupledConsensusModel.Sts.goldfish_score_eq_of_iff E s C heq hsup
  mem_T_of_mem_voter_processed_block_tree := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.mem_T_of_mem_voter_processed_block_tree
  mem_get_filtered_block_tree_of_parts := _root_.DecoupledConsensusModel.Sts.mem_get_filtered_block_tree_of_parts
  mem_latest_window_ge := _root_.DecoupledConsensusModel.Sts.mem_latest_window_ge
  mem_latest_window_lt := _root_.DecoupledConsensusModel.Sts.mem_latest_window_lt
  mem_proposer_support_view_iff := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.mem_proposer_support_view_iff
  mem_voter_processed_block_tree_of_proposal := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.mem_voter_processed_block_tree_of_proposal
  mem_voter_processed_block_tree_of_slot := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.mem_voter_processed_block_tree_of_slot
  mem_voter_processed_block_tree_of_stamped := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.mem_voter_processed_block_tree_of_stamped
  mem_voter_support_view_of_carried := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.mem_voter_support_view_of_carried
  mem_voter_view_of_carried := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.mem_voter_view_of_carried
  namedDuties_goldfish_vote_with_snd_eq_some := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.namedDuties_goldfish_vote_with_snd_eq_some
  namedDuties_goldfish_vote_with_snd_head := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.namedDuties_goldfish_vote_with_snd_head
  parts_of_mem_get_filtered_block_tree := _root_.DecoupledConsensusModel.Sts.parts_of_mem_get_filtered_block_tree
  proposer_view_eq := _root_.DecoupledConsensusModel.Sts.proposer_view_eq
  proposer_view_toFinset := _root_.DecoupledConsensusModel.Sts.proposer_view_toFinset
  targets_under_eq_true_iff := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.targets_under_eq_true_iff
  viable_witness_of_mem_get_filtered_block_tree := _root_.DecoupledConsensusModel.Sts.viable_witness_of_mem_get_filtered_block_tree
  voter_processed_block_tree_cases := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.voter_processed_block_tree_cases
  voter_support_view_cases := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.voter_support_view_cases
  voter_view_cases := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.voter_view_cases
  voter_view_cases_beforeCutoff := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.voter_view_cases_beforeCutoff
  voters_count_eq_of_participates := _root_.DecoupledConsensusModel.Sts.voters_count_eq_of_participates
  NamedProposalParent_get_head_with_mem := fun gc E hc st votes support k G hG hanchor X hX => by obtain rfl := (returns_pure _ _).1 hG; obtain rfl := (returns_pure _ _).1 hX; exact _root_.DecoupledConsensusModel.Proofs.NamedProposalParent.get_head_with_mem gc E hc st votes support k hanchor
  targets_under_nonempty := by intro T B u; exact ⟨_, (returns_pure _ _).2 rfl⟩
  goldfish_score_nonempty := fun _ _ _ _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  voter_filtered_block_tree_nonempty := fun _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  voter_view_nonempty := fun _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  voter_support_view_nonempty := fun _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  get_head_in_tree_with_layer_nonempty := fun _ _ _ _ _ _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  raw_supporters_nonempty := fun _ _ _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  proposer_support_view_nonempty := fun _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  get_head_with_nonempty := fun _ _ _ _ _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  get_sg_root_with_nonempty := fun _ _ _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  goldfish_eligible_nonempty := fun _ _ _ _ _ _ _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  voter_processed_block_tree_nonempty := fun _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  ConeSupport_eligible := fun E T votes support late s Hon tgt C hmaj hcounted hsub hno hvote hvalid hC g hg => by obtain rfl := (returns_pure _ _).1 hg; exact _root_.DecoupledConsensusModel.Proofs.Optimistic.ConeSupport.eligible ⟨hmaj, hcounted, hsub, hno, hvote⟩ hvalid hC
  goldfish_score_le_of_Preceq := by
    intro E T votes support s C D h gC hgC gD hgD
    obtain rfl := (returns_pure _ _).1 hgC; obtain rfl := (returns_pure _ _).1 hgD
    exact _root_.DecoupledConsensusModel.Sts.goldfish_score_le_of_Preceq E T votes support s h
  voter_filtered_block_tree_subset_filtered := fun E st X hX => by obtain rfl := (returns_pure _ _).1 hX; exact (priv% Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.HeightProgressClosurescoreEq DecoupledConsensusModel.Proofs.HealingSurface.pinScoreEq_voterCandidateTree_subset_filtered) E st
  ghost_nonempty := fun _ _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  ghost_step_nonempty := fun _ _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  Numerator_score_eq_supporters := by
    intro early late votes hel hf E T s B sc hsc R hR
    obtain rfl := (returns_pure _ _).1 hsc
    obtain rfl := (returns_pure _ _).1 hR
    exact _root_.DecoupledConsensusModel.Protocol.Numerator.score_eq_supporters ⟨hel, hf⟩ E T s B

/-- `Model.vocabulary` satisfies `ValidatorClientFacts`. -/
theorem Model.vocabulary_facts_validatorClient :
    ValidatorClientFacts (Model.vocabulary (V := V)) where
  create_attestation_saves := _root_.DecoupledConsensusModel.Proofs.HealingSurface.create_attestation_saves
  height_pair_timeout_of_fresh_of_finality_avoids := fun hfresh fp havoid => _root_.DecoupledConsensusModel.Proofs.HealingSurface.height_pair_timeout_of_fresh_of_finality_avoids hfresh fp havoid
  round_action_height_pair_cases := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.HealingSurface.round_action_height_pair_cases
  record_attestation_lock_eq_own_lock := _root_.DecoupledConsensusModel.Proofs.HealingSurface.record_attestation_lock_eq_own_lock
  create_attestation_fst := _root_.DecoupledConsensusModel.Proofs.ModelProperties.create_attestation_fst
  height_pair_cases := _root_.DecoupledConsensusModel.Proofs.Engine.height_pair_cases
  create_attestation_lock_mono := _root_.DecoupledConsensusModel.Proofs.HealingSurface.create_attestation_lock_mono
  create_attestation_no_self_E1 := _root_.DecoupledConsensusModel.Proofs.HealingSurface.create_attestation_no_self_E1
  encodeHeight_none := _root_.DecoupledConsensusModel.Proofs.HealingSurface.encodeHeight_none
  encodeHeight_of_target := fun {H T nu g X} => @_root_.DecoupledConsensusModel.Proofs.HealingSurface.encodeHeight_of_target H T nu g X
  encodeHeight_of_timeout := fun {H T nu g} => @_root_.DecoupledConsensusModel.Proofs.HealingSurface.encodeHeight_of_timeout H T nu g
  height_pair_eq_target_of_aligned_lock := _root_.DecoupledConsensusModel.Proofs.HealingSurface.height_pair_eq_target_of_aligned_lock
  height_pair_eq_target_of_no_lock_no_target_justifiable := _root_.DecoupledConsensusModel.Proofs.HealingSurface.height_pair_eq_target_of_no_lock_no_target_justifiable
  height_pair_eq_target_of_no_lock_recorded_target := _root_.DecoupledConsensusModel.Proofs.HealingSurface.height_pair_eq_target_of_no_lock_recorded_target
  height_pair_eq_timeout_of_no_lock_no_target_nonjustifiable := _root_.DecoupledConsensusModel.Proofs.HealingSurface.height_pair_eq_timeout_of_no_lock_no_target_nonjustifiable
  height_pair_eq_timeout_of_no_lock_off_target_record := _root_.DecoupledConsensusModel.Proofs.HealingSurface.height_pair_eq_timeout_of_no_lock_off_target_record
  height_pair_eq_timeout_of_timeout := _root_.DecoupledConsensusModel.Proofs.HealingSurface.height_pair_eq_timeout_of_timeout
  create_attestation_snd_finality_pair := _root_.DecoupledConsensusModel.Proofs.ModelProperties.create_attestation_snd_finality_pair
  own_lock_some_self := _root_.DecoupledConsensusModel.Proofs.ModelProperties.own_lock_some_self
  finality_pair_height := _root_.DecoupledConsensusModel.Proofs.finality_pair_height
  finality_pair_target := fun {Λ h_j J h_F h T} hp => by
    have hp' : _root_.DecoupledConsensusModel.Protocol.finality_pair Λ h_j J h_F = some ⟨h, T⟩ := hp
    simp only [_root_.DecoupledConsensusModel.Protocol.finality_pair] at hp'
    split_ifs at hp'
    simp_all
  encodeHeight_empty := _root_.DecoupledConsensusModel.Sts.encodeHeight_empty
  encodeHeight_vote_inv_l85c := _root_.DecoupledConsensusModel.Sts.encodeHeight_vote_inv_l85c
  fields_of_encodeHeight_vote := _root_.DecoupledConsensusModel.Sts.fields_of_encodeHeight_vote
  height_pair_cases_l85c := _root_.DecoupledConsensusModel.Sts.height_pair_cases_l85c
  own_lock_none := _root_.DecoupledConsensusModel.Sts.own_lock_none
  own_lock_some_of_ne := _root_.DecoupledConsensusModel.Sts.own_lock_some_of_ne
  own_lock_some_of_ne_explicit := _root_.DecoupledConsensusModel.Sts.own_lock_some_of_ne_explicit
  own_lock_some_pair_of_ne := _root_.DecoupledConsensusModel.Sts.own_lock_some_pair_of_ne

/-- `Model.vocabulary` satisfies `GradesFacts`. -/
theorem Model.vocabulary_facts_grades : GradesFacts (Model.vocabulary (V := V)) where
  domain_le_action := _root_.DecoupledConsensusModel.Sts.domain_le_action
  healA_succ_round := fun hc Δ r => _root_.DecoupledConsensusModel.Sts.healA_succ_round hc Δ r
  opening_add := fun E hc r k => _root_.DecoupledConsensusModel.Sts.opening_add E hc r k
  opening_eq_proposal_time := _root_.DecoupledConsensusModel.Sts.opening_eq_proposal_time
  early_g2_le_opening := fun S r => _root_.DecoupledConsensusModel.Sts.early_g2_le_opening S r
  action_succ_eq_add_rounds := fun S r => _root_.DecoupledConsensusModel.Sts.action_succ_eq_add_rounds S r
  domain_le_a := _root_.DecoupledConsensusModel.Proofs.FrameForward.domain_le_a
  attestWindow_prev_inPhase := _root_.DecoupledConsensusModel.Sts.attestWindow_prev_inPhase
  le_opening_add_toNat := _root_.DecoupledConsensusModel.Sts.le_opening_add_toNat
  domain_add_five_delta_le_action := _root_.DecoupledConsensusModel.Sts.domain_add_five_delta_le_action
  supports_transport_with_cap := fun covers _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h => (priv% Proofs.Vocabulary.Protocol.Grades.OppositionGradeTransport DecoupledConsensusModel.Protocol.supports_transport_with_cap) covers h1 h2 h3 h4 h5 h6 h
  opposition_back_with_cap := fun covers _ _ _ _ _ _ _ h1 h2 h3 h4 h => (priv% Proofs.Vocabulary.Protocol.Grades.OppositionGradeTransport DecoupledConsensusModel.Protocol.opposition_back_with_cap) covers h1 h2 h3 h4 h
  early_g2_eq := _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.early_g2_eq
  action_add_delta_le_next_Γ_neg1 := _root_.DecoupledConsensusModel.Proofs.HealingSurface.action_add_delta_le_next_Γ_neg1
  gammaNeg1_eq_domain_g2_succ := _root_.DecoupledConsensusModel.Proofs.HealingSurface.gammaNeg1_eq_domain_g2_succ
  action_delta_le_early := _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.action_delta_le_early
  a_add_rounds := _root_.DecoupledConsensusModel.Proofs.HealingLemmas.a_add_rounds (V := V)
  deepest_clear_isSome_of_mem := _root_.DecoupledConsensusModel.Proofs.HealingSurface.deepest_clear_isSome_of_mem
  gradeView_toHealing_clock := _root_.DecoupledConsensusModel.Proofs.ModelProperties.gradeView_toHealing_clock
  onPhaseTick_phase_of_align := by
    simp only [Model.vocabulary, returns_pure, forall_eq, forall_const]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.onPhaseTick_phase_of_align
  q10_supports_of_not_opposes := _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.q10_supports_of_not_opposes
  opposes_congr := _root_.DecoupledConsensusModel.Proofs.NamedOutageHistory.GuardedHelpers.opposes_congr
  supports_congr := _root_.DecoupledConsensusModel.Proofs.NamedOutageHistory.GuardedHelpers.supports_congr
  alignRound_round := _root_.DecoupledConsensusModel.Sts.alignRound_round
  Sts_anchor_cases := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.anchor_cases
  anchor_compatible := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.anchor_compatible
  bodyReady_eq_false_of_find_none := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.bodyReady_eq_false_of_find_none
  bodyReady_of_confirmed_none := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.bodyReady_of_confirmed_none
  bodyReady_of_find := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.bodyReady_of_find
  bodyReady_of_head := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.bodyReady_of_head
  bodyReady_of_no_head := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.bodyReady_of_no_head
  bodyReady_parts := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.bodyReady_parts
  cleanFrom_intro := _root_.DecoupledConsensusModel.Sts.cleanFrom_intro
  clear_of_g0 := _root_.DecoupledConsensusModel.Sts.clear_of_g0
  clear_of_g0_some_none := _root_.DecoupledConsensusModel.Sts.clear_of_g0_some_none
  clear_of_g0_ne := _root_.DecoupledConsensusModel.Sts.clear_of_g0_ne
  compatible_of_clear := _root_.DecoupledConsensusModel.Sts.compatible_of_clear
  Sts_currentSGVote_of_Q2 := _root_.DecoupledConsensusModel.Sts.currentSGVote_of_Q2
  currentSGVote_of_none_none := _root_.DecoupledConsensusModel.Sts.currentSGVote_of_none_none
  exists_find_of_bodyReady := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.exists_find_of_bodyReady
  exists_rawInputs_of_mem_rawView := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.exists_rawInputs_of_mem_rawView
  frameGradeRead_anchor := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.frameGradeRead_anchor
  frameGradeRead_clear := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.frameGradeRead_clear
  key_eq_of_cleanFrom := _root_.DecoupledConsensusModel.Sts.key_eq_of_cleanFrom
  mem_interpretedInputs_iff := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.mem_interpretedInputs_iff
  opening_slot_add_mk := _root_.DecoupledConsensusModel.Sts.opening_slot_add_mk
  opening_slot_succ_mk := _root_.DecoupledConsensusModel.Sts.opening_slot_succ_mk
  opening_slot_zero_mk := _root_.DecoupledConsensusModel.Sts.opening_slot_zero_mk
  opposes_cases := _root_.DecoupledConsensusModel.Sts.opposes_cases
  opposes_of_late := _root_.DecoupledConsensusModel.Sts.opposes_of_late
  opposes_of_opposing := by
    intro gv F η r early late u B o ho h cov hcov Re hRe Rl hRl W hW
    obtain rfl := (returns_pure _ _).1 ho
    obtain rfl : cov = _ := funext fun k => funext fun b => (returns_pure _ _).1 (hcov k b)
    obtain rfl := (returns_pure _ _).1 hRe
    obtain rfl := (returns_pure _ _).1 hRl
    obtain rfl := (returns_pure _ _).1 hW
    exact _root_.DecoupledConsensusModel.Sts.opposes_of_opposing h
  opposing_of_Opposes := by
    intro gv F η r early late u B cov hcov Re hRe Rl hRl W hW hopp o ho
    obtain rfl : cov = _ := funext fun k => funext fun b => (returns_pure _ _).1 (hcov k b)
    obtain rfl := (returns_pure _ _).1 hRe
    obtain rfl := (returns_pure _ _).1 hRl
    obtain rfl := (returns_pure _ _).1 hW
    obtain rfl := (returns_pure _ _).1 ho
    exact _root_.DecoupledConsensusModel.Sts.opposing_of_Opposes gv F η r early late u B hopp
  positive_of_Supports := by
    intro gv F η r early late u B cov hcov Re hRe Rl hRl W hW hsup p hp
    obtain rfl : cov = _ := funext fun k => funext fun b => (returns_pure _ _).1 (hcov k b)
    obtain rfl := (returns_pure _ _).1 hRe
    obtain rfl := (returns_pure _ _).1 hRl
    obtain rfl := (returns_pure _ _).1 hW
    obtain rfl := (returns_pure _ _).1 hp
    exact _root_.DecoupledConsensusModel.Sts.positive_of_Supports gv F η r early late u B hsup
  rawInputs_mem_window := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.rawInputs_mem_window
  sgVote_compatible := _root_.DecoupledConsensusModel.Sts.sgVote_compatible
  supports_elim := _root_.DecoupledConsensusModel.Sts.supports_elim
  supports_intro := _root_.DecoupledConsensusModel.Sts.supports_intro
  supports_of_positive := by
    intro gv F η r early late u B p hp h cov hcov Re hRe Rl hRl W hW
    obtain rfl := (returns_pure _ _).1 hp
    obtain rfl : cov = _ := funext fun k => funext fun b => (returns_pure _ _).1 (hcov k b)
    obtain rfl := (returns_pure _ _).1 hRe
    obtain rfl := (returns_pure _ _).1 hRl
    obtain rfl := (returns_pure _ _).1 hW
    exact _root_.DecoupledConsensusModel.Sts.supports_of_positive h
  token_mem_readyView := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.token_mem_readyView
  deepest_clear_preceq := _root_.DecoupledConsensusModel.Proofs.Engine.deepest_clear_preceq
  early_g2_le_early_g0 := _root_.DecoupledConsensusModel.Proofs.GradeCutoffMono.early_g2_le_early_g0
  early_g2_le_early_g1 := _root_.DecoupledConsensusModel.Proofs.GradeCutoffMono.early_g2_le_early_g1
  early_le_late := _root_.DecoupledConsensusModel.Proofs.GradeCutoffMono.early_le_late
  rawInputs_mono := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.GradeCutoffMono.rawInputs_mono
  rawView_mono := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.GradeCutoffMono.rawView_mono
  readyView_mono := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.GradeCutoffMono.readyView_mono
  readyView_subset_rawView := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.GradeCutoffMono.readyView_subset_rawView
  ActionRound_round_of_opening_succ := _root_.DecoupledConsensusModel.Proofs.HealingLemmas.ActionRound.round_of_opening_succ
  exists_head_of_head_covers := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.HealingLemmas.exists_head_of_head_covers
  HealingLemmas_round_of_opening_succ := _root_.DecoupledConsensusModel.Proofs.HealingLemmas.round_of_opening_succ
  deepest_clear_eq_tip := _root_.DecoupledConsensusModel.Proofs.HealingSurface.deepest_clear_eq_tip
  lastInteriorSlot_before_opening := _root_.DecoupledConsensusModel.Proofs.HealingSurface.lastInteriorSlot_before_opening
  opening_slot_succ_eq := _root_.DecoupledConsensusModel.Proofs.HealingSurface.opening_slot_succ_eq
  phaseGrade_of_honestPositiveSupport := by
    intro E gv F Hon eta r ea la C pos hpos opp hopp hmajority hpositive hopposing g hg
    obtain rfl : pos = _ := funext fun v => (returns_pure _ _).1 (hpos v)
    obtain rfl : opp = _ := funext fun v => (returns_pure _ _).1 (hopp v)
    obtain rfl := (returns_pure _ _).1 hg
    exact _root_.DecoupledConsensusModel.Proofs.HealingSurface.phaseGrade_of_honestPositiveSupport E gv F Hon eta r ea la C hmajority hpositive hopposing
  round_of_eq_of_opening_succ_le_of_lt_next_opening := _root_.DecoupledConsensusModel.Proofs.HealingSurface.round_of_eq_of_opening_succ_le_of_lt_next_opening
  round_of_opening_slot_eq := _root_.DecoupledConsensusModel.Proofs.HealingSurface.round_of_opening_slot_eq
  round_of_opening_slot_eq_schedule := _root_.DecoupledConsensusModel.Proofs.HealingSurface.round_of_opening_slot_eq_schedule
  anchor_cases := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.anchor_cases
  anchor_eq_of_filtered_fg_root := by
    intro E hc st st' r g1 htree hroot x
    exact Iff.of_eq (congrArg (· ⇢ x) (congrArg pure
      (_root_.DecoupledConsensusModel.Proofs.ModelProperties.anchor_eq_of_filtered_fg_root E hc r g1 htree hroot)))
  currentSGVote_of_Q2 := _root_.DecoupledConsensusModel.Proofs.ModelProperties.currentSGVote_of_Q2
  ModelProperties_currentSGVote_of_deepest_clear := _root_.DecoupledConsensusModel.Proofs.ModelProperties.currentSGVote_of_deepest_clear
  currentSGVote_of_not_rawG2 := _root_.DecoupledConsensusModel.Proofs.ModelProperties.currentSGVote_of_not_rawG2
  currentSGVote_of_rawG2 := _root_.DecoupledConsensusModel.Proofs.ModelProperties.currentSGVote_of_rawG2
  deepest_clear_Preceq := _root_.DecoupledConsensusModel.Proofs.ModelProperties.deepest_clear_Preceq
  deepest_clear_floor_Preceq := _root_.DecoupledConsensusModel.Proofs.ModelProperties.deepest_clear_floor_Preceq
  deepest_clear_test := _root_.DecoupledConsensusModel.Proofs.ModelProperties.deepest_clear_test
  ModelProperties_exists_mem_T_preceq_of_gradeBool := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.exists_mem_T_preceq_of_gradeBool
  grade2Block_some := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.grade2Block_some
  grade2Block_eq_of_phases := by
    intro st f f' h0 h1 h2 o
    have hf : f = f' := by
      cases f; cases f'
      simp only [Model.Frame.g0, Model.Frame.g1, Model.Frame.g2, Model.vocabulary] at h0 h1 h2
      subst h0; subst h1; subst h2; rfl
    rw [hf]
  ModelProperties_gradeView_T := _root_.DecoupledConsensusModel.Proofs.ModelProperties.gradeView_T
  mem_filtered_of_grade2Block := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.mem_filtered_of_grade2Block
  ModelProperties_phaseResult_g2 := _root_.DecoupledConsensusModel.Proofs.ModelProperties.phaseResult_g2
  readFrame_g2 := _root_.DecoupledConsensusModel.Proofs.ModelProperties.readFrame_g2
  readFrame_phase := _root_.DecoupledConsensusModel.Proofs.ModelProperties.readFrame_phase
  runtime_Q2_mem := by
    simp only [Model.vocabulary, Model.Contract.read, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.NamedConfirmationMembership.runtime_Q2_mem
  activePrefix_covers := _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.activePrefix_covers
  early_le_domain := _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.early_le_domain
  NamedOutageClosure_opening_mono := _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.opening_mono
  q10_clip_preceq := _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.q10_clip_preceq
  q10_domain_g2_lt_domain_g1 := _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.q10_domain_g2_lt_domain_g1
  q10_early_g1_le_domain_g2 := _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.q10_early_g1_le_domain_g2
  q10_early_g1_public := _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.q10_early_g1_public
  q10_early_g2_le_early_g1 := _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.q10_early_g2_le_early_g1
  q10_early_le_late := _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.q10_early_le_late
  q10_freeze_of_graded := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.q10_freeze_of_graded
  q10_gradeBool_transport := by
    intro E gva gvb Fa Fb eta r ea la eb lb B Rea hRea Rla hRla Wa hWa Reb hReb Rlb hRlb Wb hWb cva hcva cvb hcvb
      hea_la hla_ra heb_lb hlb_rb heb_la hlb_la hrb_ra hkeep hcov ga hga hgrade gb hgb
    obtain rfl : Rea = _ := funext fun w => (returns_pure _ _).1 (hRea w)
    obtain rfl : Rla = _ := funext fun w => (returns_pure _ _).1 (hRla w)
    obtain rfl : Wa = _ := funext fun w => (returns_pure _ _).1 (hWa w)
    obtain rfl : Reb = _ := funext fun w => (returns_pure _ _).1 (hReb w)
    obtain rfl : Rlb = _ := funext fun w => (returns_pure _ _).1 (hRlb w)
    obtain rfl : Wb = _ := funext fun w => (returns_pure _ _).1 (hWb w)
    obtain rfl : cva = _ := funext fun k => (returns_pure _ _).1 (hcva k)
    obtain rfl : cvb = _ := funext fun k => (returns_pure _ _).1 (hcvb k)
    obtain rfl := (returns_pure _ _).1 hga
    obtain rfl := (returns_pure _ _).1 hgb
    exact _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.q10_gradeBool_transport E gva gvb Fa Fb eta r ea la eb lb B
      hea_la hla_ra heb_lb hlb_rb heb_la hlb_la hrb_ra hkeep hcov hgrade
  q10_graded_compatible := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.q10_graded_compatible
  q10_interpreted_cut := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.q10_interpreted_cut
  q10_late_g1_le_domain_g2 := _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.q10_late_g1_le_domain_g2
  q10_late_g1_public := _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.q10_late_g1_public
  q10_rawView_cut := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.q10_rawView_cut
  q10_readyView_cut := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.q10_readyView_cut
  q10_ready_subset_raw := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.q10_ready_subset_raw
  q10_retained_prefix := _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.q10_retained_prefix
  domain_g2_le_domain_g1 := _root_.DecoupledConsensusModel.Proofs.NamedOutageHistory.GuardedHelpers.domain_g2_le_domain_g1
  early_g1_le_domain_g1 := _root_.DecoupledConsensusModel.Proofs.NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
  early_g1_le_late_g1 := _root_.DecoupledConsensusModel.Proofs.NamedOutageHistory.GuardedHelpers.early_g1_le_late_g1
  early_g2_le_late_g2 := _root_.DecoupledConsensusModel.Proofs.NamedOutageHistory.GuardedHelpers.early_g2_le_late_g2
  early_g2_public := _root_.DecoupledConsensusModel.Proofs.NamedOutageHistory.GuardedHelpers.early_g2_public
  activePrefix_mem := _root_.DecoupledConsensusModel.Proofs.NamedProposalParent.activePrefix_mem
  lo_le_domain_of_window_start := _root_.DecoupledConsensusModel.Proofs.NamedRawRelay.lo_le_domain_of_window_start
  lo_le_early_g2_of_window_start := _root_.DecoupledConsensusModel.Proofs.NamedRawRelay.lo_le_early_g2_of_window_start
  opening_add_le_of_lt := _root_.DecoupledConsensusModel.Proofs.NamedRawRelay.opening_add_le_of_lt
  Q2_compatible := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.Q2_compatible
  activePrefix_preceq := _root_.DecoupledConsensusModel.Sts.activePrefix_preceq
  anchor_of_activePrefix := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.anchor_of_activePrefix
  clipCache_round := _root_.DecoupledConsensusModel.Sts.clipCache_round
  clipResult_some_map_clipGrade := _root_.DecoupledConsensusModel.Sts.clipResult_some_map_clipGrade
  compatible_of_gradeBool_phase := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.compatible_of_gradeBool_phase
  conditions_of_opposing := by
    intro gv F η r early late u B o ho h Re hRe Rl hRl W hW cov hcov
    obtain rfl := (returns_pure _ _).1 ho
    obtain rfl := (returns_pure _ _).1 hRe
    obtain rfl := (returns_pure _ _).1 hRl
    obtain rfl := (returns_pure _ _).1 hW
    obtain rfl : cov = _ := funext fun k => (returns_pure _ _).1 (hcov k)
    exact _root_.DecoupledConsensusModel.Sts.conditions_of_opposing gv F η r early late u B h
  conditions_of_positive := by
    intro gv F η r early late u B p hp h Re hRe Rl hRl W hW cov hcov
    obtain rfl := (returns_pure _ _).1 hp
    obtain rfl := (returns_pure _ _).1 hRe
    obtain rfl := (returns_pure _ _).1 hRl
    obtain rfl := (returns_pure _ _).1 hW
    obtain rfl : cov = _ := funext fun k => (returns_pure _ _).1 (hcov k)
    exact _root_.DecoupledConsensusModel.Sts.conditions_of_positive gv F η r early late u B h
  Sts_currentSGVote_of_deepest_clear := _root_.DecoupledConsensusModel.Sts.currentSGVote_of_deepest_clear
  domain_g2_le_domain_l67 := _root_.DecoupledConsensusModel.Sts.domain_g2_le_domain_l67
  domain_le_domain_g0 := _root_.DecoupledConsensusModel.Sts.domain_le_domain_g0
  early_add_two_delta_le_domain := _root_.DecoupledConsensusModel.Sts.early_add_two_delta_le_domain
  early_g2_lt_domain := _root_.DecoupledConsensusModel.Sts.early_g2_lt_domain
  exists_find_of_head_covers := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.exists_find_of_head_covers
  exists_find_of_localCovers := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.exists_find_of_localCovers
  Sts_exists_mem_T_preceq_of_gradeBool := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.exists_mem_T_preceq_of_gradeBool
  exists_round_of_slot := _root_.DecoupledConsensusModel.Sts.exists_round_of_slot
  exists_window_of_mem_rawInputs := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.exists_window_of_mem_rawInputs
  fgRoot_preceq_grade2Block := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.fgRoot_preceq_grade2Block
  find_of_mem_readyView := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.find_of_mem_readyView
  firstInterior_lt_nextOpening_l86e := _root_.DecoupledConsensusModel.Sts.firstInterior_lt_nextOpening_l86e
  frameSGCandidate_stableRoot := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.frameSGCandidate_stableRoot
  frameStableRoot_cases := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.frameStableRoot_cases
  frameStableRoot_exists := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.frameStableRoot_exists
  frameStableRoot_of_grade2Block := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.frameStableRoot_of_grade2Block
  get_head_with_eq_fork_choice := by
    intro contract E hc st votes support s R hR X
    obtain rfl := (returns_pure _ _).1 hR
    exact Iff.of_eq (congrArg (· ⇢ X) (congrArg pure
      (_root_.DecoupledConsensusModel.Sts.get_head_with_eq_fork_choice contract E hc st votes support s)))
  grade2Block_eq_of_filtered_eq := by
    intro st st' frame h x
    exact Iff.of_eq (congrArg (· ⇢ x) (congrArg pure
      (_root_.DecoupledConsensusModel.Sts.grade2Block_eq_of_filtered_eq frame h)))
  grade2Block_preceq_root := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.grade2Block_preceq_root
  gradeBool_eq_false_of_weight_le := by
    intro E gv F η r early late B pos hpos opp hopp h g hg
    obtain rfl : pos = _ := funext fun u => (returns_pure _ _).1 (hpos u)
    obtain rfl : opp = _ := funext fun u => (returns_pure _ _).1 (hopp u)
    obtain rfl := (returns_pure _ _).1 hg
    exact _root_.DecoupledConsensusModel.Sts.gradeBool_eq_false_of_weight_le E gv F η r early late B h
  gradeBool_of_freezeRoot_eq_some := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.gradeBool_of_freezeRoot_eq_some
  gradeBool_of_subsets := by
    intro E gv gv' F F' η r early late early' late' B B' opp' hopp' opp hopp'' pos hpos' pos' hpos'' hopp hpos g hg h g' hg'
    obtain rfl : opp' = _ := funext fun u => (returns_pure _ _).1 (hopp' u)
    obtain rfl : opp = _ := funext fun u => (returns_pure _ _).1 (hopp'' u)
    obtain rfl : pos = _ := funext fun u => (returns_pure _ _).1 (hpos' u)
    obtain rfl : pos' = _ := funext fun u => (returns_pure _ _).1 (hpos'' u)
    obtain rfl := (returns_pure _ _).1 hg
    obtain rfl := (returns_pure _ _).1 hg'
    exact _root_.DecoupledConsensusModel.Sts.gradeBool_of_subsets E hopp hpos h
  gradeBool_of_supporters := by
    intro E gv F η r early late B H pos hpos' W hW hel hpos hw g hg
    obtain rfl : pos = _ := funext fun u => (returns_pure _ _).1 (hpos' u)
    obtain rfl : W = _ := funext fun u => (returns_pure _ _).1 (hW u)
    obtain rfl := (returns_pure _ _).1 hg
    exact _root_.DecoupledConsensusModel.Sts.gradeBool_of_supporters E gv F η r early late B H hel hpos hw
  gradeBool_of_weight_lt := by
    intro E gv F η r early late B opp hopp pos hpos h g hg
    obtain rfl : opp = _ := funext fun u => (returns_pure _ _).1 (hopp u)
    obtain rfl : pos = _ := funext fun u => (returns_pure _ _).1 (hpos u)
    obtain rfl := (returns_pure _ _).1 hg
    exact _root_.DecoupledConsensusModel.Sts.gradeBool_of_weight_lt E gv F η r early late B h
  gradeBool_round_zero := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.gradeBool_round_zero
  Sts_gradeView_T := _root_.DecoupledConsensusModel.Sts.gradeView_T
  gradeView_sg_votes := _root_.DecoupledConsensusModel.Sts.gradeView_sg_votes
  gradeView_timestamp_block := _root_.DecoupledConsensusModel.Sts.gradeView_timestamp_block
  gradeView_timestamp_sg_vote := _root_.DecoupledConsensusModel.Sts.gradeView_timestamp_sg_vote
  gradeView_tree := _root_.DecoupledConsensusModel.Sts.gradeView_tree
  head_covers_of_find := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.head_covers_of_find
  late_le_domain := _root_.DecoupledConsensusModel.Sts.late_le_domain
  le_opening_round_of_sub_two := _root_.DecoupledConsensusModel.Sts.le_opening_round_of_sub_two
  le_opening_slot_far := _root_.DecoupledConsensusModel.Sts.le_opening_slot_far
  le_round_of_sub_two := _root_.DecoupledConsensusModel.Sts.le_round_of_sub_two
  lo_le_of_rawInputs_l53 := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.lo_le_of_rawInputs_l53
  localCovers_eq_true_iff := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.localCovers_eq_true_iff
  localCovers_none := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.localCovers_none
  localCovers_of_find := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.localCovers_of_find
  localCovers_some_iff_of_find := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.localCovers_some_iff_of_find
  lt_opening_slot_round_of_succ := _root_.DecoupledConsensusModel.Sts.lt_opening_slot_round_of_succ
  mem_T_of_freezeRoot_eq_some := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.mem_T_of_freezeRoot_eq_some
  mem_rawInputs_of_occurrenceBefore := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.mem_rawInputs_of_occurrenceBefore
  mem_rawInputs_of_stamp := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.mem_rawInputs_of_stamp
  mem_rawView_iff := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.mem_rawView_iff
  mem_readyView_iff := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.mem_readyView_iff
  mem_sg_votes_of_mem_rawInputs := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.mem_sg_votes_of_mem_rawInputs
  onPhaseTick_round := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.onPhaseTick_round
  openingSlot_pos_l58 := _root_.DecoupledConsensusModel.Sts.openingSlot_pos_l58
  openingSlot_pred_pos_l58 := _root_.DecoupledConsensusModel.Sts.openingSlot_pred_pos_l58
  openingSlots_l86f := _root_.DecoupledConsensusModel.Sts.openingSlots_l86f
  opening_eq_of_delta_eq := _root_.DecoupledConsensusModel.Sts.opening_eq_of_delta_eq
  Sts_opening_mono := _root_.DecoupledConsensusModel.Sts.opening_mono
  opening_slot_add := _root_.DecoupledConsensusModel.Sts.opening_slot_add
  opening_slot_le_of_le := _root_.DecoupledConsensusModel.Sts.opening_slot_le_of_le
  opening_slot_le_of_le_round_of := _root_.DecoupledConsensusModel.Sts.opening_slot_le_of_le_round_of
  opening_slot_mono := _root_.DecoupledConsensusModel.Sts.opening_slot_mono
  opening_slot_pos := _root_.DecoupledConsensusModel.Sts.opening_slot_pos
  opening_slot_pos_of_round_pos := _root_.DecoupledConsensusModel.Sts.opening_slot_pos_of_round_pos
  opening_slot_round_of_le_slot := _root_.DecoupledConsensusModel.Sts.opening_slot_round_of_le_slot
  opening_slot_succ := _root_.DecoupledConsensusModel.Sts.opening_slot_succ
  opening_slot_succ_le_l78 := _root_.DecoupledConsensusModel.Sts.opening_slot_succ_le_l78
  opening_slot_succ_lt_l78 := _root_.DecoupledConsensusModel.Sts.opening_slot_succ_lt_l78
  opening_slot_succ_lt_l88 := _root_.DecoupledConsensusModel.Sts.opening_slot_succ_lt_l88
  opposing_cases := by
    intro gv F η r early late u B o ho h Re hRe Rl hRl W hW cov hcov
    obtain rfl := (returns_pure _ _).1 ho
    obtain rfl := (returns_pure _ _).1 hRe
    obtain rfl := (returns_pure _ _).1 hRl
    obtain rfl := (returns_pure _ _).1 hW
    obtain rfl : cov = _ := funext fun k => (returns_pure _ _).1 (hcov k)
    exact _root_.DecoupledConsensusModel.Sts.opposing_cases gv F η r early late u B h
  opposing_false_of_positive := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.opposing_false_of_positive
  opposing_of_late_not_covers := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.opposing_of_late_not_covers
  opposing_of_positive_not_compatible := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.opposing_of_positive_not_compatible
  phaseResult_clipCache := _root_.DecoupledConsensusModel.Sts.phaseResult_clipCache
  phaseResult_clipCache_isSome := _root_.DecoupledConsensusModel.Sts.phaseResult_clipCache_isSome
  phaseResult_clipCache_some := _root_.DecoupledConsensusModel.Sts.phaseResult_clipCache_some
  phaseResult_g0 := _root_.DecoupledConsensusModel.Sts.phaseResult_g0
  phaseResult_g1 := _root_.DecoupledConsensusModel.Sts.phaseResult_g1
  Sts_phaseResult_g2 := _root_.DecoupledConsensusModel.Sts.phaseResult_g2
  phaseResult_onPhaseTick := by
    intro E hc st t c r₁ p root c' hc' h g hg
    obtain rfl := (returns_pure _ _).1 hc'
    obtain rfl : g = _ := funext fun B => (returns_pure _ _).1 (hg B)
    exact _root_.DecoupledConsensusModel.Sts.phaseResult_onPhaseTick E hc st t c h
  phaseResult_onPhaseTick_domain := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.phaseResult_onPhaseTick_domain
  phaseResult_onPhaseTick_domain_current := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    intro E hc st t _
    exact _root_.DecoupledConsensusModel.Sts.phaseResult_onPhaseTick_domain_current E hc st t
  phaseResult_onPhaseTick_domain_ne_none := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    intro E hc st t _
    exact _root_.DecoupledConsensusModel.Sts.phaseResult_onPhaseTick_domain_ne_none E hc st t
  phaseResult_onPhaseTick_kept := by
    simp only [Model.vocabulary, returns_pure, forall_eq, forall_const]
    exact _root_.DecoupledConsensusModel.Sts.phaseResult_onPhaseTick_kept
  phaseResult_onPhaseTick_some_cases := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.phaseResult_onPhaseTick_some_cases
  phaseResult_onPhaseTick_some_domain_or_kept := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.phaseResult_onPhaseTick_some_domain_or_kept
  plusTwo_slot_le_nextOpening_l53 := _root_.DecoupledConsensusModel.Sts.plusTwo_slot_le_nextOpening_l53
  positive_of_conditions := by
    intro gv F η r early late u B u₀ Re hRe hmem hlatest cov hcov' hcov W hW hclean Rl hRl hlater p hp
    obtain rfl := (returns_pure _ _).1 hRe
    obtain rfl : cov = _ := funext fun k => (returns_pure _ _).1 (hcov' k)
    obtain rfl := (returns_pure _ _).1 hW
    obtain rfl := (returns_pure _ _).1 hRl
    obtain rfl := (returns_pure _ _).1 hp
    exact _root_.DecoupledConsensusModel.Sts.positive_of_conditions gv F η r early late u B u₀ hmem hlatest hcov hclean hlater
  preceq_anchor_of_fgRoot := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.preceq_anchor_of_fgRoot
  preceq_anchor_of_g1 := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.preceq_anchor_of_g1
  preceq_clipGrade := _root_.DecoupledConsensusModel.Sts.preceq_clipGrade
  preceq_currentSGVote_of_cases := _root_.DecoupledConsensusModel.Sts.preceq_currentSGVote_of_cases
  preceq_deepest_clear := _root_.DecoupledConsensusModel.Sts.preceq_deepest_clear
  preceq_frameStableRoot := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.preceq_frameStableRoot
  preceq_freezeRoot := by
    intro E gv F η r early late X g hg hXT hX hcmp fr hfr
    obtain rfl : g = _ := funext fun B => (returns_pure _ _).1 (hg B)
    obtain rfl := (returns_pure _ _).1 hfr
    exact _root_.DecoupledConsensusModel.Sts.preceq_freezeRoot E gv F η r early late hXT hX hcmp
  preceq_grade2Block_of_g2 := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.preceq_grade2Block_of_g2
  preceq_of_activePrefix_eq_some := _root_.DecoupledConsensusModel.Sts.preceq_of_activePrefix_eq_some
  preceq_of_head_covers_of_find := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.preceq_of_head_covers_of_find
  preceq_of_localCovers_of_find := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.preceq_of_localCovers_of_find
  readFrame_g1_of_cache := _root_.DecoupledConsensusModel.Sts.readFrame_g1_of_cache
  readFrame_g1_provenance := _root_.DecoupledConsensusModel.Sts.readFrame_g1_provenance
  readFrame_g2_of_cache := _root_.DecoupledConsensusModel.Sts.readFrame_g2_of_cache
  readFrame_g2_provenance := _root_.DecoupledConsensusModel.Sts.readFrame_g2_provenance
  readFrame_phase_of_cache := _root_.DecoupledConsensusModel.Sts.readFrame_phase_of_cache
  readFrame_phase_provenance := _root_.DecoupledConsensusModel.Sts.readFrame_phase_provenance
  round_of_mono := _root_.DecoupledConsensusModel.Sts.round_of_mono
  round_of_mono_sts := _root_.DecoupledConsensusModel.Sts.round_of_mono_sts
  round_of_opening_slot_add := _root_.DecoupledConsensusModel.Sts.round_of_opening_slot_add
  round_of_sub_two_lt := _root_.DecoupledConsensusModel.Sts.round_of_sub_two_lt
  slot_round_bounds_l86e := _root_.DecoupledConsensusModel.Sts.slot_round_bounds_l86e
  token_key := _root_.DecoupledConsensusModel.Sts.token_key
  token_round := _root_.DecoupledConsensusModel.Sts.token_round
  val_index_of_mem_rawInputs := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.val_index_of_mem_rawInputs
  positive_nonempty := fun _ _ _ _ _ _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  opposing_nonempty := fun _ _ _ _ _ _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  rawView_nonempty := fun _ _ _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  readyView_nonempty := fun _ _ _ _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  head_covers_nonempty := fun _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  onPhaseTick_nonempty := by intro E hc st t c; exact ⟨_, (returns_pure _ _).2 rfl⟩
  rawInputs_nonempty := fun _ _ _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  read_nonempty := fun _ _ _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  anchor_nonempty := fun _ _ _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  grade2Block_nonempty := fun _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  gradeBool_nonempty := fun _ _ _ _ _ _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  bodyReady_nonempty := fun _ _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  early_g2_add_delta_le_early_g1 := fun S r => by
    have h1 := _root_.DecoupledConsensusModel.Sts.early_g2_eq_opening S r
    have h2 := _root_.DecoupledConsensusModel.Sts.early_g1_eq_opening S r
    show Protocol.early S.E S.hc r .g2 + S.E.Δ ≤ Protocol.early S.E S.hc r .g1
    linarith
  early_g1_add_delta_le_early_g0 := fun S r => by
    have h1 := _root_.DecoupledConsensusModel.Sts.early_g1_eq_opening S r
    have h2 := _root_.DecoupledConsensusModel.Sts.early_g0_eq_opening S r
    show Protocol.early S.E S.hc r .g1 + S.E.Δ ≤ Protocol.early S.E S.hc r .g0
    linarith
  late_g1_add_delta_le_late_g2 := fun S r => by
    have h1 := _root_.DecoupledConsensusModel.Sts.late_g1_eq_opening S r
    have h2 := _root_.DecoupledConsensusModel.Sts.late_g2_eq_opening S r
    show Protocol.late S.E S.hc r .g1 + S.E.Δ ≤ Protocol.late S.E S.hc r .g2
    linarith
  late_g0_add_delta_le_late_g1 := fun S r => by
    have h1 := _root_.DecoupledConsensusModel.Sts.late_g0_eq_opening S r
    have h2 := _root_.DecoupledConsensusModel.Sts.late_g1_eq_opening S r
    show Protocol.late S.E S.hc r .g0 + S.E.Δ ≤ Protocol.late S.E S.hc r .g1
    linarith
  opening_sub_five_delta_le_early_g2 := fun S r => by
    have h1 := _root_.DecoupledConsensusModel.Sts.early_g2_eq_opening S r
    show Protocol.opening S.E S.hc r - 5 * S.E.Δ ≤ Protocol.early S.E S.hc r .g2
    linarith
  late_g1_add_delta_lt_opening := fun S r => by
    have h1 := _root_.DecoupledConsensusModel.Sts.late_g1_eq_opening S r
    have h2 := S.E.Δ_pos
    show Protocol.late S.E S.hc r .g1 + S.E.Δ < Protocol.opening S.E S.hc r
    linarith
  opposes_of_raw := _root_.DecoupledConsensusModel.Sts.opposes_of_raw
  phaseResult_clipCache_ne_none := by intro F c r p h; show DecoupledConsensusModel.Protocol.phaseResult (DecoupledConsensusModel.Protocol.cacheAtRound (DecoupledConsensusModel.Protocol.clipCache F c) r) p ≠ none; rw [show DecoupledConsensusModel.Protocol.phaseResult (DecoupledConsensusModel.Protocol.cacheAtRound (DecoupledConsensusModel.Protocol.clipCache F c) r) p = DecoupledConsensusModel.Protocol.clipResult F (DecoupledConsensusModel.Protocol.phaseResult (DecoupledConsensusModel.Protocol.cacheAtRound c r) p) from (priv% Proofs.Vocabulary.Protocol.Grades.FrameCompleted DecoupledConsensusModel.Proofs.FrameCompleted.phase_clip) F c r p]; exact (priv% Proofs.Vocabulary.Protocol.Grades.FrameCompleted DecoupledConsensusModel.Proofs.FrameCompleted.clipResult_ne_none) F _ h
  round_of_slotOf_domain := by intro S r hr p; cases p with | g0 => exact Or.inl ((priv% Proofs.Vocabulary.Protocol.Grades.FrameCompleted DecoupledConsensusModel.Proofs.FrameCompleted.clockRound_domain_g0) S r).symm | g1 => exact Or.inl ((priv% Proofs.Vocabulary.Protocol.Grades.FrameCompleted DecoupledConsensusModel.Proofs.FrameCompleted.clockRound_domain_g1) S r).symm | g2 => exact Or.inr ((priv% Proofs.Vocabulary.Protocol.Grades.FrameCompleted DecoupledConsensusModel.Proofs.FrameCompleted.clockRound_domain_g2) S hr).symm
  publicTime_domain := fun S r hr p => (priv% Proofs.Vocabulary.Protocol.Grades.FrameCompleted DecoupledConsensusModel.Proofs.FrameCompleted.publicTime_domain) S hr p
  late_g0_public := fun S s hs =>
    (priv% Proofs.Vocabulary.Protocol.Store.RawSource
      DecoupledConsensusModel.Proofs.NamedRawSource.late_g0_public) S s hs
  q10_domain_g2_le_late_g2 := fun S r =>
    le_of_eq (DecoupledConsensusModel.Proofs.NamedOutageClosure.q10_late_g2_eq_domain_g2 S r).symm
  action_add_three_delta_le_late_succ := _root_.DecoupledConsensusModel.Sts.action_add_three_delta_le_late_succ
  phaseResult_onPhaseTick_ne_none_of_le := by intro E hc st t c r p hlo hhi h c' hc'; obtain rfl := (returns_pure _ _).1 hc'; have halign : DecoupledConsensusModel.Protocol.cacheAtRound (DecoupledConsensusModel.Protocol.alignRound (c : DecoupledConsensusModel.Protocol.Cache V) (hc.round_of (E.slotOf t))) r = DecoupledConsensusModel.Protocol.cacheAtRound c r := (priv% Proofs.Vocabulary.Protocol.Grades.FrameCompleted DecoupledConsensusModel.Proofs.FrameCompleted.cacheAtRound_align) c _ r hlo hhi; have h' : DecoupledConsensusModel.Protocol.phaseResult (DecoupledConsensusModel.Protocol.cacheAtRound (DecoupledConsensusModel.Protocol.alignRound c (hc.round_of (E.slotOf t))) r) p ≠ none := by { rw [halign]; exact h }; show DecoupledConsensusModel.Protocol.phaseResult (DecoupledConsensusModel.Protocol.cacheAtRound (DecoupledConsensusModel.Protocol.onPhaseTick E hc st t c) r) p ≠ none; rw [DecoupledConsensusModel.Proofs.ModelProperties.onPhaseTick_phase_of_align E hc st t c r p h']; exact (priv% Proofs.Vocabulary.Protocol.Grades.FrameCompleted DecoupledConsensusModel.Proofs.FrameCompleted.clipResult_ne_none) _ _ h'
  localCovers_nonempty := fun _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  interpretedInputs_nonempty := fun _ _ _ _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  freezeRoot_nonempty := fun _ _ _ _ _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  domain_g2_add_delta_le_domain_g1 := fun S r => by
    have h1 := _root_.DecoupledConsensusModel.Sts.domain_g2_eq_opening S r
    have h2 := _root_.DecoupledConsensusModel.Sts.domain_g1_eq_opening S r
    show Protocol.domain S.E S.hc r .g2 + S.E.Δ ≤ Protocol.domain S.E S.hc r .g1
    linarith
  domain_g1_add_delta_le_domain_g0 := fun S r => by show DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 + S.E.Δ ≤ DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0; unfold DecoupledConsensusModel.Protocol.domain DecoupledConsensusModel.Protocol.Phase.domainOffset; linarith
  Sts_domain_g1_eq_opening := fun S r => _root_.DecoupledConsensusModel.Sts.domain_g1_eq_opening S r
  exists_honest_max_positive_supporter_of_relativeGrade := by
    intro E hc gv F Hon r B p hwin g hg hgt
    obtain rfl := (returns_pure _ _).1 hg
    obtain ⟨v, hv, u, hu, head, h1, h2, h3, h4, h5, h6⟩ :=
      _root_.DecoupledConsensusModel.Proofs.HealingSurface.exists_honest_max_positive_supporter_of_relativeGrade
        E hc (hwin _ (fun _ => (returns_pure _ _).2 rfl)) hgt
    exact ⟨v, hv, _, (returns_pure _ _).2 rfl, u, hu, head, h1, h2, h3, h4,
      fun b hb => ((returns_pure _ _).1 hb).trans h5, h6⟩
  frameStableRoot_nonempty := by intro c E hc st r; exact ⟨_, (returns_pure _ _).2 rfl⟩
  domain_g0_eq_opening := fun S r => _root_.DecoupledConsensusModel.Sts.domain_g0_eq_opening S r
  allPhasesCutoff_eq_early_g0 := fun S q => _root_.DecoupledConsensusModel.Proofs.HealingSurface.allPhasesCutoff_eq_early_g0 S q

/-- `Model.vocabulary` satisfies `HandlersFacts`. -/
theorem Model.vocabulary_facts_handlers : HandlersFacts (Model.vocabulary (V := V)) where
  sgArrival_rows_data := _root_.DecoupledConsensusModel.Proofs.NamedOutageHistory.SGArrival.rows_data
  NamedAdmission_coherent_admit_rows := _root_.DecoupledConsensusModel.Proofs.NamedAdmission.coherent_admit_rows
  update_confirmation_with_live_confirmed_walk_or_fgRoot := by
    intro contract E hc st s tm htm R hR score hscore W hW st' hst'
    obtain rfl := (returns_pure _ _).1 htm
    obtain rfl := (returns_pure _ _).1 hR
    obtain rfl : score = _ := funext fun B => (returns_pure _ _).1 (hscore B)
    obtain rfl := (returns_pure _ _).1 hW
    obtain rfl := (returns_pure _ _).1 hst'
    by_cases h : _root_.DecoupledConsensusModel.Protocol.confEligible E st s
        (_root_.DecoupledConsensusModel.Protocol.confWalkWith contract E hc st s) = true
    · exact Or.inl ((_root_.DecoupledConsensusModel.Protocol.update_confirmation_with_live_confirmed
        contract E hc st s).trans (by rw [if_pos h]; rfl))
    · exact Or.inr ((_root_.DecoupledConsensusModel.Protocol.update_confirmation_with_live_confirmed
        contract E hc st s).trans (by rw [if_neg h]; rfl))
  treeSlotBounded_init := _root_.DecoupledConsensusModel.Sts.treeSlotBounded_init (V := V)
  blockStamps_init :=
    let h := _root_.DecoupledConsensusModel.Protocol.blockStamps_init (V := V)
    ⟨h.stamped, h.stored, h.bounded⟩
  finalizedViable_update_finality := fun st σ _B hB hσB hFB h => ((_root_.DecoupledConsensusModel.Proofs.finalizedViable_iff _).mp (_root_.DecoupledConsensusModel.Proofs.finalizedViable_update_finality st σ hB hσB hFB ((_root_.DecoupledConsensusModel.Proofs.finalizedViable_iff st).mpr (h.imp_right fun ⟨W, hW, hFW, hh⟩ => ⟨W, hW, _root_.DecoupledConsensusModel.Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hFW, hh⟩)))).imp_right fun ⟨W, hW, hFW, hh⟩ => ⟨W, hW, _root_.DecoupledConsensusModel.Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp hFW, hh⟩
  block_carried_before_deadline_or_equivocates := fun S st B u Γ hstamps hpre hpost hu hcommittee hfresh hfuture hclock => _root_.DecoupledConsensusModel.Proofs.Optimistic.block_carried_before_deadline_or_equivocates S st B u Γ ((Restated.Vocabulary.Protocol.PoolStamps_vocabulary_eq _).mpr hstamps) hpre hpost hu hcommittee hfresh hfuture hclock
  on_goldfish_vote_beforeCutoff_or_equivocates := fun st u Γ h => _root_.DecoupledConsensusModel.Protocol.on_goldfish_vote_beforeCutoff_or_equivocates st u Γ ((Restated.Vocabulary.Protocol.PoolStamps_vocabulary_eq st).mpr h)
  update_confirmation_with_live_confirmed_genuine_or_fgRoot := by
    intro contract E hc st s tm htm R hR score hscore W hW st' hst'
    obtain rfl := (returns_pure _ _).1 htm
    obtain rfl := (returns_pure _ _).1 hR
    obtain rfl : score = _ := funext fun B => (returns_pure _ _).1 (hscore B)
    obtain rfl := (returns_pure _ _).1 hW
    obtain rfl := (returns_pure _ _).1 hst'
    by_cases h : _root_.DecoupledConsensusModel.Protocol.confEligible E st s
        (_root_.DecoupledConsensusModel.Protocol.confWalkWith contract E hc st s) = true
    · exact Or.inl ⟨_, rfl, h⟩
    · exact Or.inr ((_root_.DecoupledConsensusModel.Protocol.update_confirmation_with_live_confirmed
        contract E hc st s).trans (by rw [if_neg h]; rfl))
  poolStamps_initial := (Restated.Vocabulary.Protocol.PoolStamps_vocabulary_eq _).mp _root_.DecoupledConsensusModel.Sts.poolStamps_initial
  ns_with_core_core := fun _ _ => rfl
  rawRelay_block_new_round_floor := by intro S st B a h0 h1; exact (priv% Proofs.Vocabulary.Protocol.Handlers.RawRelay DecoupledConsensusModel.Proofs.NamedRawRelay.block_new_round_floor) S st B a h0 h1
  rawRelay_new_row_round_floor := by intro hc st incoming a h0 h1; exact (priv% Proofs.Vocabulary.Protocol.Handlers.RawRelay DecoupledConsensusModel.Proofs.NamedRawRelay.new_row_round_floor) hc st incoming a h0 h1
  ns_with_core_sg_rows := fun _ _ _ _ _ => rfl
  new_body_guards := by intro E hc cfg st B; exact (priv% Proofs.Vocabulary.Protocol.Handlers.BlockAdmission DecoupledConsensusModel.Protocol.new_body_guards) E hc cfg st B
  ns_with_core_bodies := fun _ _ _ _ _ => rfl
  invariant_clock := _root_.DecoupledConsensusModel.Proofs.NamedConfirmationMembership.invariant_clock
  initial_core_justifier := (priv% Proofs.Vocabulary.Protocol.Handlers.JustificationCarrier DecoupledConsensusModel.Proofs.NamedJustificationCarrier.initial_core_justifier) (V := V)
  full_new_core_guard := fun hc st a hpre hpost => (priv% Proofs.Vocabulary.Protocol.Schedule.ReceiptCallsF1 DecoupledConsensusModel.Proofs.NamedReceiptCallsF1.full_new_core_guard) hc st a hpre hpost
  coreEq_on_goldfish_vote_checked := fun E st u => let h := _root_.DecoupledConsensusModel.Proofs.coreEq_on_goldfish_vote_checked E st u; ⟨h.σ_eq, h.F_eq, h.J_eq, h.h_j_eq⟩
  NamedAdmission_admitted_original_row := _root_.DecoupledConsensusModel.Proofs.NamedAdmission.admitted_original_row
  committeePools_on_tick_emit := fun S v before t out hout h => by obtain rfl := (Record.returns_pure _ out).1 hout; exact _root_.DecoupledConsensusModel.Protocol.CommitteePools.on_tick_emit S v before t h
  mem_gf_votes_on_goldfish_vote_checked := _root_.DecoupledConsensusModel.Sts.mem_gf_votes_on_goldfish_vote_checked
  process_block_core_gf_votes_upper := _root_.DecoupledConsensusModel.Sts.process_block_core_gf_votes_upper
  on_sg_vote_existing_row_stamp := _root_.DecoupledConsensusModel.Proofs.CarriedAdmission.on_sg_vote_existing_row_stamp
  live_confirmed_eq_with := by
    intro contract E hc st s Hon B tm htm hsup hvalid R hR hpre hpath st' hst'
    obtain rfl := (returns_pure _ _).1 htm
    obtain rfl := (returns_pure _ _).1 hR
    obtain rfl := (returns_pure _ _).1 hst'
    exact _root_.DecoupledConsensusModel.Protocol.live_confirmed_eq_with (V := V) contract E hc st s Hon B hsup hvalid hpre hpath
  setClock_core_sg_votes := _root_.DecoupledConsensusModel.Sts.setClock_core_sg_votes
  poolStep_on_goldfish_vote_checked := fun E st u h => let r := _root_.DecoupledConsensusModel.Protocol.poolStep_on_goldfish_vote_checked E st u ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩; ⟨⟨r.1.mem, r.1.stamp⟩, r.2.slot, r.2.stamped, r.2.pooled, r.2.bounded⟩
  mem_and_stamp_of_process := fun st u h1 h2 h3 h4 hfresh hslot hequiv => _root_.DecoupledConsensusModel.Protocol.mem_and_stamp_of_process st u ⟨h1, h2, h3, h4⟩ hfresh hslot hequiv
  sg_pool_subset_on_sg_vote := _root_.DecoupledConsensusModel.Proofs.HealingLemmas.sg_pool_subset_on_sg_vote
  commitBlock_core := fun before after B _ => _root_.DecoupledConsensusModel.Execution.commitBlock_core before after B
  on_block_checked_using_store_part := fun _ _ _ _ _ => rfl
  initial_core := _root_.DecoupledConsensusModel.Proofs.ModelProperties.initial_core (V := V)
  initial_core_σ := _root_.DecoupledConsensusModel.Proofs.ModelProperties.initial_core_σ (V := V)
  mem_commitBlock_bodies := fun _ _ _ {_before _after _B _D} _ _ hD =>
    _root_.DecoupledConsensusModel.Proofs.ModelProperties.mem_commitBlock_bodies hD
  mem_commitBlock_bodies_of_fresh := fun _ _ _ {_before _after _B} _ h =>
    _root_.DecoupledConsensusModel.Proofs.ModelProperties.mem_commitBlock_bodies_of_fresh h
  process_block_core_of_parent_mem := fun E hc cfg _ _ hp _ =>
    congrArg Protocol.NamedStore.core
      (_root_.DecoupledConsensusModel.Proofs.ModelProperties.process_block_core_of_parent_mem E hc cfg hp)
  process_block_core_bodies_eq_commit := fun E hc cfg st B hp => by
    have h := _root_.DecoupledConsensusModel.Proofs.ModelProperties.process_block_core_of_parent_mem E hc cfg hp
    show (Protocol.NamedStore.process_block_core E hc cfg st B).bodies =
      (Protocol.NamedStore.commitBlock st (Protocol.NamedStore.process_block_core E hc cfg st B).core B).bodies
    rw [h, _root_.DecoupledConsensusModel.Proofs.NamedStore.commit_core]
  update_finality_F_of_conditions := fun st σ _ =>
    _root_.DecoupledConsensusModel.Proofs.ModelProperties.update_finality_F_of_conditions st σ
  chainStateInTree_of_derived := by intros; trivial
  commit_core := fun before after B _ => _root_.DecoupledConsensusModel.Proofs.NamedStore.commit_core before after B
  commit_rows := fun _ _ _ before after B _ =>
    _root_.DecoupledConsensusModel.Proofs.NamedStore.commit_rows before after B
  mem_commitBlock_bodies_of_mem := fun _ _ _ {_before _after _B _D} _ hD =>
    _root_.DecoupledConsensusModel.Sts.mem_commitBlock_bodies_of_mem hD
  on_block_checked_using_eq_handle := _root_.DecoupledConsensusModel.Sts.on_block_checked_using_eq_handle
  on_block_with_of_new := _root_.DecoupledConsensusModel.Sts.on_block_with_of_new
  on_block_with_of_not_new := _root_.DecoupledConsensusModel.Sts.on_block_with_of_not_new
  on_sg_vote_of_rejected := _root_.DecoupledConsensusModel.Sts.on_sg_vote_of_rejected
  update_confirmation_with_keeps_stable_of_root_preceq := by
    simp only [Model.vocabulary, Model.Contract.stableRoot, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.update_confirmation_with_keeps_stable_of_root_preceq
  update_confirmation_with_latest_stable_of_root := by
    simp only [Model.vocabulary, Model.Contract.stableRoot, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.update_confirmation_with_latest_stable_of_root
  Execution_admit_row_core := _root_.DecoupledConsensusModel.Execution.admit_row_core
  on_goldfish_vote_checked_time := _root_.DecoupledConsensusModel.Execution.on_goldfish_vote_checked_time
  on_sg_vote_time := _root_.DecoupledConsensusModel.Execution.on_sg_vote_time
  update_finality_time := _root_.DecoupledConsensusModel.Execution.update_finality_time
  checked_existing := _root_.DecoupledConsensusModel.Proofs.BlockProcessingDefaults.checked_existing
  on_block_with_bodies_eq := _root_.DecoupledConsensusModel.Proofs.HealingSurface.on_block_with_bodies_eq
  update_finality_h_max_eq := _root_.DecoupledConsensusModel.Proofs.HealingSurface.update_finality_h_max_eq
  admit_carried_of_new := _root_.DecoupledConsensusModel.Proofs.ModelProperties.admit_carried_of_new
  carried_attestations_admissible_eq_true_iff := _root_.DecoupledConsensusModel.Proofs.ModelProperties.carried_attestations_admissible_eq_true_iff
  initial_bodies := _root_.DecoupledConsensusModel.Proofs.ModelProperties.initial_bodies (V := V)
  initial_core_F := _root_.DecoupledConsensusModel.Proofs.ModelProperties.initial_core_F (V := V)
  initial_core_J := _root_.DecoupledConsensusModel.Proofs.ModelProperties.initial_core_J (V := V)
  initial_core_T := _root_.DecoupledConsensusModel.Proofs.ModelProperties.initial_core_T (V := V)
  initial_core_h_j := _root_.DecoupledConsensusModel.Proofs.ModelProperties.initial_core_h_j (V := V)
  initial_core_h_j_lt_h_max := _root_.DecoupledConsensusModel.Proofs.ModelProperties.initial_core_h_j_lt_h_max (V := V)
  initial_core_h_max := _root_.DecoupledConsensusModel.Proofs.ModelProperties.initial_core_h_max (V := V)
  initial_core_not_mem_pool := _root_.DecoupledConsensusModel.Proofs.ModelProperties.initial_core_not_mem_pool
  initial_core_not_mem_sg_pool := _root_.DecoupledConsensusModel.Proofs.ModelProperties.initial_core_not_mem_sg_pool
  initial_core_s := _root_.DecoupledConsensusModel.Proofs.ModelProperties.initial_core_s (V := V)
  initial_core_t := _root_.DecoupledConsensusModel.Proofs.ModelProperties.initial_core_t (V := V)
  initial_core_σ_h_le_h_max := _root_.DecoupledConsensusModel.Proofs.ModelProperties.initial_core_σ_h_le_h_max
  initial_sg_rows := _root_.DecoupledConsensusModel.Proofs.ModelProperties.initial_sg_rows (V := V)
  on_block_checked_using_of_admissible := _root_.DecoupledConsensusModel.Proofs.ModelProperties.on_block_checked_using_of_admissible
  on_block_checked_using_of_not_admissible := _root_.DecoupledConsensusModel.Proofs.ModelProperties.on_block_checked_using_of_not_admissible
  on_block_using_of_rejected := _root_.DecoupledConsensusModel.Proofs.ModelProperties.on_block_using_of_rejected
  on_block_with_core_F := _root_.DecoupledConsensusModel.Proofs.ModelProperties.on_block_with_core_F
  on_goldfish_vote_checked_of_mem_committee := _root_.DecoupledConsensusModel.Proofs.ModelProperties.on_goldfish_vote_checked_of_mem_committee
  process_block_core_of_parent_not_mem := _root_.DecoupledConsensusModel.Proofs.ModelProperties.process_block_core_of_parent_not_mem
  ModelProperties_setClock_bodies := _root_.DecoupledConsensusModel.Proofs.ModelProperties.setClock_bodies
  ModelProperties_setClock_core_T := _root_.DecoupledConsensusModel.Proofs.ModelProperties.setClock_core_T
  ModelProperties_setClock_core_pool := _root_.DecoupledConsensusModel.Proofs.ModelProperties.setClock_core_pool
  ModelProperties_setClock_core_s := _root_.DecoupledConsensusModel.Proofs.ModelProperties.setClock_core_s
  ModelProperties_setClock_core_t := _root_.DecoupledConsensusModel.Proofs.ModelProperties.setClock_core_t
  ModelProperties_setClock_core_σ := _root_.DecoupledConsensusModel.Proofs.ModelProperties.setClock_core_σ
  ModelProperties_voter_filtered_block_tree_subset := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.voter_filtered_block_tree_subset
  NamedAdmission_admit_row_bodies := _root_.DecoupledConsensusModel.Proofs.NamedAdmission.admit_row_bodies
  NamedAdmission_admit_row_core := _root_.DecoupledConsensusModel.Proofs.NamedAdmission.admit_row_core
  admit_row_of_core_noop := _root_.DecoupledConsensusModel.Proofs.NamedAdmission.admit_row_of_core_noop
  admit_rows_core := _root_.DecoupledConsensusModel.Proofs.NamedAdmission.admit_rows_core
  sameCore_t := fun h => by cases (h : _ = _); rfl
  sameCore_s := fun h => by cases (h : _ = _); rfl
  sameCore_T := fun h => by cases (h : _ = _); rfl
  sameCore_timestamp_block := fun h => by cases (h : _ = _); rfl
  sameCore_timestamp_vote := fun h => by cases (h : _ = _); rfl
  sameCore_timestamp_sg_vote := fun h => by cases (h : _ = _); rfl
  sameCore_gf_votes := fun h => by cases (h : _ = _); rfl
  sameCore_F := fun h => by cases (h : _ = _); rfl
  sameCore_store_sg_pool := fun h => by cases (h : _ = _); rfl
  carried_row_prefix := _root_.DecoupledConsensusModel.Proofs.NamedAdmission.carried_row_prefix
  on_block_clock := _root_.DecoupledConsensusModel.Proofs.NamedAdmission.on_block_clock
  process_block_clock := _root_.DecoupledConsensusModel.Proofs.NamedAdmission.process_block_clock
  process_block_core_F := _root_.DecoupledConsensusModel.Proofs.NamedFinalityMonotone.process_block_core_F
  raw_eq_or_accepted := fun E st B build =>
    (_root_.DecoupledConsensusModel.Proofs.NamedJustificationBound.raw_eq_or_accepted E st B build).imp_right
      fun ⟨u, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ =>
        ⟨u, h1, h2, h3, h4, h5, h6, fun _ _ => trivial, h7, h8, h9⟩
  admit_row_mem_cases := _root_.DecoupledConsensusModel.Proofs.NamedReceiptCallsF1.admit_row_mem_cases
  admit_row_mem_mono := _root_.DecoupledConsensusModel.Proofs.NamedReceiptCallsF1.admit_row_mem_mono
  admit_rows_mem_mono := _root_.DecoupledConsensusModel.Proofs.NamedReceiptCallsF1.admit_rows_mem_mono
  admit_rows_new_marker := _root_.DecoupledConsensusModel.Proofs.NamedReceiptCallsF1.admit_rows_new_marker
  finalized_preceq_get_stable := _root_.DecoupledConsensusModel.Proofs.NestedOutputs.finalized_preceq_get_stable
  goldfish_vote_with_snd := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.Optimistic.goldfish_vote_with_snd
  on_goldfish_vote_checked_slot := _root_.DecoupledConsensusModel.Proofs.Optimistic.on_goldfish_vote_checked_slot
  on_sg_vote_slot := _root_.DecoupledConsensusModel.Proofs.Optimistic.on_sg_vote_slot
  process_block_core_sg_votes := _root_.DecoupledConsensusModel.Proofs.Optimistic.process_block_core_sg_votes
  on_goldfish_vote_checked_F := _root_.DecoupledConsensusModel.Proofs.on_goldfish_vote_checked_F
  on_goldfish_vote_checked_T := _root_.DecoupledConsensusModel.Proofs.on_goldfish_vote_checked_T
  on_goldfish_vote_checked_h_max := _root_.DecoupledConsensusModel.Proofs.on_goldfish_vote_checked_h_max
  on_sg_vote_F := _root_.DecoupledConsensusModel.Proofs.on_sg_vote_F
  on_sg_vote_T := _root_.DecoupledConsensusModel.Proofs.on_sg_vote_T
  on_sg_vote_h_max := _root_.DecoupledConsensusModel.Proofs.on_sg_vote_h_max
  update_finality_F := _root_.DecoupledConsensusModel.Proofs.update_finality_F
  update_finality_T := _root_.DecoupledConsensusModel.Proofs.update_finality_T
  update_finality_h_max_mono := _root_.DecoupledConsensusModel.Proofs.update_finality_h_max_mono
  update_finality_heightId := _root_.DecoupledConsensusModel.Proofs.update_finality_heightId
  update_finality_preceq := _root_.DecoupledConsensusModel.Proofs.update_finality_preceq
  update_finality_σ := _root_.DecoupledConsensusModel.Proofs.update_finality_σ
  Protocol_admit_row_bodies := _root_.DecoupledConsensusModel.Protocol.admit_row_bodies
  admit_row_core_T := _root_.DecoupledConsensusModel.Protocol.admit_row_core_T
  admit_rows_bodies_and_core_T := _root_.DecoupledConsensusModel.Protocol.admit_rows_bodies_and_core_T
  goldfish_vote_with_T := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Protocol.goldfish_vote_with_T
  on_block_with_F := _root_.DecoupledConsensusModel.Protocol.on_block_with_F
  on_block_with_new_body := _root_.DecoupledConsensusModel.Protocol.on_block_with_new_body
  on_goldfish_vote_checked_timestamp_block := _root_.DecoupledConsensusModel.Protocol.on_goldfish_vote_checked_timestamp_block
  on_sg_vote_gf_votes := _root_.DecoupledConsensusModel.Protocol.on_sg_vote_gf_votes
  on_sg_vote_timestamp_block := _root_.DecoupledConsensusModel.Protocol.on_sg_vote_timestamp_block
  on_sg_vote_timestamp_vote := _root_.DecoupledConsensusModel.Protocol.on_sg_vote_timestamp_vote
  update_finality_gf_votes := _root_.DecoupledConsensusModel.Protocol.update_finality_gf_votes
  update_finality_timestamp_block := _root_.DecoupledConsensusModel.Protocol.update_finality_timestamp_block
  update_finality_timestamp_vote := _root_.DecoupledConsensusModel.Protocol.update_finality_timestamp_vote
  advance_confirmed_eq_or_not_preceq := _root_.DecoupledConsensusModel.Sts.advance_confirmed_eq_or_not_preceq
  advance_confirmed_values := _root_.DecoupledConsensusModel.Sts.advance_confirmed_values
  floor_on_stable_cases := _root_.DecoupledConsensusModel.Sts.floor_on_stable_cases
  floor_on_stable_stable_preceq := _root_.DecoupledConsensusModel.Sts.floor_on_stable_stable_preceq
  floor_on_stable_values := _root_.DecoupledConsensusModel.Sts.floor_on_stable_values
  get_confirmed_eq_or := _root_.DecoupledConsensusModel.Sts.get_confirmed_eq_or
  get_confirmed_preceq_of_fields := _root_.DecoupledConsensusModel.Sts.get_confirmed_preceq_of_fields
  get_confirmed_upper := _root_.DecoupledConsensusModel.Sts.get_confirmed_upper
  get_confirmed_values := _root_.DecoupledConsensusModel.Sts.get_confirmed_values
  get_head_in_tree_with_eq_fork_choice := by
    intro contract E hc st tree votes support s R hR X
    obtain rfl := (returns_pure _ _).1 hR
    exact Iff.of_eq (congrArg (· ⇢ X) (congrArg pure
      (_root_.DecoupledConsensusModel.Sts.get_head_in_tree_with_eq_fork_choice contract E hc st tree votes support s)))
  get_head_in_tree_with_eq_layer := by
    intro contract E hc st tree votes support k X
    exact Iff.of_eq (congrArg (· ⇢ X) (congrArg pure
      (_root_.DecoupledConsensusModel.Sts.get_head_in_tree_with_eq_layer contract E hc st tree votes support k)))
  get_sg_root_with_preceq_get_head_in_tree_with_store := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.get_sg_root_with_preceq_get_head_in_tree_with_store
  get_stable_eq_or := _root_.DecoupledConsensusModel.Sts.get_stable_eq_or
  get_stable_preceq_of_fields := _root_.DecoupledConsensusModel.Sts.get_stable_preceq_of_fields
  get_stable_upper := _root_.DecoupledConsensusModel.Sts.get_stable_upper
  mem_T_on_block_using := fun E st B build hslot hnew hpar hfin hprop hpslot _ =>
    _root_.DecoupledConsensusModel.Sts.mem_T_on_block_using E st B build hslot hnew hpar hfin hprop
      hpslot
  mem_on_block_with_bodies_of_mem_core := _root_.DecoupledConsensusModel.Sts.mem_on_block_with_bodies_of_mem_core
  mem_on_sg_vote_sg_pool_of_not := _root_.DecoupledConsensusModel.Sts.mem_on_sg_vote_sg_pool_of_not
  mem_round_votes_iff := _root_.DecoupledConsensusModel.Sts.mem_round_votes_iff
  mem_voter_filtered_block_tree_of_parts := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.mem_voter_filtered_block_tree_of_parts
  namedStore_initial_h_max := _root_.DecoupledConsensusModel.Sts.namedStore_initial_h_max (V := V)
  on_goldfish_vote_checked_of_mem := _root_.DecoupledConsensusModel.Sts.on_goldfish_vote_checked_of_mem
  on_sg_vote_timestamp_of_admitted := _root_.DecoupledConsensusModel.Sts.on_sg_vote_timestamp_of_admitted
  preceq_advance_confirmed_candidate := _root_.DecoupledConsensusModel.Sts.preceq_advance_confirmed_candidate
  preceq_floor_on_stable_of_compatible := _root_.DecoupledConsensusModel.Sts.preceq_floor_on_stable_of_compatible
  preceq_get_stable_of_record := _root_.DecoupledConsensusModel.Sts.preceq_get_stable_of_record
  process_block_core_sg_rows_eq := _root_.DecoupledConsensusModel.Sts.process_block_core_sg_rows_eq
  Sts_setClock_bodies := _root_.DecoupledConsensusModel.Sts.setClock_bodies
  setClock_core_F := _root_.DecoupledConsensusModel.Sts.setClock_core_F
  setClock_core_J := _root_.DecoupledConsensusModel.Sts.setClock_core_J
  Sts_setClock_core_T := _root_.DecoupledConsensusModel.Sts.setClock_core_T
  setClock_core_gf_votes := _root_.DecoupledConsensusModel.Sts.setClock_core_gf_votes
  setClock_core_h_max := _root_.DecoupledConsensusModel.Sts.setClock_core_h_max
  setClock_core_latest_confirmed := _root_.DecoupledConsensusModel.Sts.setClock_core_latest_confirmed
  setClock_core_latest_stable := _root_.DecoupledConsensusModel.Sts.setClock_core_latest_stable
  Sts_setClock_core_pool := _root_.DecoupledConsensusModel.Sts.setClock_core_pool
  Sts_setClock_core_s := _root_.DecoupledConsensusModel.Sts.setClock_core_s
  Sts_setClock_core_t := _root_.DecoupledConsensusModel.Sts.setClock_core_t
  setClock_core_timestamp_block := _root_.DecoupledConsensusModel.Sts.setClock_core_timestamp_block
  setClock_core_timestamp_vote := _root_.DecoupledConsensusModel.Sts.setClock_core_timestamp_vote
  Sts_setClock_core_σ := _root_.DecoupledConsensusModel.Sts.setClock_core_σ
  setClock_gradeView := _root_.DecoupledConsensusModel.Sts.setClock_gradeView
  setClock_sg_rows := _root_.DecoupledConsensusModel.Sts.setClock_sg_rows
  setClock_toHealing_F := _root_.DecoupledConsensusModel.Sts.setClock_toHealing_F
  setClock_toHealing_J := _root_.DecoupledConsensusModel.Sts.setClock_toHealing_J
  setClock_toHealing_T := _root_.DecoupledConsensusModel.Sts.setClock_toHealing_T
  setClock_toHealing_h_j := _root_.DecoupledConsensusModel.Sts.setClock_toHealing_h_j
  setClock_toHealing_h_max := _root_.DecoupledConsensusModel.Sts.setClock_toHealing_h_max
  setClock_toHealing_σ := _root_.DecoupledConsensusModel.Sts.setClock_toHealing_σ
  update_confirmation_with_filtered := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.update_confirmation_with_filtered
  update_confirmation_with_toHealing_F := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.update_confirmation_with_toHealing_F
  voter_filtered_block_tree_cases := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.voter_filtered_block_tree_cases
  Sts_voter_filtered_block_tree_subset := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.voter_filtered_block_tree_subset
  setClock_core_eq_store_with_t_s := by intro E st t; show (Protocol.NamedStore.setClock E st t).core = _; unfold Protocol.NamedStore.setClock; rfl
  coherent_clock := _root_.DecoupledConsensusModel.Proofs.NamedStore.coherent_clock
  update_confirmation_with_live_confirmed_of_eligible := by
    intro contract E hc st s tm htm R hR score hscore W hW h st' hst'
    obtain rfl := (returns_pure _ _).1 htm
    obtain rfl := (returns_pure _ _).1 hR
    obtain rfl : score = _ := funext fun B => (returns_pure _ _).1 (hscore B)
    obtain rfl := (returns_pure _ _).1 hW
    obtain rfl := (returns_pure _ _).1 hst'
    have h' : _root_.DecoupledConsensusModel.Protocol.confEligible E st s
        (_root_.DecoupledConsensusModel.Protocol.confWalkWith contract E hc st s) = true := h
    exact (_root_.DecoupledConsensusModel.Protocol.update_confirmation_with_live_confirmed
      contract E hc st s).trans (if_pos h')
  update_confirmation_with_latest_confirmed_cases := by
    intro contract E hc st s tm htm R hR score hscore W hW st' hst'
    obtain rfl := (returns_pure _ _).1 htm
    obtain rfl := (returns_pure _ _).1 hR
    obtain rfl : score = _ := funext fun B => (returns_pure _ _).1 (hscore B)
    obtain rfl := (returns_pure _ _).1 hW
    obtain rfl := (returns_pure _ _).1 hst'
    obtain ⟨cand, h1, h2⟩ :=
      _root_.DecoupledConsensusModel.Sts.update_confirmation_with_latest_confirmed_cases contract E hc st s
    refine ⟨cand, h1, ?_⟩
    rcases h2 with h | ⟨hel, h⟩ | ⟨select, G, hmode, hsel, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hel, h⟩)
    · refine Or.inr (Or.inr ⟨G, ?_, h⟩)
      simp only [Model.vocabulary, Model.Contract.confirmationSG, hmode, returns_pure]
      exact hsel.symm
  update_confirmation_with_latest_confirmed_of_eligible := by
    intro contract E hc st s tm htm R hR score hscore W hW h st' hst'
    obtain rfl := (returns_pure _ _).1 htm
    obtain rfl := (returns_pure _ _).1 hR
    obtain rfl : score = _ := funext fun B => (returns_pure _ _).1 (hscore B)
    obtain rfl := (returns_pure _ _).1 hW
    obtain rfl := (returns_pure _ _).1 hst'
    have h' : _root_.DecoupledConsensusModel.Protocol.confEligible E st s
        (_root_.DecoupledConsensusModel.Protocol.confWalkWith contract E hc st s) = true := h
    exact _root_.DecoupledConsensusModel.Sts.update_confirmation_with_latest_confirmed_of_eligible
      contract E hc st s h'

/-- `Model.vocabulary` satisfies `DutiesFacts`. -/
theorem Model.vocabulary_facts_duties : DutiesFacts (Model.vocabulary (V := V)) where
  insertsAt_named_propose := by
    intro E c contract hc cfg nd st D hD
    obtain rfl := (returns_pure _ _).1 hD
    exact (DecoupledConsensusModel.Sts.Restated.InsertsAt_vocabulary_eq _ _ _ _).1 (_root_.DecoupledConsensusModel.Sts.insertsAt_named_propose E c contract hc cfg nd st)
  insertsAt_named_vote := by
    intro E c contract hc nd st D hD
    obtain rfl := (returns_pure _ _).1 hD
    exact (DecoupledConsensusModel.Sts.Restated.InsertsAt_vocabulary_eq _ _ _ _).1 (_root_.DecoupledConsensusModel.Sts.insertsAt_named_vote E c contract hc nd st)
  insertsAt_named_confirmation := by
    intro E c contract hc st s D hD
    obtain rfl := (returns_pure _ _).1 hD
    exact (DecoupledConsensusModel.Sts.Restated.InsertsAt_vocabulary_eq _ _ _ _).1 (_root_.DecoupledConsensusModel.Sts.insertsAt_named_confirmation E c contract hc st s)
  insertsAt_named_attest := by
    intro E c contract hc nd st record D hD
    obtain rfl := (returns_pure _ _).1 hD
    exact (DecoupledConsensusModel.Sts.Restated.InsertsAt_vocabulary_eq _ _ _ _).1 (_root_.DecoupledConsensusModel.Sts.insertsAt_named_attest E c contract hc nd st record)
  update_confirmation_with_σ := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.update_confirmation_with_σ
  update_confirmation_with_live_confirmed_mem_filtered := by
    intro contract E hc st s hroot R hR hanchor st' hst'
    obtain rfl := (returns_pure _ _).1 hR
    obtain rfl := (returns_pure _ _).1 hst'
    show (_root_.DecoupledConsensusModel.Protocol.update_confirmation_with contract E hc st s).live_confirmed ∈ _
    rw [_root_.DecoupledConsensusModel.Protocol.update_confirmation_with_live_confirmed]
    split
    · exact _root_.DecoupledConsensusModel.Proofs.Records.ghost_mem_of _ _ hanchor (Finset.Subset.refl _)
    · exact hroot
  mem_select_poolAndCarried := by
    intro hc st a L hL h C hC
    obtain rfl := (returns_pure _ _).1 hL
    obtain rfl := (returns_pure _ _).1 hC
    rw [_root_.DecoupledConsensusModel.Proofs.NamedProposalRows.selected_source_exact] at h
    exact List.mem_append.1 h
  namedDuties_goldfish_vote_with_fst_core_F := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.namedDuties_goldfish_vote_with_fst_core_F
  proposal_with_gradeContract_isSome := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.proposal_with_gradeContract_isSome
  selected_row_round_le := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.HealingSurface.selected_row_round_le
  attestation_input_head_gradeContract := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.attestation_input_head_gradeContract
  frame_fg_source_mem := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact fun S cache st r hinv _ hs =>
      _root_.DecoupledConsensusModel.Proofs.NamedActionSources.frame_fg_source_mem S cache st r hinv hs
  round_action_names_source := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.NamedActions.round_action_names_source
  invariant_update_gradeContract := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.invariant_update_gradeContract
  round_action_finality_pair_eq := by
    intro contract E hc nd st record A hA res hres H hH
    have e1 : res = Protocol.resolved st.T := funext fun u => (returns_pure _ _).1 (hres u)
    subst e1
    obtain rfl := (returns_pure _ _).1 hA
    obtain rfl := (returns_pure _ _).1 hH
    exact _root_.DecoupledConsensusModel.Proofs.HealingSurface.round_action_finality_pair_eq contract E hc nd st record
  namedRoundAction_finality_pair_of_record_guard := by
    intro contract E hc nd st record h J htarget htimeout hlock A hA res hres H hH hhj hJ hF
    have e1 : res = Protocol.resolved st.T := funext fun u => (returns_pure _ _).1 (hres u)
    subst e1
    obtain rfl := (returns_pure _ _).1 hA
    obtain rfl := (returns_pure _ _).1 hH
    exact _root_.DecoupledConsensusModel.Proofs.HealingSurface.namedRoundAction_finality_pair_of_record_guard
      contract E hc nd st record htarget htimeout hlock hhj hJ hF
  named_round_action_height_pair := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.HealingSurface.named_round_action_height_pair
  proposal_payload := by
    simp only [Model.vocabulary, returns_pure, forall_eq, forall_const]
    exact _root_.DecoupledConsensusModel.Proofs.NamedActions.proposal_payload
  proposal_with_parent? := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.proposal_with_parent?
  with_attestation_input_id_confirmed := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.with_attestation_input_id_confirmed
  with_attestation_input_id_fields := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.with_attestation_input_id_fields
  with_proposal_input_id_gf_support_votes := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.with_proposal_input_id_gf_support_votes
  with_proposal_input_id_gf_votes := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.with_proposal_input_id_gf_votes
  with_proposal_input_id_parent := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.with_proposal_input_id_parent
  with_proposal_input_id_proposer := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.with_proposal_input_id_proposer
  with_proposal_input_id_slot := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.with_proposal_input_id_slot
  with_proposal_input_id_root := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    intro _ _ _ _ _
    unfold _root_.DecoupledConsensusModel.Protocol.with_proposal_input
    rfl
  mem_carried_rows := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.NamedProposalRows.mem_carried_rows
  mem_proposalRows := _root_.DecoupledConsensusModel.Proofs.NamedProposalRows.mem_proposalRows
  mem_proposalRows_of_unique := _root_.DecoupledConsensusModel.Proofs.NamedProposalRows.mem_proposalRows_of_unique
  ordered_bodies_mem := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.NamedProposalRows.ordered_bodies_mem
  mem_processedRows_of_mem_poolRows := _root_.DecoupledConsensusModel.Sts.mem_processedRows_of_mem_poolRows
  namedDuties_attest_with_confirmed := by
    simp only [Model.vocabulary, Model.Contract.read, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.namedDuties_attest_with_confirmed
  round_action_with_height_pair_input := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.round_action_with_height_pair_input
  named_attest_clock := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Execution.named_attest_clock
  named_confirmation_clock := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Execution.named_confirmation_clock
  named_propose_clock := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Execution.named_propose_clock
  named_vote_clock := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Execution.named_vote_clock
  propose_block_with_slot := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.HealingSurface.propose_block_with_slot
  attest_with_row := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.attest_with_row
  fg_source_with_some_of_deepest_clear := by
    simp only [Model.vocabulary, Model.Contract.read, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.fg_source_with_some_of_deepest_clear
  fg_source_with_some_of_deepest_clear_none := by
    simp only [Model.vocabulary, Model.Contract.read, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.fg_source_with_some_of_deepest_clear_none
  get_sg_vote_with_gradeContract_grade2 := by
    simp only [Model.vocabulary, Model.Contract.read, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.get_sg_vote_with_gradeContract_grade2
  get_sg_vote_with_gradeContract_of_deepest_clear := by
    simp only [Model.vocabulary, Model.Contract.read, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.get_sg_vote_with_gradeContract_of_deepest_clear
  grade2_block_with_eq_read_Q2 := by
    simp only [Model.vocabulary, Model.Contract.read, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.grade2_block_with_eq_read_Q2
  inWindow_eq_true_iff := _root_.DecoupledConsensusModel.Proofs.ModelProperties.inWindow_eq_true_iff
  named_update_confirmation_with_bodies := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.named_update_confirmation_with_bodies
  named_update_confirmation_with_core := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.named_update_confirmation_with_core
  ModelProperties_proposal_with_slot := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.proposal_with_slot
  propose_block_with_eq_of_snd := by
    simp only [Model.vocabulary, returns_pure, forall_eq, forall_const]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.propose_block_with_eq_of_snd
  propose_block_with_fst_of_none := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.propose_block_with_fst_of_none
  propose_block_with_fst_of_some := by
    simp only [Model.vocabulary, returns_pure, forall_eq, forall_const]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.propose_block_with_fst_of_some
  read_Q2_isSome_of_fg_source_with_grade2 := by
    simp only [Model.vocabulary, Model.Contract.read, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.read_Q2_isSome_of_fg_source_with_grade2
  round_action_with_confirmed := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.round_action_with_confirmed
  round_action_with_round := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.round_action_with_round
  round_action_with_val_index := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.round_action_with_val_index
  update_confirmation_with_F := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.update_confirmation_with_F
  update_confirmation_with_T := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.update_confirmation_with_T
  update_confirmation_with_pool := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.update_confirmation_with_pool
  update_confirmation_with_s := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.update_confirmation_with_s
  update_confirmation_with_toHealing_fg_root := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.update_confirmation_with_toHealing_fg_root
  update_confirmation_with_toHealing_filtered := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.update_confirmation_with_toHealing_filtered
  update_confirmation_with_toHealing_gradeView := by
    simp only [Model.vocabulary, returns_pure, forall_eq, forall_const]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.update_confirmation_with_toHealing_gradeView
  confirmation_metadata := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.NamedDuties.confirmation_metadata
  goldfish_vote_metadata := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.NamedDuties.goldfish_vote_metadata
  propose_none := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.NamedDuties.propose_none
  goldfish_vote_with_sg_votes := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.Optimistic.goldfish_vote_with_sg_votes
  proposal_with_gf_votes := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.Optimistic.proposal_with_gf_votes
  Optimistic_proposal_with_slot := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.Optimistic.proposal_with_slot
  propose_block_with_F := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Protocol.propose_block_with_F
  Sts_attest_with_live_confirmed := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.attest_with_live_confirmed
  attest_with_records := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.attest_with_records
  exists_sg_rows_of_mem_processedRows := _root_.DecoupledConsensusModel.Sts.exists_sg_rows_of_mem_processedRows
  fg_source_cases := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.fg_source_cases
  fg_source_with_some := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.fg_source_with_some
  inWindow_iff := _root_.DecoupledConsensusModel.Sts.inWindow_iff
  mem_select_of_processed_inWindow := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.mem_select_of_processed_inWindow
  namedDuties_attest_with_fst := by
    simp only [Model.vocabulary, returns_pure, forall_eq, forall_const]
    exact _root_.DecoupledConsensusModel.Sts.namedDuties_attest_with_fst
  namedDuties_attest_with_fst_eq_round_action := by
    simp only [Model.vocabulary, returns_pure, forall_eq, forall_const]
    exact _root_.DecoupledConsensusModel.Sts.namedDuties_attest_with_fst_eq_round_action
  namedDuties_goldfish_vote_with_fst_core := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.namedDuties_goldfish_vote_with_fst_core
  namedDuties_goldfish_vote_with_snd := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.namedDuties_goldfish_vote_with_snd
  namedDuties_update_confirmation_with_bodies := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.namedDuties_update_confirmation_with_bodies
  namedDuties_update_confirmation_with_core := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.namedDuties_update_confirmation_with_core
  proposal_with_carried_admissible_inclG2 := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.proposal_with_carried_admissible_inclG2
  proposal_with_eq_of_propose_block_with_snd := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.proposal_with_eq_of_propose_block_with_snd
  proposal_with_gf_support_subset := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.proposal_with_gf_support_subset
  proposal_with_of_propose_block_with := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.proposal_with_of_propose_block_with
  proposal_with_support_subset := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.proposal_with_support_subset
  propose_block_with_snd_of_some := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.propose_block_with_snd_of_some
  proposer_of_propose_block_with := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.proposer_of_propose_block_with
  round_action_with_height_pair_of_Q2_none := by
    simp only [Model.vocabulary, Model.Contract.read, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.round_action_with_height_pair_of_Q2_none
  update_confirmation_with_gf_votes := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.update_confirmation_with_gf_votes
  update_confirmation_with_t := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.update_confirmation_with_t
  update_confirmation_with_timestamp_vote := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.update_confirmation_with_timestamp_vote
  update_confirmation_with_toHealing_J := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.update_confirmation_with_toHealing_J
  update_confirmation_with_toHealing_h_j := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.update_confirmation_with_toHealing_h_j
  update_confirmation_with_toHealing_h_max := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.update_confirmation_with_toHealing_h_max
  update_confirmation_with_toHealing_s := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.update_confirmation_with_toHealing_s
  goldfish_vote_with_nonempty := by intro gc E hc nd st; exact ⟨_, (returns_pure _ _).2 rfl⟩
  propose_block_with_nonempty := by
    intro S v n t out hout hs ht hv hawake c hc _ _
    exact ⟨_, (returns_pure _ _).2 rfl⟩
  round_action_with_nonempty := fun _ _ _ _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  with_attestation_input_nonempty := fun _ _ _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  attest_with_nonempty := by intro contract E hc nd st record; exact ⟨_, (returns_pure _ _).2 rfl⟩
  grade2_block_with_nonempty := by intro contract E hc st r; exact ⟨_, (returns_pure _ _).2 rfl⟩
  get_sg_vote_with_nonempty := by intro contract E hc st r A2; exact ⟨_, (returns_pure _ _).2 rfl⟩
  update_confirmation_with_nonempty := by intro contract E hc st s; exact ⟨_, (returns_pure _ _).2 rfl⟩
  select_nonempty := fun _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  with_proposal_input_nonempty := fun _ _ _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  proposal_with_nonempty := fun _ _ _ _ _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  carriedRows_nonempty := fun _ _ => ⟨_, (returns_pure _ _).2 rfl⟩
  orderedBodies_nonempty := fun _ => ⟨_, (returns_pure _ _).2 rfl⟩
  duties_update_confirmation_with_nonempty := by intro contract E hc st s; exact ⟨_, (returns_pure _ _).2 rfl⟩
  fg_source_with_nonempty := by intro contract E hc st r A2; exact ⟨_, (returns_pure _ _).2 rfl⟩
  processed_rows_erasure := fun hc st h => _root_.DecoupledConsensusModel.Proofs.NamedProposalRows.processed_rows_erasure hc st h
  chainRows_iff_named_chain := fun B a => (priv% Proofs.Vocabulary.Protocol.ChainState.RawHeightCoverage DecoupledConsensusModel.Proofs.HealingSurface.chainRows_iff_named_chain) (V := V) (B := B) (a := a)
  duties_attest_with_store_with_cache := fun _ _ _ _ _ _ _ => rfl
  duties_update_confirmation_with_store_with_cache_outcome := fun _ _ _ _ _ _ h => h
  duties_goldfish_vote_with_store_with_cache := fun _ _ _ _ _ _ => rfl
  proposal_with_store_with_cache := fun _ _ _ _ _ _ _ => rfl
  coherent_confirmation := fun gc E hc cfg st s h D hD => by obtain rfl := (returns_pure _ _).1 hD; exact _root_.DecoupledConsensusModel.Proofs.NamedDuties.coherent_confirmation gc E hc cfg st s h

/-- `Model.vocabulary` satisfies `NodeFacts`. -/
theorem Model.vocabulary_facts_node : NodeFacts (Model.vocabulary (V := V)) where
  treeBlockShapedStep_node_tick := by intro S v n t out hout; simp only [Model.vocabulary, returns_pure] at hout; subst hout; exact _root_.DecoupledConsensusModel.Sts.treeBlockShapedStep_node_tick S v n t
  treeBlockShapedStep_node_process := by intro S n o n' hn'; simp only [Model.vocabulary, returns_pure] at hn'; subst hn'; exact _root_.DecoupledConsensusModel.Sts.treeBlockShapedStep_node_process S n o
  sgMono_node_tick := by intro S v n t hs out hout; simp only [Model.vocabulary, returns_pure] at hout; subst hout; exact (DecoupledConsensusModel.Sts.Restated.SgMono_vocabulary_eq _ _ _).1 (_root_.DecoupledConsensusModel.Sts.sgMono_node_tick S v n t hs)
  sgMono_process := fun S st o => (DecoupledConsensusModel.Sts.Restated.SgMono_vocabulary_eq _ _ _).1 (_root_.DecoupledConsensusModel.Sts.sgMono_process S st o)
  process_nonempty := fun S n o _ => ⟨_, (Record.returns_pure _ _).2 rfl⟩
  tick_send_eq_of_state := by
    intro S v n t out out' h h' _
    obtain rfl := (Record.returns_pure _ _).mp h
    obtain rfl := (Record.returns_pure _ _).mp h'
    rfl
  mkNode_cache := fun _ _ _ => rfl
  finalitySafeAt_on_tick_emit := by
    intro S v n t h T hs out hout
    obtain rfl := (Record.returns_pure _ _).mp hout
    exact _root_.DecoupledConsensusModel.Proofs.HealingSurface.finalitySafeAt_on_tick_emit S v n t hs
  on_tick_emit_finalitySafeAt_of_mem := by
    intro S v n t out hout a hmem h T hfp
    obtain rfl := (Record.returns_pure _ _).mp hout
    exact _root_.DecoupledConsensusModel.Proofs.HealingSurface.on_tick_emit_finalitySafeAt_of_mem S v n t hmem hfp
  on_tick_emit_timeout_true_of_mem := by
    intro S v n t out hout a hmem h hhp
    obtain rfl := (Record.returns_pure _ _).mp hout
    exact _root_.DecoupledConsensusModel.Proofs.HealingSurface.on_tick_emit_timeout_true_of_mem S v n t hmem hhp
  rawRelay_process_data := by intro S bound st o hcoh hd; exact (priv% Proofs.Vocabulary.Protocol.Handlers.RawRelay DecoupledConsensusModel.Proofs.NamedRawRelay.process_data) S bound st o hcoh hd
  coherent_postCore := _root_.DecoupledConsensusModel.Proofs.ModelProperties.coherent_postCore
  timeout_mono_on_tick_emit := by intro S v n t h hs out hout; rw [(Record.returns_pure _ _).mp hout]; exact _root_.DecoupledConsensusModel.Proofs.HealingSurface.timeout_mono_on_tick_emit S v n t hs
  on_tick_emit_timeout_introduced := by intro S v n t h hpre out hout hpost; rw [(Record.returns_pure _ _).mp hout] at hpost ⊢; exact _root_.DecoupledConsensusModel.Proofs.HealingSurface.on_tick_emit_timeout_introduced S v n t hpre hpost
  on_tick_emit_lock_introduced := by intro S v n t h T hpre out hout hpost; rw [(Record.returns_pure _ _).mp hout] at hpost ⊢; exact _root_.DecoupledConsensusModel.Protocol.on_tick_emit_lock_introduced S v n t hpre hpost
  on_tick_emit_target_introduced := by intro S v n t h T hpre out hout hpost; rw [(Record.returns_pure _ _).mp hout] at hpost ⊢; exact _root_.DecoupledConsensusModel.Protocol.on_tick_emit_target_introduced S v n t hpre hpost
  node_tick_h_max_le_succ := by intro S v n t h out hout; simp only [Model.vocabulary, returns_pure] at hout; subst hout; exact (priv% Proofs.Vocabulary.Protocol.Handlers.HMaxCore DecoupledConsensusModel.Proofs.HealingSurface.node_tick_h_max_le_succ) S v n t h
  node_process_h_max_le_succ := by intro S n o h n' hn'; simp only [Model.vocabulary, returns_pure] at hn'; subst hn'; exact (priv% Proofs.Vocabulary.Protocol.Handlers.HMaxCore DecoupledConsensusModel.Proofs.HealingSurface.node_process_h_max_le_succ) S n o h
  step_bodies_subset := by
    intro S w e v w' hw'
    rcases Event.eq_wake_or_ofVocabulary e with ⟨u, t, rfl⟩ | ⟨e, rfl⟩
    · rw [worldStepOf_vocabulary_wake] at hw'
      rw [Set.mem_singleton_iff.mp hw']
    · have hw'' : w' = NamedWorld.step S w e := by
        rw [worldStepOf_vocabulary] at hw'; exact hw'
      subst hw''
      exact _root_.DecoupledConsensusModel.Proofs.NamedBodyRetention.step_bodies_subset S w e v
  tick_h_max_mono := by intro S v n t out hout; simp only [Model.vocabulary, returns_pure] at hout; subst hout; exact (priv% Proofs.Vocabulary.Protocol.Handlers.HMaxMonotone DecoupledConsensusModel.Proofs.HealingSurface.node_tick_h_max_mono) S v n t
  process_h_max_mono := by intro S n o n' hn'; simp only [Model.vocabulary, returns_pure] at hn'; subst hn'; exact (priv% Proofs.Vocabulary.Protocol.Handlers.HMaxMonotone DecoupledConsensusModel.Proofs.HealingSurface.node_process_h_max_mono) S n o
  tick_core_bound := by intro S v n t out hout; simp only [Model.vocabulary, returns_pure] at hout; subst hout; exact ((priv% Proofs.Vocabulary.Protocol.Handlers.NumericStore DecoupledConsensusModel.Proofs.NamedNumericStore.node_tick_step) S v n t).2
  process_core_bound := by intro S n o n' hn'; simp only [Model.vocabulary, returns_pure] at hn'; subst hn'; exact ((priv% Proofs.Vocabulary.Protocol.Handlers.NumericStore DecoupledConsensusModel.Proofs.NamedNumericStore.node_process_step) S n o).2
  tick_core_justifier := by intro S v n t out hout; simp only [Model.vocabulary, returns_pure] at hout; subst hout; exact (priv% Proofs.Vocabulary.Protocol.Handlers.JustificationCarrier DecoupledConsensusModel.Proofs.NamedJustificationCarrier.node_tick_justifier) S v n t
  process_core_justifier := by intro S n o n' hn'; simp only [Model.vocabulary, returns_pure] at hn'; subst hn'; exact (priv% Proofs.Vocabulary.Protocol.Handlers.JustificationCarrier DecoupledConsensusModel.Proofs.NamedJustificationCarrier.node_process_justifier) S n o
  tick_proposerOk := by
    intro S v n t out hout h; simp only [Model.vocabulary, returns_pure] at hout; subst hout
    show _root_.DecoupledConsensusModel.Proofs.HealingSurface.ProposerOk S.E (Execution.NamedNode.tick S v n t).1.st.core
    rw [_root_.DecoupledConsensusModel.Proofs.ModelProperties.tick_fst_st]
    exact (priv% Proofs.Vocabulary.Protocol.Handlers.Proposer DecoupledConsensusModel.Proofs.HealingSurface.proposerOk_named_tick) S _ v n.st n.record t h
  process_proposerOk := by
    intro S n o n' hn' h; simp only [Model.vocabulary, returns_pure] at hn'; subst hn'
    show _root_.DecoupledConsensusModel.Proofs.HealingSurface.ProposerOk S.E (Execution.NamedNode.process S n o).st.core
    cases o with
    | block B =>
      rw [_root_.DecoupledConsensusModel.Proofs.ModelProperties.process_st, _root_.DecoupledConsensusModel.Proofs.ModelProperties.process_block]
      exact (priv% Proofs.Vocabulary.Protocol.Handlers.Proposer DecoupledConsensusModel.Proofs.HealingSurface.proposerOk_on_block_with) S.E S.hc S.cfg _ B h
    | gfVote u =>
      rw [_root_.DecoupledConsensusModel.Proofs.ModelProperties.process_st, _root_.DecoupledConsensusModel.Proofs.ModelProperties.process_gfVote]
      exact _root_.DecoupledConsensusModel.Proofs.HealingSurface.proposerOk_of_T_eq (_root_.DecoupledConsensusModel.Proofs.on_goldfish_vote_checked_T S.E _ u) h
    | attest a =>
      rw [_root_.DecoupledConsensusModel.Proofs.ModelProperties.process_st, _root_.DecoupledConsensusModel.Proofs.ModelProperties.process_attest]
      exact (priv% Proofs.Vocabulary.Protocol.Handlers.Proposer DecoupledConsensusModel.Proofs.HealingSurface.proposerOk_admit_row) S.E S.hc _ a h
  lockCompatible_on_tick_emit := by intro S v n t hla out hout; rw [(Record.returns_pure _ _).mp hout]; exact _root_.DecoupledConsensusModel.Proofs.HealingSurface.lockCompatible_on_tick_emit S v n t hla
  lock_mono_on_tick_emit := by intro S v n t h T hs out hout; rw [(Record.returns_pure _ _).mp hout]; exact _root_.DecoupledConsensusModel.Proofs.HealingSurface.lock_mono_on_tick_emit S v n t hs
  target_mono_on_tick_emit := by intro S v n t h T hs out hout; rw [(Record.returns_pure _ _).mp hout]; exact _root_.DecoupledConsensusModel.Proofs.HealingSurface.target_mono_on_tick_emit S v n t hs
  on_tick_emit_attestation_created := by intro S v n t _ out hout a hmem; rw [(Record.returns_pure _ _).mp hout] at hmem ⊢; exact _root_.DecoupledConsensusModel.Proofs.HealingSurface.on_tick_emit_attestation_created S v n t hmem
  mkNode_record := fun _ _ _ => rfl
  wake_st_record := fun _ => ⟨rfl, rfl⟩
  wake_cache := fun _ => rfl
  wake_events_or_id := Or.inr fun _ => rfl
  wake_idem := fun _ => rfl
  store_with_cache_bodies := fun _ _ => rfl
  store_with_cache_sg_rows := fun _ _ _ => rfl
  store_with_cache_core_T := by intros; rfl
  store_with_cache_core_F := by intros; rfl
  store_with_cache_core_J := by intros; rfl
  store_with_cache_core_s := by intros; rfl
  store_with_cache_core_t := by intros; rfl
  store_with_cache_core_h_max := by intros; rfl
  store_with_cache_core_h_j := by intros; rfl
  store_with_cache_core_σ := by intros; rfl
  store_with_cache_core_timestamp_block := by intros; rfl
  store_with_cache_core_timestamp_vote := by intros; rfl
  store_with_cache_core_timestamp_sg_vote := by intros; rfl
  store_with_cache_core_gf_votes := by intros; rfl
  store_with_cache_core_pool := by intros; rfl
  store_with_cache_core_live_confirmed := by intros; rfl
  store_with_cache_core_latest_confirmed := by intros; rfl
  store_with_cache_core_latest_stable := by intros; rfl
  store_with_cache_core_sg_votes := by intros; rfl
  store_with_cache_core_sg_pool := by intros; rfl
  store_with_cache_core_tau := by intros; rfl
  store_with_cache_core_attestations := by intros; rfl
  store_with_cache_get_fg_root := by intros; rfl
  store_with_cache_get_filtered_block_tree := by intros; rfl
  store_with_cache_voter_filtered_block_tree := by intros; rfl
  store_with_cache_voter_processed_block_tree := by intros; rfl
  store_with_cache_voter_view := by intros; rfl
  store_with_cache_voter_support_view := by intros; rfl
  store_with_cache_proposer_view := by intros; rfl
  store_with_cache_proposer_support_view := by intros; rfl
  store_with_cache_get_head_in_tree_with_layer := by intros; rfl
  store_with_cache_get_head_in_tree_with := by intros; rfl
  store_with_cache_grade2_block_with := by intros; rfl
  store_with_cache_get_sg_vote_with := by intros; rfl
  store_with_cache_onPhaseTick := by intros; rfl
  store_with_cache_readFrame := by intros; rfl
  store_with_cache_frameGradeRead := by intros; rfl
  store_with_cache_currentSGVote := by intros; rfl
  store_with_cache_inWindow := by intros; rfl
  store_with_cache_store_pool := by intros; rfl
  store_with_cache_gradeView := by intros; rfl
  reachedNode_initial := by intros; trivial
  reachedNode_wake := by intros; trivial
  runs_as_wake := by intros; trivial
  reachedNode_tick := by intros; trivial
  reachedNode_process := by intros; trivial
  reachedNode_confirmationRead := by intros; trivial
  reachedNode_confirmationDuty := by intros; trivial
  reachedStore_of_node := by intros; trivial
  reachedCore_of_store := by intros; trivial
  reachedRead_of_node := by intros; trivial
  initial_invariants := fun S _ => _root_.DecoupledConsensusModel.Proofs.NamedNode.initial_invariants S
  confirmation_invariant_tick := by intro S v n t h out hout; simp only [Model.vocabulary, returns_pure] at hout; subst hout; exact _root_.DecoupledConsensusModel.Proofs.NamedNode.confirmation_invariant_tick S v n t h
  record_invariant_tick := by intro S v n t h out hout; simp only [Model.vocabulary, returns_pure] at hout; subst hout; exact _root_.DecoupledConsensusModel.Proofs.NamedNode.record_invariant_tick S v n t h
  invariants_process := by intro S n o hStore hRecord n' hn'; simp only [Model.vocabulary, returns_pure] at hn'; subst hn'; exact _root_.DecoupledConsensusModel.Proofs.NamedNode.invariants_process S n o hStore hRecord
  mkNode_st := fun _ _ _ => rfl
  committeePools_process := fun S n o n' hn' h => by obtain rfl := (Record.returns_pure _ n').1 hn'; exact _root_.DecoupledConsensusModel.Protocol.CommitteePools.process S n o h
  sg_pool_subset_process := by intro S n o r n' hn'; simp only [Model.vocabulary, returns_pure] at hn'; subst hn'; exact _root_.DecoupledConsensusModel.Proofs.HealingLemmas.sg_pool_subset_process S n o r
  sg_pool_subset_on_tick_emit := by intro S v n t r out hout; simp only [Model.vocabulary, returns_pure] at hout; subst hout; exact _root_.DecoupledConsensusModel.Proofs.HealingLemmas.sg_pool_subset_on_tick_emit S v n t r
  tick_cache_eq := by intro S v n t out hout c hcache _; simp only [Model.vocabulary, returns_pure] at hout hcache; subst hout hcache; exact _root_.DecoupledConsensusModel.Proofs.NamedNode.tick_cache_eq S v n t
  tick_cache_round := by intro S v n t out hout; simp only [Model.vocabulary, returns_pure] at hout; subst hout; exact _root_.DecoupledConsensusModel.Proofs.NamedNode.tick_cache_round S v n t
  process_cache_eq := by intro S n o n' hn' _; simp only [Model.vocabulary, returns_pure] at hn'; subst hn'; exact _root_.DecoupledConsensusModel.Proofs.NamedNode.process_cache_eq S n o
  cache_clipped_initial := fun _ _ => _root_.DecoupledConsensusModel.Proofs.NamedNode.cache_clipped_initial (V := V)
  cache_clipped_tick := by intro S v n t out hout; simp only [Model.vocabulary, returns_pure] at hout; subst hout; exact _root_.DecoupledConsensusModel.Proofs.NamedNode.cache_clipped_tick S v n t
  cache_clipped_process := by intro S n o n' hn'; simp only [Model.vocabulary, returns_pure] at hn'; subst hn'; exact _root_.DecoupledConsensusModel.Proofs.NamedNode.cache_clipped_process S n o
  initial_cache_current_phase := fun _ _ => _root_.DecoupledConsensusModel.Proofs.ModelProperties.initial_cache_current_phase (V := V)
  process_gfVote := _root_.DecoupledConsensusModel.Proofs.ModelProperties.process_gfVote
  gradeContract_grade2_block_with := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.gradeContract_grade2_block_with
  gradeContract_read := by
    intro c E hc st r g
    exact Iff.of_eq (congrArg (· ⇢ g) (congrArg pure
      (_root_.DecoupledConsensusModel.Sts.gradeContract_read c E hc st r)))
  gradeContract_sgVote := _root_.DecoupledConsensusModel.Sts.gradeContract_sgVote
  namedNodeProcess_setupWithGST := fun S g hg n o =>
    congrArg pure (_root_.DecoupledConsensusModel.Sts.namedNodeProcess_setupWithGST S g hg n o)
  namedNodeTick_setupWithGST := fun S g hg v n t =>
    congrArg pure (_root_.DecoupledConsensusModel.Sts.namedNodeTick_setupWithGST S g hg v n t)
  named_propose_cases := by
    simp only [Model.vocabulary, returns_pure, forall_eq, forall_const]
    exact _root_.DecoupledConsensusModel.Sts.named_propose_cases
  named_vote_cases := by
    simp only [Model.vocabulary, returns_pure, forall_eq, forall_const]
    exact _root_.DecoupledConsensusModel.Sts.named_vote_cases
  process_gfVote_of_mem_pool := _root_.DecoupledConsensusModel.Sts.process_gfVote_of_mem_pool
  process_node_of_store_id := by
    intro S n o hst hcache n' hn' _
    simp only [Model.vocabulary, returns_pure] at hn'
    subst hn'
    exact _root_.DecoupledConsensusModel.Sts.process_node_of_store_id S n o hst hcache
  ModelProperties_gradeContract_read_Q2 := by
    simp only [Model.vocabulary, Model.Contract.read, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.gradeContract_read_Q2
  ModelProperties_gradeContract_read_anchor := by
    simp only [Model.vocabulary, Model.Contract.read, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.gradeContract_read_anchor
  initial_cache_round := fun _ _ => _root_.DecoupledConsensusModel.Proofs.ModelProperties.initial_cache_round (V := V)
  initial_record_legacy_lock := fun _ _ => _root_.DecoupledConsensusModel.Proofs.ModelProperties.initial_record_legacy_lock (V := V)
  initial_record_legacy_target := fun _ _ => _root_.DecoupledConsensusModel.Proofs.ModelProperties.initial_record_legacy_target (V := V)
  initial_record_legacy_timeout := fun _ _ => _root_.DecoupledConsensusModel.Proofs.ModelProperties.initial_record_legacy_timeout (V := V)
  initial_st := fun _ _ => _root_.DecoupledConsensusModel.Proofs.ModelProperties.initial_st (V := V)
  on_block_with_eq_admit_rows_postCore := _root_.DecoupledConsensusModel.Proofs.ModelProperties.on_block_with_eq_admit_rows_postCore
  on_block_with_eq_postCore_of_not_new := _root_.DecoupledConsensusModel.Proofs.ModelProperties.on_block_with_eq_postCore_of_not_new
  postCore_bodies_of_erase_mem := _root_.DecoupledConsensusModel.Proofs.ModelProperties.postCore_bodies_of_erase_mem
  postCore_clock := _root_.DecoupledConsensusModel.Proofs.ModelProperties.postCore_clock
  process_attest := _root_.DecoupledConsensusModel.Proofs.ModelProperties.process_attest
  process_block := _root_.DecoupledConsensusModel.Proofs.ModelProperties.process_block
  process_st := by intro S n o n' hn'; simp only [Model.vocabulary, returns_pure] at hn'; subst hn'; exact _root_.DecoupledConsensusModel.Proofs.ModelProperties.process_st S n o
  make_grades_compatible_with_finalized_bodies := fun _ => rfl
  make_grades_compatible_with_finalized_sg_rows := fun _ => rfl
  make_grades_compatible_with_finalized_core_t := fun _ => rfl
  make_grades_compatible_with_finalized_core_s := fun _ => rfl
  make_grades_compatible_with_finalized_core_T := fun _ => rfl
  make_grades_compatible_with_finalized_core_F := fun _ => rfl
  make_grades_compatible_with_finalized_core_gf_votes := fun _ => rfl
  make_grades_compatible_with_finalized_core_timestamp_vote := fun _ => rfl
  make_grades_compatible_with_finalized_core_timestamp_sg_vote := fun _ => rfl
  make_grades_compatible_with_finalized_core_pool := fun _ => rfl
  make_grades_compatible_with_finalized_core_round_votes := fun _ => rfl
  node_process_F := by intro S n o n' hn'; simp only [Model.vocabulary, returns_pure] at hn'; subst hn'; exact _root_.DecoupledConsensusModel.Proofs.NamedFinalityMonotone.node_process_F S n o
  node_tick_F := by intro S v n t out hout; simp only [Model.vocabulary, returns_pure] at hout; subst hout; exact _root_.DecoupledConsensusModel.Proofs.NamedFinalityMonotone.node_tick_F S v n t
  process_cache_round := by intro S n o n' hn'; simp only [Model.vocabulary, returns_pure] at hn'; subst hn'; exact _root_.DecoupledConsensusModel.Proofs.NamedNode.process_cache_round S n o
  process_clock := by intro S n o n' hn'; simp only [Model.vocabulary, returns_pure] at hn'; subst hn'; exact _root_.DecoupledConsensusModel.Proofs.NamedNode.process_clock S n o
  process_record_eq := by intro S n o n' hn'; simp only [Model.vocabulary, returns_pure] at hn'; subst hn'; exact _root_.DecoupledConsensusModel.Proofs.NamedNode.process_record_eq S n o
  tick_clock := by intro S v n t out hout; simp only [Model.vocabulary, returns_pure] at hout; subst hout; exact _root_.DecoupledConsensusModel.Proofs.NamedNode.tick_clock S v n t
  frozen_process_preceq := by intro S n o h n' hn'; simp only [Model.vocabulary, returns_pure] at hn'; subst hn'; exact _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.frozen_process_preceq S n o h
  frozen_tick_preceq := by intro S v n t h out hout; simp only [Model.vocabulary, returns_pure] at hout; subst hout; exact _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.frozen_tick_preceq S v n t h
  node_process_latest := by intro S n o n' hn'; simp only [Model.vocabulary, returns_pure] at hn'; subst hn'; exact _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.node_process_latest S n o
  node_process_stable := by intro S n o n' hn'; simp only [Model.vocabulary, returns_pure] at hn'; subst hn'; exact _root_.DecoupledConsensusModel.Proofs.NamedOutageClosure.node_process_stable S n o
  Sts_gradeContract_read_Q2 := by
    simp only [Model.vocabulary, Model.Contract.read, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.gradeContract_read_Q2
  Sts_gradeContract_read_anchor := by
    simp only [Model.vocabulary, Model.Contract.read, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.gradeContract_read_anchor
  gradeContract_read_rawG2 := by
    simp only [Model.vocabulary, Model.Contract.read, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.gradeContract_read_rawG2
  gradeContract_sgRoot_eq_frameAnchor := by
    intro c E hc st r x
    exact Iff.of_eq (congrArg (· ⇢ x) (congrArg pure
      (_root_.DecoupledConsensusModel.Sts.gradeContract_sgRoot_eq_frameAnchor c E hc st r)))
  gradeContract_stableRoot := by
    intro c E hc st r x
    exact Iff.of_eq (congrArg (· ⇢ x) (congrArg pure
      (congrFun (congrFun (congrFun (congrFun
        (_root_.DecoupledConsensusModel.Sts.gradeContract_stableRoot c) E) hc) st) r)))
  initial_body_eq_genesis := fun _ _ => _root_.DecoupledConsensusModel.Sts.initial_body_eq_genesis
  initial_cache_phaseResult_ne := fun _ _ => _root_.DecoupledConsensusModel.Sts.initial_cache_phaseResult_ne
  initial_clock_eq_zero := fun _ _ => _root_.DecoupledConsensusModel.Sts.initial_clock_eq_zero (V := V)
  initial_record_lock := fun _ _ => _root_.DecoupledConsensusModel.Sts.initial_record_lock (V := V)
  initial_record_target := fun _ _ => _root_.DecoupledConsensusModel.Sts.initial_record_target (V := V)
  initial_st_inclG2 := fun _ _ => _root_.DecoupledConsensusModel.Sts.initial_st_inclG2 (V := V)
  initial_timestamp_genesis := fun _ _ => _root_.DecoupledConsensusModel.Sts.initial_timestamp_genesis (V := V)
  namedNode_process_cache := by intro S n o n' hn' _; simp only [Model.vocabulary, returns_pure] at hn'; subst hn'; exact _root_.DecoupledConsensusModel.Sts.namedNode_process_cache S n o
  namedNode_tick_cache := by intro S v n t out hout c hcache _; simp only [Model.vocabulary, returns_pure] at hout hcache; subst hout hcache; exact _root_.DecoupledConsensusModel.Sts.namedNode_tick_cache S v n t
  node_process_body_stamp := by intro S n o n' hn' B h0 h1; simp only [Model.vocabulary, returns_pure] at hn'; subst hn'; exact _root_.DecoupledConsensusModel.Sts.node_process_body_stamp S n o B h0 h1
  node_tick_body_stamp := by intro S v n t out hout B h0 h1; simp only [Model.vocabulary, returns_pure] at hout; subst hout; exact _root_.DecoupledConsensusModel.Sts.node_tick_body_stamp S v n t B h0 h1
  postCore_eq_process_block_core := _root_.DecoupledConsensusModel.Sts.postCore_eq_process_block_core
  postCore_of_parent_not_mem := _root_.DecoupledConsensusModel.Sts.postCore_of_parent_not_mem
  postCore_sg_rows := _root_.DecoupledConsensusModel.Sts.postCore_sg_rows
  postCore_timestamp_sg_vote := _root_.DecoupledConsensusModel.Sts.postCore_timestamp_sg_vote
  process_attest_of_mem_rows := _root_.DecoupledConsensusModel.Sts.process_attest_of_mem_rows
  process_block_of_mem_bodies := _root_.DecoupledConsensusModel.Sts.process_block_of_mem_bodies
  round_action_head_mem_gradeContract := by
    simp only [Model.vocabulary, returns_pure, forall_eq]
    exact _root_.DecoupledConsensusModel.Sts.round_action_head_mem_gradeContract
  process_record := by intro S n o n' hn'; simp only [Model.vocabulary, returns_pure] at hn'; subst hn'; exact _root_.DecoupledConsensusModel.Proofs.HealingSurface.process_record S n o
  block_mem_on_tick_emit := by intro S v n t out hout B h _ _; simp only [Model.vocabulary, returns_pure] at hout; subst hout; refine ⟨(_root_.DecoupledConsensusModel.Proofs.HealingSurface.block_mem_on_tick_emit S v n t h).1, ?_⟩; intro c hc D hD; simp only [Model.vocabulary, returns_pure] at hc hD; subst hc hD; have hp := (_root_.DecoupledConsensusModel.Proofs.HealingSurface.block_mem_on_tick_emit S v n t h).2; rw [_root_.DecoupledConsensusModel.Sts.confirmationReadFrom_gradeContract, _root_.DecoupledConsensusModel.Sts.confirmationReadFrom_st] at hp; exact hp
  block_mem_on_tick_emit_awake := by intros; trivial
  gfVote_mem_on_tick_emit_awake := by intros; trivial
  tick_frame_of_not_awake_for_grade1 := fun _ _ _ _ _ _ h => absurd trivial h
  tick_records_frame_of_not_awake_for_grade2 := fun _ _ _ _ _ _ h => absurd rfl h
  tick_new_full_row_origin := by intro S v n t out hout a hpre hpost; simp only [Model.vocabulary, returns_pure] at hout; subst hout; have h1 := _root_.DecoupledConsensusModel.Proofs.ModelProperties.tick_fst_st_frameContract S v n t; have h2 := _root_.DecoupledConsensusModel.Proofs.ModelProperties.tick_snd_frameContract S v n t; have hpost' := hpost; change a ∈ (Execution.NamedNode.tick S v n t).1.st.sg_rows a.round at hpost'; rw [h1] at hpost'; show NamedObject.attest a ∈ (Execution.NamedNode.tick S v n t).2 ∨ _; rw [h2]; exact _root_.DecoupledConsensusModel.Proofs.NamedReceiptCallsF1.tick_new_full_row_origin (DecoupledConsensusModel.Protocol.frameContract (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache)) S.E S.hc S.cfg (S.node v) n.st n.record t a hpre hpost'
  wake_cache_clipped := fun _ h => h
  named_tick_preserves := by intro P S v n t hp hv hcf ha _ _ h out hout _ _; have hout' := (returns_pure _ _).1 hout; subst hout'; have hc := (returns_pure (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache) (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache)).2 rfl; unfold DecoupledConsensusModel.Execution.NamedNode.tick DecoupledConsensusModel.Execution.NamedProfile.tick DecoupledConsensusModel.Execution.NamedProfile.gradeContract; exact _root_.DecoupledConsensusModel.Execution.named_tick_preserves P _ S.E S.hc S.cfg (S.node v) (fun st hst => hp _ hc st hst _ ((returns_pure _ _).2 rfl)) (fun st hst => hv _ hc st hst _ ((returns_pure _ _).2 rfl)) (fun st s hst => hcf _ hc st s hst _ ((returns_pure _ _).2 rfl)) (fun st record hst => ha _ hc st record hst _ ((returns_pure _ _).2 rfl)) n.st n.record t h
  tick_new_vote_origin := by intro S v n t out hout u hpre hpost; have hout' := (returns_pure _ _).1 hout; subst hout'; unfold DecoupledConsensusModel.Execution.NamedNode.tick DecoupledConsensusModel.Execution.NamedProfile.tick at hpost ⊢; exact _root_.DecoupledConsensusModel.Proofs.NamedReceiptCallsGF.tick_new_vote_origin _ S.E S.hc S.cfg (S.node v) n.st n.record t u hpre hpost
  gfVote_emitted_shape := by intro S v n t out hout u h _ _; have hout' := (returns_pure _ _).1 hout; subst hout'; obtain ⟨hpos, ht, hd, hval, hslot⟩ := _root_.DecoupledConsensusModel.Proofs.Optimistic.gfVote_emitted_shape S v n t h; refine ⟨hpos, ht, ?_, hval, hslot⟩; intro c hc D hD; have hc' := (returns_pure _ _).1 hc; subst hc'; have hD' := (returns_pure _ _).1 hD; subst hD'; unfold DecoupledConsensusModel.Execution.NamedActionReads.confirmationReadFrom DecoupledConsensusModel.Execution.NamedActionReads.preparedCache DecoupledConsensusModel.Execution.NamedProfile.gradeContract at hd; exact hd
  tick_bodies_and_coreT_from_proposal := by
    intro S v n t out hout _ _
    have hout' := (returns_pure _ _).1 hout
    subst hout'
    have hl := _root_.DecoupledConsensusModel.Protocol.tick_bodies_and_coreT_from_proposal (DecoupledConsensusModel.Execution.NamedProfile.gradeContract (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache)) S (S.node v) n.st n.record t
    dsimp only at hl ⊢
    unfold DecoupledConsensusModel.Execution.NamedNode.tick DecoupledConsensusModel.Execution.NamedProfile.tick DecoupledConsensusModel.Execution.NamedProfile.gradeContract
    unfold DecoupledConsensusModel.Execution.NamedProfile.gradeContract at hl
    refine ⟨fun hcond c hc D hD => ?_, fun _ hcond => ?_⟩
    · have hc' := (returns_pure _ _).1 hc; subst hc'; have hD' := (returns_pure _ _).1 hD; subst hD'
      split_ifs at hl with hcnd
      · exact hl
      · exact absurd ⟨hcond.1, hcond.2.1, hcond.2.2.1⟩ hcnd
    · split_ifs at hl with hcnd
      · exact absurd ⟨hcnd.1, hcnd.2.1, hcnd.2.2, trivial⟩ hcond
      · exact hl
  tick_at_action_awake := by intro S v before r out hout c hc st hst D hD (hawake : (S.node v).awake r = true) _ _; obtain rfl := (returns_pure _ _).1 hout; obtain rfl := (returns_pure _ _).1 hc; obtain rfl := (returns_pure _ _).1 hst; obtain rfl := (returns_pure _ _).1 hD; have h := _root_.DecoupledConsensusModel.Proofs.NamedActionSources.tick_at_action S v before r; rw [if_pos hawake] at h; rw [show (Model.vocabulary (V := V)).a S.hc S.E.Δ r = S.a r from rfl, h]; unfold NamedActionReads.actionReadFrom NamedActionReads.confirmationReadFrom NamedActionReads.preparedCache; simp only [Model.vocabulary, Model.N.st, Model.N.record, Model.N.cache, Model.NS.core, Model.S.toHealing]
  tick_at_action_asleep := by intro S v before r out hout (hasleep : ¬ (S.node v).awake r = true); obtain rfl := (returns_pure _ _).1 hout; have h := _root_.DecoupledConsensusModel.Proofs.NamedActionSources.tick_at_action S v before r; rw [if_neg hasleep] at h; exact h
  on_tick_emit_confirmation_of_outcomes := by intro S v n s hs out hout c hc D hD _ _; obtain rfl := (returns_pure _ _).1 hout; obtain rfl := (returns_pure _ _).1 hc; obtain rfl := (returns_pure _ _).1 hD; have h := _root_.DecoupledConsensusModel.Proofs.Optimistic.on_tick_emit_confirmation S v n s hs; unfold NamedActionReads.confirmationReadFrom NamedActionReads.preparedCache at h; exact h
  on_tick_emit_vote_mem_of_outcomes := by intro S v n s hs u c hc D hD hu out hout _ _ _; obtain rfl := (returns_pure _ _).1 hout; obtain rfl := (returns_pure _ _).1 hc; obtain rfl := (returns_pure _ _).1 hD; apply _root_.DecoupledConsensusModel.Proofs.Optimistic.on_tick_emit_vote_mem S v n s hs; unfold NamedActionReads.confirmationReadFrom NamedActionReads.preparedCache; exact hu
  on_tick_emit_proposal_mem_of_outcomes := by intro S v n s hs hpr B c hc D hD hB out hout _ _ _; obtain rfl := (returns_pure _ _).1 hout; obtain rfl := (returns_pure _ _).1 hc; obtain rfl := (returns_pure _ _).1 hD; apply _root_.DecoupledConsensusModel.Proofs.Optimistic.on_tick_emit_proposal_mem S v n s hs hpr; unfold NamedActionReads.confirmationReadFrom NamedActionReads.preparedCache; exact hB
  tick_new_body_origin := by intro S v n t out hout B hpre hpost; have hout' := (returns_pure _ _).1 hout; subst hout'; unfold DecoupledConsensusModel.Execution.NamedNode.tick DecoupledConsensusModel.Execution.NamedProfile.tick at hpost ⊢; exact (priv% Proofs.Vocabulary.Execution.ReceiptCalls DecoupledConsensusModel.Proofs.NamedReceiptCalls.tick_new_body_origin) _ S.E S.hc S.cfg (S.node v) n.st n.record t B hpre hpost
  tick_attestation_fields := by intro S v n t _ out hout a h; obtain rfl := (returns_pure _ _).1 hout; rw [_root_.DecoupledConsensusModel.Proofs.ModelProperties.tick_snd_frameContract S v n t] at h; exact _root_.DecoupledConsensusModel.Proofs.NamedOutageHistory.OutageInputs.tick_attestation_fields _ S v _ _ t a h
  rawRelay_tick_outcome_data := by intro S v n t out hout bound ht hcoh hd; simp only [Model.vocabulary, returns_pure] at hout; subst hout; simp only [Model.N.st, Model.vocabulary] at hcoh hd ⊢; rw [_root_.DecoupledConsensusModel.Proofs.ModelProperties.tick_fst_st]; exact (priv% Proofs.Vocabulary.Protocol.Handlers.RawRelay DecoupledConsensusModel.Proofs.NamedRawRelay.tick_data) _ S bound (S.node v) _ _ t ht hcoh hd
  on_tick_emit_proposal_timestamp_block_of_outcomes := by intro S v n s hs hpr c hc D hD out hout _ _ _; obtain rfl := (returns_pure _ _).1 hout; obtain rfl := (returns_pure _ _).1 hc; obtain rfl := (returns_pure _ _).1 hD; have h := _root_.DecoupledConsensusModel.Protocol.HonestWeightMajority.on_tick_emit_proposal_timestamp_block S v n s hs hpr; unfold NamedActionReads.confirmationReadFrom NamedActionReads.preparedCache at h; exact h
  tick_new_body_core := by intro S v n t out hout B hpre hpost; simp only [Model.vocabulary, returns_pure] at hout; subst hout; have h1 := _root_.DecoupledConsensusModel.Proofs.ModelProperties.tick_fst_st_frameContract S v n t; have hpost' := hpost; change B ∈ (Execution.NamedNode.tick S v n t).1.st.bodies at hpost'; rw [h1] at hpost'; show _ ∧ _ = (Execution.NamedNode.tick S v n t).1.st.core.F; rw [h1]; exact _root_.DecoupledConsensusModel.Proofs.NamedOutageHistory.HeldSkipProducers.tick_new_body_core (DecoupledConsensusModel.Protocol.frameContract (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache)) S.E S.hc S.cfg (S.node v) n.st n.record t B hpre hpost'
  processed_mono_receipt := by intro S st o'; exact ⟨fun B h => (_root_.DecoupledConsensusModel.Sts.processed_block_iff _ B).1 (_root_.DecoupledConsensusModel.Sts.processed_mono_receipt S st (.block B) o' ((_root_.DecoupledConsensusModel.Sts.processed_block_iff st B).2 h)), fun u h => (_root_.DecoupledConsensusModel.Sts.processed_gfVote_iff _ u).1 (_root_.DecoupledConsensusModel.Sts.processed_mono_receipt S st (.gfVote u) o' ((_root_.DecoupledConsensusModel.Sts.processed_gfVote_iff st u).2 h)), fun a h => (_root_.DecoupledConsensusModel.Sts.processed_attest_iff _ a).1 (_root_.DecoupledConsensusModel.Sts.processed_mono_receipt S st (.attest a) o' ((_root_.DecoupledConsensusModel.Sts.processed_attest_iff st a).2 h))⟩
  flip_of_process := by intro S st o'; refine ⟨fun B h0 h1 => ?_, fun u h0 h1 => _root_.DecoupledConsensusModel.Sts.flip_of_process S st o' (.gfVote u) (Bool.eq_false_iff.2 fun h => h0 ((_root_.DecoupledConsensusModel.Sts.processed_gfVote_iff st u).1 h)) ((_root_.DecoupledConsensusModel.Sts.processed_gfVote_iff _ u).2 h1), fun a h0 h1 => _root_.DecoupledConsensusModel.Sts.flip_of_process S st o' (.attest a) (Bool.eq_false_iff.2 fun h => h0 ((_root_.DecoupledConsensusModel.Sts.processed_attest_iff st a).1 h)) ((_root_.DecoupledConsensusModel.Sts.processed_attest_iff _ a).2 h1)⟩; rcases _root_.DecoupledConsensusModel.Sts.flip_of_process S st o' (.block B) (Bool.eq_false_iff.2 fun h => h0 ((_root_.DecoupledConsensusModel.Sts.processed_block_iff st B).1 h)) ((_root_.DecoupledConsensusModel.Sts.processed_block_iff _ B).2 h1) with h | ⟨C, -, hc⟩; exacts [h, hc.elim]
  receipt_noop_or_processed := by intro S st; exact ⟨fun B => (_root_.DecoupledConsensusModel.Sts.receipt_noop_or_processed S st (.block B)).imp id (_root_.DecoupledConsensusModel.Sts.processed_block_iff _ B).1, fun u => (_root_.DecoupledConsensusModel.Sts.receipt_noop_or_processed S st (.gfVote u)).imp id (_root_.DecoupledConsensusModel.Sts.processed_gfVote_iff _ u).1, fun a => (_root_.DecoupledConsensusModel.Sts.receipt_noop_or_processed S st (.attest a)).imp id (_root_.DecoupledConsensusModel.Sts.processed_attest_iff _ a).1⟩
  addsOnlyCarried_node_tick := by intro S v n t out hout; have hout' := (returns_pure _ _).1 hout; subst hout'; have h := _root_.DecoupledConsensusModel.Sts.addsOnlyCarried_node_tick S v n t; refine ⟨⟨fun B hB => (_root_.DecoupledConsensusModel.Sts.processed_block_iff _ B).1 (h.1 (.block B) ((_root_.DecoupledConsensusModel.Sts.processed_block_iff _ B).2 hB)), fun u hu => (_root_.DecoupledConsensusModel.Sts.processed_gfVote_iff _ u).1 (h.1 (.gfVote u) ((_root_.DecoupledConsensusModel.Sts.processed_gfVote_iff _ u).2 hu)), fun a ha => (_root_.DecoupledConsensusModel.Sts.processed_attest_iff _ a).1 (h.1 (.attest a) ((_root_.DecoupledConsensusModel.Sts.processed_attest_iff _ a).2 ha))⟩, fun B h0 h1 => ?_, fun u h0 h1 => h.2 (.gfVote u) (Bool.eq_false_iff.2 fun h' => h0 ((_root_.DecoupledConsensusModel.Sts.processed_gfVote_iff _ u).1 h')) ((_root_.DecoupledConsensusModel.Sts.processed_gfVote_iff _ u).2 h1), fun a h0 h1 => h.2 (.attest a) (Bool.eq_false_iff.2 fun h' => h0 ((_root_.DecoupledConsensusModel.Sts.processed_attest_iff _ a).1 h')) ((_root_.DecoupledConsensusModel.Sts.processed_attest_iff _ a).2 h1)⟩; rcases h.2 (.block B) (Bool.eq_false_iff.2 fun h' => h0 ((_root_.DecoupledConsensusModel.Sts.processed_block_iff _ B).1 h')) ((_root_.DecoupledConsensusModel.Sts.processed_block_iff _ B).2 h1) with h' | ⟨C, -, hc⟩; exacts [h', hc.elim]
  tick_fields_from_proposal := by
    intro S v n t out hout hdue _ c hc D hD _ _
    obtain rfl := (returns_pure _ _).1 hout
    obtain rfl := (returns_pure _ _).1 hc
    obtain rfl := (returns_pure _ _).1 hD
    have hl := _root_.DecoupledConsensusModel.Proofs.Optimistic.tick_fields_from_proposal (DecoupledConsensusModel.Execution.NamedProfile.gradeContract (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache)) S (S.node v) n.st n.record t hdue
    dsimp only at hl ⊢
    unfold DecoupledConsensusModel.Execution.NamedNode.tick DecoupledConsensusModel.Execution.NamedProfile.tick DecoupledConsensusModel.Execution.NamedProfile.gradeContract
    unfold DecoupledConsensusModel.Execution.NamedProfile.gradeContract at hl
    split_ifs at hl with hcnd
    · exact hl
    · exact absurd hdue hcnd
  advance_tick_of_stage1 := by intro S v n t out hout _ h _ _; obtain rfl := (returns_pure _ _).1 hout; have h1 := h _ ((returns_pure _ _).2 rfl) _ (by rw [Restated.Vocabulary.Proofs.HealingSurface.tickStage1_vocabulary_eq]; exact (returns_pure _ _).2 rfl); have hfc : (Model.vocabulary (V := V)).frameContract (Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache) = NamedProfile.gradeContract (Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache) := (by simp only [Model.vocabulary, NamedProfile.gradeContract]); rw [hfc] at h1; show _root_.DecoupledConsensusModel.Proofs.HealingSurface.NamedFinalityAdvance S (NamedNode.tick S v n t).1.st; rw [_root_.DecoupledConsensusModel.Proofs.ModelProperties.tick_fst_st]; exact _root_.DecoupledConsensusModel.Proofs.HealingSurface.advance_tick_of_stage1 S _ (S.node v) n.st n.record t ((Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance_vocabulary_eq S _).mpr h1)
  action_tick_store_of_outcomes := by
    intro S v before r (hawake : (S.node v).awake r = true) out hout c hc st hst D hD _ _
    suffices hst' : out.1.st = D.1 by rw [hst']
    obtain rfl := (returns_pure _ _).1 hout
    obtain rfl := (returns_pure _ _).1 hc
    obtain rfl := (returns_pure _ _).1 hst
    obtain rfl := (returns_pure _ _).1 hD
    have h := _root_.DecoupledConsensusModel.Proofs.NamedOutageHistory.SGArrival.action_tick_store
      S v before r hawake
    refine h.trans ?_
    unfold Internal.NamedOutageEntry.actionReadFrom NamedActionReads.actionReadFrom
      NamedActionReads.confirmationReadFrom NamedActionReads.preparedCache
    simp only [Model.vocabulary, Model.N.st, Model.N.record, Model.N.cache, Model.NS.core,
      Model.S.toHealing]
  tick_rows_after_proposal_of_outcomes := by
    intro S v n t out hout _ _
    obtain rfl := (returns_pure _ _).1 hout
    have h := _root_.DecoupledConsensusModel.Proofs.NamedOutageHistory.SGArrival.tick_rows_after_proposal
      (DecoupledConsensusModel.Protocol.frameContract
        (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
      S (S.node v) n.st n.record t
    refine ⟨fun hdue c hc D hD a ha => ?_, fun hndue a ha => ?_⟩
    · obtain rfl := (returns_pure _ _).1 hc
      obtain rfl := (returns_pure _ _).1 hD
      simp only [Model.N.st, Model.vocabulary]
      rw [_root_.DecoupledConsensusModel.Proofs.ModelProperties.tick_fst_st_frameContract S v n t]
      refine h a ?_
      split_ifs with hh
      · exact ha
      · exact absurd ⟨hdue.1, hdue.2.1, hdue.2.2.1⟩ hh
    · simp only [Model.N.st, Model.vocabulary]
      rw [_root_.DecoupledConsensusModel.Proofs.ModelProperties.tick_fst_st_frameContract S v n t]
      refine h a ?_
      split_ifs with hh
      · exact absurd ⟨hh.1, hh.2.1, hh.2.2, trivial⟩ hndue
      · exact ha
  postCore_absorbs_finality := fun S before B h₁ h₂ h₃ h₄ h₅ h₆ h₇ _ =>
    _root_.DecoupledConsensusModel.Sts.postCore_absorbs_finality_r58a S before B h₁ h₂ h₃ h₄ h₅ h₆ h₇
  node_tick_sg_row_stamp := by
    intro S v n t out hout hcoh a hpre hpost
    simp only [Model.vocabulary, returns_pure] at hout
    subst hout
    have h1 := _root_.DecoupledConsensusModel.Proofs.ModelProperties.tick_fst_st S v n t
    change a ∈ (Execution.NamedNode.tick S v n t).1.st.sg_rows a.round at hpost
    change (Execution.NamedNode.tick S v n t).1.st.core.timestamp_sg_vote
      (DecoupledConsensusModel.Protocol.sgVote a.erase) = some (t : Stamp)
    rw [h1] at hpost ⊢
    exact (priv% Proofs.Vocabulary.Protocol.Store.PublicCutSG
      DecoupledConsensusModel.Proofs.NamedPublicCutSG.tick_new_stamp)
      (NamedProfile.gradeContract
        (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
      S (S.node v) n.st n.record t a hcoh hpre hpost
  receipt_process_sg_row_stamp := fun S st o a hpre hpost =>
    (priv% Proofs.Vocabulary.Protocol.Store.PublicCutSG
      DecoupledConsensusModel.Proofs.NamedPublicCutSG.process_new_stamp) S st o a hpre hpost
  tick_vote_pooled := _root_.DecoupledConsensusModel.Proofs.Optimistic.record_vocabulary_tick_vote_pooled
  initial_setupWithGST := fun _ _ _ _ => rfl
  tick_records_at_confirmation_of_outcomes := by
    intro S v n t hspos hnp hnv hsc _ out hout c hc D hD _
    obtain rfl := (returns_pure _ _).1 hout
    obtain rfl := (returns_pure _ _).1 hc
    obtain rfl := (returns_pure _ _).1 hD
    have h := _root_.DecoupledConsensusModel.Sts.namedTick_records_at_confirmation
      (NamedProfile.gradeContract (Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
      S.E S.hc S.cfg (S.node v) n.st n.record t hspos hnp hnv hsc
    have h1 := _root_.DecoupledConsensusModel.Proofs.ModelProperties.tick_fst_st S v n t
    simp only [Model.vocabulary, Model.N.st, Model.NS.core, Model.S.latest_stable,
      Model.S.latest_confirmed, Model.N.cache, Model.N.record] at h h1 ⊢
    rw [h1]
    exact h
  on_tick_emit_stable_of_ne := by intro S v n t h out hout; simp only [Model.vocabulary, returns_pure] at hout; subst hout; exact _root_.DecoupledConsensusModel.Proofs.StableRecord.on_tick_emit_stable_of_ne S v n t h
  on_tick_emit_latest_of_ne := by intro S v n t h out hout; simp only [Model.vocabulary, returns_pure] at hout; subst hout; exact _root_.DecoupledConsensusModel.Proofs.ConfirmationOrigin.on_tick_emit_latest_of_ne S v n t h
  gradeContract_confirmationSG := by
    intro c E hc st s x
    simp only [Model.vocabulary, Model.Contract.confirmationSG,
      _root_.DecoupledConsensusModel.Sts.gradeContract_confirmationSG]
  gradeContract_eq_frameContract := fun c =>
    show _root_.DecoupledConsensusModel.Execution.NamedProfile.gradeContract c
      = _root_.DecoupledConsensusModel.Protocol.frameContract c from
    by unfold _root_.DecoupledConsensusModel.Execution.NamedProfile.gradeContract; rfl
  tick_tree_fields_of_not_proposal_vote := by
    intro S v n t hnp hnv out hout
    obtain rfl := (returns_pure _ _).1 hout
    have h := _root_.DecoupledConsensusModel.Sts.namedTick_tree_fields_of_not_proposal_vote
      (NamedProfile.gradeContract (Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
      S.E S.hc S.cfg (S.node v) n.st n.record t hnp hnv
    have h1 := _root_.DecoupledConsensusModel.Proofs.ModelProperties.tick_fst_st S v n t
    simp only [Model.vocabulary, Model.N.st, Model.NS.core, Model.NS.bodies, Model.S.F, Model.S.J,
      Model.S.h_j, Model.S.h_max, Model.S.T, Model.N.cache, Model.N.record] at h h1 ⊢
    rw [h1]
    exact h

/-- `Model.vocabulary` satisfies `EvidenceFacts`. -/
theorem Model.vocabulary_facts_evidence : EvidenceFacts (Model.vocabulary (V := V)) where
  no_faulty_intersection := _root_.DecoupledConsensusModel.Proofs.AlignedRoundLemmas.no_faulty_intersection
  hasSlashableWeightBetween_elim := _root_.DecoupledConsensusModel.Proofs.ModelProperties.hasSlashableWeightBetween_elim
  ModelProperties_hasSlashableWeightBetween_intro := _root_.DecoupledConsensusModel.Proofs.ModelProperties.hasSlashableWeightBetween_intro
  slashableBetween_elim := _root_.DecoupledConsensusModel.Proofs.ModelProperties.slashableBetween_elim
  ModelProperties_slashableBetween_intro := _root_.DecoupledConsensusModel.Proofs.ModelProperties.slashableBetween_intro
  quorum_intersection := _root_.DecoupledConsensusModel.Proofs.quorum_intersection
  Sts_hasSlashableWeightBetween_intro := _root_.DecoupledConsensusModel.Sts.hasSlashableWeightBetween_intro
  Sts_slashableBetween_intro := _root_.DecoupledConsensusModel.Sts.slashableBetween_intro
  totalWeight_le_three_mul_weightOf_of_hasIntersectionWeight := _root_.DecoupledConsensusModel.Sts.totalWeight_le_three_mul_weightOf_of_hasIntersectionWeight
  erase_mem_chain_attestations := _root_.DecoupledConsensusModel.Proofs.Bridges.erase_mem_chain_attestations
  mem_store_attestations_iff := _root_.DecoupledConsensusModel.Proofs.ModelProperties.mem_store_attestations_iff
  chain_attestations_mono := _root_.DecoupledConsensusModel.Protocol.chain_attestations_mono
  chain_attestations_subset_store := fun hB => _root_.DecoupledConsensusModel.Protocol.chain_attestations_subset_store (W := V) hB
  hasSlashableWeightBetween_mono := _root_.DecoupledConsensusModel.Protocol.hasSlashableWeightBetween_mono
  mem_chain_attestations_of_mem := fun {p s r gv gsv _ats i _a} ha => _root_.DecoupledConsensusModel.Protocol.mem_chain_attestations_of_mem (p := p) (s := s) (r := r) (gv := gv) (gsv := gsv) (i := i) ha
  named_row_erase_mem := _root_.DecoupledConsensusModel.Protocol.named_row_erase_mem
  named_mem_chain_attestations_of_erase := _root_.DecoupledConsensusModel.Sts.named_mem_chain_attestations_of_erase

end DecoupledConsensusModel.Sts.Record
