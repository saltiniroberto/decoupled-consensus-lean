module
public import Model.Vocabulary.Protocol.ChainState

@[expose] public section

/-!
# The chain-state family marked `irreducible`

Marks every definition of the chain-state family (the slashing conditions, the chain state's quorum
reads, `process_attestation`, `advance_height`, `process_height_events`, `fold_rows`,
`transition_rows`, `named_transition`, `derive_named` and their helpers) `irreducible`, so that a
proof reads them through facts stated about them, and `rfl`, `change` and `show` no longer see
through them. The kernel ignores the attribute, and `allowUnsafeReducibility` adds no axiom.
-/

set_option allowUnsafeReducibility true in
attribute [irreducible]
  DecoupledConsensusModel.Protocol.ChainState.Q_finality
  DecoupledConsensusModel.Protocol.ChainState.Q_prog
  DecoupledConsensusModel.Protocol.ChainState.Q_target
  DecoupledConsensusModel.Protocol.ChainState.finalityQuorum
  DecoupledConsensusModel.Protocol.ChainState.initial
  DecoupledConsensusModel.Protocol.ChainState.progQuorum
  DecoupledConsensusModel.Protocol.ChainState.targetQuorum
  DecoupledConsensusModel.Protocol.E1Slashable
  DecoupledConsensusModel.Protocol.E2Slashable
  DecoupledConsensusModel.Protocol.HonestEmissionBudget
  DecoupledConsensusModel.Protocol.SGHeadEquivocation
  DecoupledConsensusModel.Protocol.Slashable
  DecoupledConsensusModel.Protocol.TimeoutBinding.targeted
  DecoupledConsensusModel.Protocol.TimeoutBinding.targetedHeightPair
  DecoupledConsensusModel.Protocol.TimeoutBinding.view
  DecoupledConsensusModel.Protocol.advance_height
  DecoupledConsensusModel.Protocol.atMostOnePer
  DecoupledConsensusModel.Protocol.conflictsWithFinality
  DecoupledConsensusModel.Protocol.derive_named
  DecoupledConsensusModel.Protocol.e1Fields
  DecoupledConsensusModel.Protocol.e1Slashable
  DecoupledConsensusModel.Protocol.e2Fields
  DecoupledConsensusModel.Protocol.e2Slashable
  DecoupledConsensusModel.Protocol.finalityReady
  DecoupledConsensusModel.Protocol.fold_rows
  DecoupledConsensusModel.Protocol.named_transition
  DecoupledConsensusModel.Protocol.nonjustifiable
  DecoupledConsensusModel.Protocol.process_attestation
  DecoupledConsensusModel.Protocol.process_attestation_with
  DecoupledConsensusModel.Protocol.process_height_events
  DecoupledConsensusModel.Protocol.progReady
  DecoupledConsensusModel.Protocol.sameRound
  DecoupledConsensusModel.Protocol.sameValidator
  DecoupledConsensusModel.Protocol.selfSlashable
  DecoupledConsensusModel.Protocol.sgHeadEquivocation
  DecoupledConsensusModel.Protocol.slashable
  DecoupledConsensusModel.Protocol.targetReady
  DecoupledConsensusModel.Protocol.transition_rows
