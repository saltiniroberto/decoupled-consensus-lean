module
public import Proofs.Claims.ModelIrreducible
public import Proofs.Claims.Spec2Claims.Claim13bModel_named_transition
public import Proofs.Claims.Spec2Claims.Claim13bModel_Env_committee_gst

@[expose] public section

/-!
# The named block handler does not read the GST

`NamedAdmission.on_block_with` is the same routine at a setup's environment and at that environment
with its GST replaced.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedAdmission.on_block_with
  DecoupledConsensusModel.Protocol.NamedStore.process_block_core
  DecoupledConsensusModel.Protocol.NamedStore.commitBlock DecoupledConsensusModel.NamedBlock.erase
  DecoupledConsensusModel.NamedAttestation.erase DecoupledConsensusModel.NamedHeightPair.erase
  DecoupledConsensusModel.Protocol.on_block_using DecoupledConsensusModel.Protocol.update_finality
  DecoupledConsensusModel.Protocol.viable_tree
  DecoupledConsensusModel.Protocol.finalized_descendants DecoupledConsensusModel.Block.preceq
  DecoupledConsensusModel.Protocol.viable DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Block.prec DecoupledConsensusModel.Block.root
  DecoupledConsensusModel.genesisRoot DecoupledConsensusModel.Block.gf_votes
  DecoupledConsensusModel.Protocol.on_goldfish_vote_checked
  DecoupledConsensusModel.Protocol.on_goldfish_vote DecoupledConsensusModel.Protocol.Store.pool
  DecoupledConsensusModel.Protocol.equivocates DecoupledConsensusModel.Protocol.votes_by
  DecoupledConsensusModel.Env.committee DecoupledConsensusModel.Block.proposer?
  DecoupledConsensusModel.Block.parent DecoupledConsensusModel.Block.slot
  DecoupledConsensusModel.Protocol.on_block_checked_using
  DecoupledConsensusModel.Protocol.carried_attestations_admissible
  DecoupledConsensusModel.Protocol.HealConfig.round_of DecoupledConsensusModel.Block.attestations
  DecoupledConsensusModel.NamedBlock.parent
  DecoupledConsensusModel.Protocol.NamedAdmission.admit_carried
  DecoupledConsensusModel.NamedBlock.attestations
  DecoupledConsensusModel.Protocol.NamedAdmission.admit_rows
  DecoupledConsensusModel.Protocol.NamedAdmission.admit_row
  DecoupledConsensusModel.Protocol.Store.sg_pool DecoupledConsensusModel.Protocol.on_sg_vote
  DecoupledConsensusModel.Protocol.sgVote DecoupledConsensusModel.Protocol.round_votes

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `NamedAdmission.on_block_with`, with the same admission mode, heal configuration and height
    configuration, is the same routine at `S`'s environment and at `S`'s environment with its GST
    replaced by `g`. -/
theorem onBlockWith_setupWithGST (S : Setup V) (g : Int) (hg : 0 ≤ g)
    (admission : Protocol.CarriedAdmission) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) :
    NamedAdmission.on_block_with admission (setupWithGST S g hg).E hc cfg =
      NamedAdmission.on_block_with admission S.E hc cfg := by
  funext st B
  simp only [NamedAdmission.on_block_with, NamedStore.process_block_core, setupWithGST]
  rw [named_transition_withGST]
  rfl

end DecoupledConsensusModel.Sts
