module
public import Proofs.Claims.ModelIrreducible
public import Proofs.Claims.Spec2Claims.Claim13bModel_Env_committee_gst
public import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAdmission_on_block_with_gst

@[expose] public section

/-!
# `NamedNode.process` does not read the GST

A node's processing of a delivered object is the same at a setup and at that setup with its GST
replaced (`setupWithGST`).
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Execution.NamedNode.process
  DecoupledConsensusModel.Protocol.clipCache DecoupledConsensusModel.Protocol.clipFrame
  DecoupledConsensusModel.Protocol.clipResult DecoupledConsensusModel.Protocol.clipGrade
  DecoupledConsensusModel.Block.compatible DecoupledConsensusModel.Block.preceq
  DecoupledConsensusModel.Execution.NamedReceipt.process
  DecoupledConsensusModel.Protocol.NamedAdmission.admit_row
  DecoupledConsensusModel.Protocol.Store.sg_pool DecoupledConsensusModel.NamedAttestation.erase
  DecoupledConsensusModel.NamedHeightPair.erase DecoupledConsensusModel.Protocol.on_sg_vote
  DecoupledConsensusModel.Protocol.sgVote DecoupledConsensusModel.Protocol.round_votes
  DecoupledConsensusModel.Protocol.HealConfig.round_of
  DecoupledConsensusModel.Protocol.on_goldfish_vote_checked
  DecoupledConsensusModel.Protocol.on_goldfish_vote DecoupledConsensusModel.Protocol.Store.pool
  DecoupledConsensusModel.Protocol.equivocates DecoupledConsensusModel.Protocol.votes_by
  DecoupledConsensusModel.Env.committee
  DecoupledConsensusModel.Protocol.NamedStore.process_block_core
  DecoupledConsensusModel.Protocol.NamedStore.commitBlock DecoupledConsensusModel.NamedBlock.erase
  DecoupledConsensusModel.Protocol.on_block_using DecoupledConsensusModel.Protocol.update_finality
  DecoupledConsensusModel.Protocol.viable_tree
  DecoupledConsensusModel.Protocol.finalized_descendants DecoupledConsensusModel.Protocol.viable
  DecoupledConsensusModel.Block.Preceq DecoupledConsensusModel.Block.prec
  DecoupledConsensusModel.Block.root DecoupledConsensusModel.genesisRoot
  DecoupledConsensusModel.Block.gf_votes DecoupledConsensusModel.Block.proposer?
  DecoupledConsensusModel.Block.parent DecoupledConsensusModel.Block.slot
  DecoupledConsensusModel.Protocol.on_block_checked_using
  DecoupledConsensusModel.Protocol.carried_attestations_admissible
  DecoupledConsensusModel.Block.attestations DecoupledConsensusModel.NamedBlock.parent
  DecoupledConsensusModel.Protocol.NamedAdmission.admit_carried
  DecoupledConsensusModel.NamedBlock.attestations
  DecoupledConsensusModel.Protocol.NamedAdmission.admit_rows

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A node's processing of a delivered object is the same at `S` and at `setupWithGST S g hg`. -/
theorem namedNodeProcess_setupWithGST (S : Setup V) (g : Int) (hg : 0 ≤ g)
    (n : NamedNodeState V) (o : NamedObject V) :
    NamedNode.process (setupWithGST S g hg) n o = NamedNode.process S n o := by
  cases o with
  | block B =>
    simp only [NamedNode.process, NamedReceipt.process]
    rw [onBlockWith_setupWithGST]
    rfl
  | gfVote u => rfl
  | attest a => rfl

end DecoupledConsensusModel.Sts
