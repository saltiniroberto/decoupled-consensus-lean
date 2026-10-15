import Model.Vocabulary.Protocol.Evidence
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `chain_attestations`

The attestations included along the chain of a block.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.chain_attestations

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type}

/-- The chain of the genesis block includes no attestation. -/
theorem chain_attestations_genesis [DecidableEq V] :
    chain_attestations (Block.genesis : Block V) = ∅ := by
  unfold chain_attestations
  rfl

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type}

/-- The attestations included along the chain of a block node with parent `p` and attestations `ats`
    are `ats` together with those included along `p`'s chain. -/
theorem chain_attestations_node [DecidableEq V] (p : Block V) (s : Slot) (r : BlockId)
    (votes support : List (GoldfishVote V)) (ats : List (CombinedAttestation V)) (proposer : V) :
    chain_attestations (Block.node p s r votes support ats proposer) =
      ats.toFinset ∪ chain_attestations p := by
  rw [chain_attestations]

end DecoupledConsensusModel.Sts
