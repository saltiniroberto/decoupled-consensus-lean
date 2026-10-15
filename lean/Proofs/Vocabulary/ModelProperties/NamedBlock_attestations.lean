module
public import Model.Vocabulary.Objects.NamedBlocks

@[expose] public section

/-!
# Facts about `NamedBlock.attestations`

The attestations a named block carries, at genesis.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type}

/-- The named genesis block carries no attestation. -/
theorem attestations_genesis : (NamedBlock.genesis : NamedBlock V).attestations = [] := rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
