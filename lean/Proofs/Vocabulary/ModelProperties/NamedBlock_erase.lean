module
public import Model.Vocabulary.Objects.NamedBlocks

@[expose] public section

/-!
# Facts about `NamedBlock.erase`

The erasure of a named block to a block.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type}

/-- The erasure of the named genesis block is the genesis block. -/
theorem erase_genesis : (NamedBlock.genesis : NamedBlock V).erase = Block.genesis := rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
