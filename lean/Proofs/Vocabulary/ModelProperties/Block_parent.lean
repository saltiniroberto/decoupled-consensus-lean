module
public import Model.Vocabulary.Objects.Blocks

@[expose] public section

/-!
# Facts about `Block.parent`

The parent of a block, genesis being its own parent.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type}

/-- The parent of the genesis block is the genesis block. -/
theorem parent_genesis : (Block.genesis : Block V).parent = Block.genesis := rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
