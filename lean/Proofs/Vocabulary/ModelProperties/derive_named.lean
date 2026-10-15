module
public import Model.Vocabulary.Protocol.ChainState

@[expose] public section

/-!
# Facts about `Protocol.derive_named`

The chain state a named block derives along its ancestry.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The justified height of the chain state derived for the genesis block is `0`. -/
theorem derive_named_genesis_h_j (E : Env V) (cfg : HeightConfig) :
    (derive_named E cfg (.genesis : NamedBlock V)).h_j = 0 := rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
