module
public import Proofs.Vocabulary.Protocol.ChainState.DerivationGeometry

@[expose] public section

/-!
# The height target is an ancestor of the block

The height target `T_h` of a named block's derived state is an ancestor of the block.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace Optimistic

open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The height target of `B`'s derived state is an ancestor of `B.erase`. -/
theorem derive_named_T_h_preceq (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    Block.Preceq (Protocol.derive_named E cfg B).T_h B.erase := by
  simpa only [Proofs.NamedDerivationGeometry.derive_named_latest, Block.Preceq] using
    (Proofs.NamedDerivationGeometry.chainOrder_derive_named E cfg B).target_preceq_latest


end Optimistic
end Proofs
end DecoupledConsensusModel

end
