module
public import Proofs.Vocabulary.Objects.Ancestry
public import Proofs.Vocabulary.Internal.Legacy.Definitions.NestedOutputs

@[expose] public section

/-!
# The finalized block precedes the stable output

`Σ.F` precedes `get_stable`, for every store.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace NestedOutputs

open Internal Execution

variable {V : Type} [DecidableEq V]

/-- Finality reaches the stable output, for an arbitrary store. -/
theorem finalized_preceq_get_stable (st : Protocol.Store V) :
    Block.Preceq st.F (Protocol.get_stable st) := by
  unfold Protocol.get_stable
  split
  · assumption
  · exact Block.preceq_self _


variable [Fintype V]

end NestedOutputs
end Proofs
end DecoupledConsensusModel

end
