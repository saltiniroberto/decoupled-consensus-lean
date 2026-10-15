module
public import Model.Vocabulary.Execution.Node

@[expose] public section

/-!
# Facts about `Execution.NamedReceipt.excludes`

Whether a named store excludes an object for good, at a block.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A store whose finalized block is compatible with the erasure of `B` does not exclude `B`. -/
theorem excludes_block_eq_false_of_compatible {st : Protocol.NamedStore V} {B : NamedBlock V}
    (h : Block.compatible st.core.F B.erase = true) :
    NamedReceipt.excludes st (.block B) = false := by
  simp [NamedReceipt.excludes, h]

end DecoupledConsensusModel.Proofs.ModelProperties

end
