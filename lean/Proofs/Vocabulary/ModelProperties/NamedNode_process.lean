module
public import Model.Vocabulary.Execution.Node

@[expose] public section

/-!
# Facts about `Execution.NamedNode.process`

The node state after a receipt.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The store of the node state after `n` processes `o` is `NamedReceipt.process` on `n`'s store and
    `o`. -/
theorem process_st (S : Setup V) (n : NamedNodeState V) (o : NamedObject V) :
    (NamedNode.process S n o).st = NamedReceipt.process S n.st o := rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
