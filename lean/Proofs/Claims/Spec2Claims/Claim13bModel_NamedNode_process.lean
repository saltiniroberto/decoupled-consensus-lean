module
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `NamedNode.process`

The node receipt, which runs the receipt on the store, keeps the signing record and clips the cache.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Execution.NamedNode.process

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the receipt returns the store unchanged and the cache is already clipped against that store's
    finalized block, then `NamedNode.process` returns the node state unchanged. -/
theorem process_node_of_store_id (S : Setup V) (n : NamedNodeState V) (o : NamedObject V)
    (hst : NamedReceipt.process S n.st o = n.st)
    (hcache : Protocol.clipCache n.st.core.F n.cache = n.cache) :
    NamedNode.process S n o = n := by
  simp only [NamedNode.process, hst, hcache]

end DecoupledConsensusModel.Sts
