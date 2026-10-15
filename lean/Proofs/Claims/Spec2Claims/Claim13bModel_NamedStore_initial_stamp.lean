import Model.Vocabulary.Execution.Node
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Proofs.Claims.ModelIrreducible

/-!
# The initial store's genesis stamp and bodies

The stamp the initial store gives genesis, and its bodies.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Execution.NamedNode.initial
  DecoupledConsensusModel.Protocol.NamedStore.initial DecoupledConsensusModel.Protocol.Store.init
  DecoupledConsensusModel.genesisStamp

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V]

/-- In the node state every validator starts from, genesis carries the bottom stamp `⊥`. -/
theorem initial_timestamp_genesis :
    (NamedNode.initial : NamedNodeState V).st.core.timestamp_block Block.genesis = some ⊥ := by
  simp [NamedNode.initial, Protocol.NamedStore.initial, Protocol.Store.init, genesisStamp]

/-- Every body of the node state every validator starts from is the named genesis. -/
theorem initial_body_eq_genesis {D : NamedBlock V}
    (hD : D ∈ (NamedNode.initial : NamedNodeState V).st.bodies) : D = NamedBlock.genesis := by
  simpa only [NamedNode.initial, Protocol.NamedStore.initial, Finset.mem_singleton] using hD

end DecoupledConsensusModel.Sts
