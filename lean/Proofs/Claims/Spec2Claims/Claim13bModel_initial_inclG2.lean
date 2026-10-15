import Model.Vocabulary.Execution.Node
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `NamedNode.initial`: its store

The initial node state's store is `Protocol.NamedStore.initial`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Execution.NamedNode.initial
  DecoupledConsensusModel.Protocol.ChainState.initial
  DecoupledConsensusModel.Protocol.NamedRecord.initial
  DecoupledConsensusModel.Protocol.NamedStore.initial
  DecoupledConsensusModel.Protocol.Record.initial

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The store of the initial node state is `Protocol.NamedStore.initial`. -/
theorem initial_st_inclG2 :
    (NamedNode.initial : NamedNodeState V).st = (Protocol.NamedStore.initial : Protocol.NamedStore V) :=
  rfl

end DecoupledConsensusModel.Sts
