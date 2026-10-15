import Proofs.Vocabulary.Execution.Runtime
import Proofs.Claims.ModelIrreducible
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedStore_initial_stamp
import Proofs.Vocabulary.Protocol.Handlers.Pool

/-!
# Facts about `Protocol.NamedStore.initial`

The named store every validator starts from.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Execution.NamedNode.initial
  DecoupledConsensusModel.Protocol.NamedStore.initial DecoupledConsensusModel.Protocol.Store.init

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The height maximum `h_max` of the initial named store's core store is `1`. -/
theorem namedStore_initial_h_max :
    (Protocol.NamedStore.initial : Protocol.NamedStore V).core.h_max = 1 := rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The core store of the initial named store satisfies `Protocol.PoolStamps`: its Goldfish pool and
    its vote stamps are empty. -/
theorem poolStamps_initial :
    Protocol.PoolStamps (Protocol.NamedStore.initial : Protocol.NamedStore V).core := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Protocol.NamedStore.initial, Protocol.Store.init]

end DecoupledConsensusModel.Sts
