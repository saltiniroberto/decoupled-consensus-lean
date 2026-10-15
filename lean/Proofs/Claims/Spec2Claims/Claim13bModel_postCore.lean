import Model.Vocabulary.Execution.Run
import Proofs.Claims.ModelIrreducible
import Proofs.Vocabulary.Protocol.Handlers.SGArrivalStampCarrier
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedReceiptCalls_postCore

/-!
# Facts about `Execution.NamedReceiptCalls.postCore`

Lemmas that unfold the named store a block call leaves after the block handler's core step
`Protocol.NamedStore.process_block_core`, before the block's rows are admitted.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Execution.NamedReceiptCalls.postCore
  DecoupledConsensusModel.Protocol.NamedStore.process_block_core

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the named store `before` does not hold the parent body of `B`, the store the core step of the
    call on `B` leaves is `before` itself. -/
theorem postCore_of_parent_not_mem (S : Setup V) {before : Protocol.NamedStore V}
    {B : NamedBlock V} (h : B.parent ∉ before.bodies) :
    NamedReceiptCalls.postCore S before B = before := by
  unfold NamedReceiptCalls.postCore Protocol.NamedStore.process_block_core
  rw [if_pos h]

end DecoupledConsensusModel.Sts

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]


end DecoupledConsensusModel.Sts
