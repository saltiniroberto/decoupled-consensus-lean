import Proofs.Vocabulary.Protocol.Handlers.SGArrivalStampCarrier
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `NamedReceiptCalls.postCore`

The named store after the core block call on a block, and the SG fields it keeps.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Execution.NamedReceiptCalls.postCore

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The named store after the core call on `B` from `before` is the store
    `Protocol.NamedStore.process_block_core` returns from `before` and `B`, under the setup's
    environment, healing configuration and height configuration. -/
theorem postCore_eq_process_block_core (S : Setup V) (before : Protocol.NamedStore V)
    (B : NamedBlock V) :
    NamedReceiptCalls.postCore S before B =
      Protocol.NamedStore.process_block_core S.E S.hc S.cfg before B := rfl

/-- The core block call keeps the named SG rows of `before`. -/
theorem postCore_sg_rows (S : Setup V) (before : Protocol.NamedStore V) (B : NamedBlock V) :
    (NamedReceiptCalls.postCore S before B).sg_rows = before.sg_rows :=
  Proofs.NamedOutageHistory.SGArrival.core_block_rows S before B

/-- The core block call keeps the SG vote stamps of `before`. -/
theorem postCore_timestamp_sg_vote (S : Setup V) (before : Protocol.NamedStore V)
    (B : NamedBlock V) :
    (NamedReceiptCalls.postCore S before B).core.timestamp_sg_vote =
      before.core.timestamp_sg_vote :=
  Proofs.NamedOutageHistory.SGArrival.core_block_stamp S before B

end DecoupledConsensusModel.Sts
