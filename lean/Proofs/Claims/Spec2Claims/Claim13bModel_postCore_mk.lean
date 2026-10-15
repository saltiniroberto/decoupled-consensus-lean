module
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `NamedReceiptCalls.postCore`, as a module file

The erased tree and named bodies of the store a block receipt's core leaves.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Execution.NamedReceiptCalls.postCore

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The erased tree of the store the receipt core leaves on block `B` is the erased tree of the
    store the named block core leaves on `B`. -/
theorem postCore_core_T_eq (S : Setup V) (before : Protocol.NamedStore V) (B : NamedBlock V) :
    (NamedReceiptCalls.postCore S before B).core.T
      = (Protocol.NamedStore.process_block_core S.E S.hc S.cfg before B).core.T := rfl

/-- The named bodies of the store the receipt core leaves on block `B` are the named bodies of the
    store the named block core leaves on `B`. -/
theorem postCore_bodies_eq (S : Setup V) (before : Protocol.NamedStore V) (B : NamedBlock V) :
    (NamedReceiptCalls.postCore S before B).bodies
      = (Protocol.NamedStore.process_block_core S.E S.hc S.cfg before B).bodies := rfl

end DecoupledConsensusModel.Sts
