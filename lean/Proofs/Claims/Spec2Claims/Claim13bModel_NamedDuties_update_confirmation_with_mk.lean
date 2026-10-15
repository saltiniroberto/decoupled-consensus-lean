module
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# More facts about `NamedDuties.update_confirmation_with`

The objects the store records across the named confirmation duty.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Execution.NamedReceipt.processed
  DecoupledConsensusModel.Protocol.NamedDuties.update_confirmation_with
  DecoupledConsensusModel.Protocol.Store.pool
  DecoupledConsensusModel.Protocol.update_confirmation_with

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- After the named confirmation duty, the store records exactly the objects it recorded before. -/
theorem processed_update_confirmation_with (gc : GradeContract V) (E : Env V)
    (hc : HealConfig) (st : NamedStore V) (s : Slot) (o : NamedObject V) :
    NamedReceipt.processed (NamedDuties.update_confirmation_with gc E hc st s) o
      = NamedReceipt.processed st o := by
  cases o <;> rfl

end DecoupledConsensusModel.Sts
