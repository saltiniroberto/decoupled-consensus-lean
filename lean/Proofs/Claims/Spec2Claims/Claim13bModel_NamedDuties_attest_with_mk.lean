module
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# More facts about `NamedDuties.attest_with`

The store the named attestation duty returns, related to the receipt of the row it emits.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedDuties.attest_with DecoupledConsensusModel.Execution.NamedReceipt.process

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The store the named attestation duty returns is the store the receipt of the emitted attestation
    returns, run on the store the duty was given. -/
theorem attest_with_fst_eq_process (S : Setup V) (gc : GradeContract V) (nd : Node V)
    (st : NamedStore V) (record : NamedRecord) :
    (NamedDuties.attest_with gc S.E S.hc nd st record).1
      = NamedReceipt.process S st (.attest (NamedDuties.attest_with gc S.E S.hc nd st record).2.2) :=
  rfl

end DecoupledConsensusModel.Sts
