module
public import Model.Vocabulary.Protocol.Grades
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.opening`, as a module file

Round `r` opens at the proposal instant of its opening slot.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.opening

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Round `r` opens at the proposal instant of its opening slot. -/
theorem opening_eq_proposal_time_inclRelay (E : Env V) (hc : Protocol.HealConfig) (r : Round) :
    Protocol.opening E hc r = Protocol.proposal_time E (hc.opening_slot r) := rfl

end DecoupledConsensusModel.Sts
