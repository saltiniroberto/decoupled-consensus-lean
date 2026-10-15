import Model.Vocabulary.Protocol.Duties.Proposals
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `NamedDuties.update_confirmation_with`

The named-store wrapper of the confirmation duty, which runs the confirmation duty on the core store
and keeps the rest of the named store.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible]
  DecoupledConsensusModel.Protocol.NamedDuties.update_confirmation_with

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The named confirmation duty keeps the bodies of `st`. -/
theorem namedDuties_update_confirmation_with_bodies (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) (s : Slot) :
    (Protocol.NamedDuties.update_confirmation_with contract E hc st s).bodies = st.bodies := rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The named confirmation duty keeps the named rows of `st`. -/
theorem namedDuties_update_confirmation_with_sg_rows (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) (s : Slot) :
    (Protocol.NamedDuties.update_confirmation_with contract E hc st s).sg_rows = st.sg_rows := rfl

end DecoupledConsensusModel.Sts
