import Model.Vocabulary.Protocol.Handlers
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.NamedStore.setClock`: the bodies

The clock stamp keeps the named bodies.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedStore.setClock

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Stamping a named store with the time `t` leaves its named bodies unchanged. -/
theorem setClock_bodies (E : Env V) (st : Protocol.NamedStore V) (t : Int) :
    (Protocol.NamedStore.setClock E st t).bodies = st.bodies := rfl

end DecoupledConsensusModel.Sts
