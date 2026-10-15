import Model.Vocabulary.Protocol.Handlers
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.NamedStore.setClock`: the fork-choice fields

The clock stamp keeps the finalized block, the justified block, `h_max` and `h_j` of the store's
healing view.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedStore.setClock
  DecoupledConsensusModel.Protocol.Store.toHealing

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Stamping a named store with the time `t` leaves its finalized block unchanged. -/
theorem setClock_toHealing_F (E : Env V) (st : Protocol.NamedStore V) (t : Int) :
    (Protocol.NamedStore.setClock E st t).core.toHealing.F = st.core.F := rfl

/-- Stamping a named store with the time `t` leaves its justified block unchanged. -/
theorem setClock_toHealing_J (E : Env V) (st : Protocol.NamedStore V) (t : Int) :
    (Protocol.NamedStore.setClock E st t).core.toHealing.J = st.core.J := rfl

/-- Stamping a named store with the time `t` leaves its `h_max` unchanged. -/
theorem setClock_toHealing_h_max (E : Env V) (st : Protocol.NamedStore V) (t : Int) :
    (Protocol.NamedStore.setClock E st t).core.toHealing.h_max = st.core.h_max := rfl

/-- Stamping a named store with the time `t` leaves its `h_j` unchanged. -/
theorem setClock_toHealing_h_j (E : Env V) (st : Protocol.NamedStore V) (t : Int) :
    (Protocol.NamedStore.setClock E st t).core.toHealing.h_j = st.core.h_j := rfl

end DecoupledConsensusModel.Sts
