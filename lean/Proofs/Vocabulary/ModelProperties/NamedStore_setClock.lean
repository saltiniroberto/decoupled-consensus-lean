module
public import Model.Vocabulary.Protocol.Handlers

@[expose] public section

/-!
# Facts about `Protocol.NamedStore.setClock`

The clock staging of a named store sets the clock and the slot and keeps every other field.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Clock staging keeps the Goldfish pool. -/
theorem setClock_core_pool (E : Env V) (st : Protocol.NamedStore V) (t : Time) :
    (Protocol.NamedStore.setClock E st t).core.pool = st.core.pool := rfl

/-- Clock staging keeps the block tree. -/
theorem setClock_core_T (E : Env V) (st : Protocol.NamedStore V) (t : Time) :
    (Protocol.NamedStore.setClock E st t).core.T = st.core.T := rfl

/-- Clock staging keeps the chain-state map. -/
theorem setClock_core_σ (E : Env V) (st : Protocol.NamedStore V) (t : Time) :
    (Protocol.NamedStore.setClock E st t).core.σ = st.core.σ := rfl

/-- Clock staging keeps the bodies. -/
theorem setClock_bodies (E : Env V) (st : Protocol.NamedStore V) (t : Time) :
    (Protocol.NamedStore.setClock E st t).bodies = st.bodies := rfl

/-- Clock staging to `t` sets the slot to the slot of `t`. -/
theorem setClock_core_s (E : Env V) (st : Protocol.NamedStore V) (t : Time) :
    (Protocol.NamedStore.setClock E st t).core.s = E.slotOf t := rfl

/-- Clock staging to `t` sets the clock to `t`. -/
theorem setClock_core_t (E : Env V) (st : Protocol.NamedStore V) (t : Time) :
    (Protocol.NamedStore.setClock E st t).core.t = t := rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
