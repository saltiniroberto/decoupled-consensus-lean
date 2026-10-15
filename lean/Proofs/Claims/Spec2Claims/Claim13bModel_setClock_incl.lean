module
public import Model.Vocabulary.Protocol.Handlers
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.NamedStore.setClock`: the fields a confirmation walk reads

The clock stamp writes only the clock and the slot, so the tree, the finalized and justified blocks,
the running maximum height and the recorded chain states are the store's own.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedStore.setClock

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Stamping a named store with the time `t` leaves its block tree unchanged. -/
theorem setClock_core_T (E : Env V) (st : Protocol.NamedStore V) (t : Int) :
    (Protocol.NamedStore.setClock E st t).core.T = st.core.T := rfl

/-- Stamping a named store with the time `t` leaves its finalized block unchanged. -/
theorem setClock_core_F (E : Env V) (st : Protocol.NamedStore V) (t : Int) :
    (Protocol.NamedStore.setClock E st t).core.F = st.core.F := rfl

/-- Stamping a named store with the time `t` leaves its justified block unchanged. -/
theorem setClock_core_J (E : Env V) (st : Protocol.NamedStore V) (t : Int) :
    (Protocol.NamedStore.setClock E st t).core.J = st.core.J := rfl

/-- Stamping a named store with the time `t` leaves its running maximum chain-state height `h_max`
    unchanged. -/
theorem setClock_core_h_max (E : Env V) (st : Protocol.NamedStore V) (t : Int) :
    (Protocol.NamedStore.setClock E st t).core.h_max = st.core.h_max := rfl

/-- Stamping a named store with the time `t` leaves the chain state it records for every block
    unchanged. -/
theorem setClock_core_σ (E : Env V) (st : Protocol.NamedStore V) (t : Int) :
    (Protocol.NamedStore.setClock E st t).core.σ = st.core.σ := rfl

end DecoupledConsensusModel.Sts
