module
public import Model.Vocabulary.Protocol.Handlers
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.NamedStore.setClock`

Lemmas that unfold the clock stamp a tick puts on a named store.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedStore.setClock
  DecoupledConsensusModel.Protocol.Store.toHealing DecoupledConsensusModel.Protocol.get_fg_root
  DecoupledConsensusModel.Protocol.get_filtered_block_tree
  DecoupledConsensusModel.Protocol.get_filtered_block_tree_from

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Stamping a named store with the time `t` leaves its `latest_stable` unchanged. -/
theorem setClock_core_latest_stable (E : Env V) (st : Protocol.NamedStore V) (t : Int) :
    (Protocol.NamedStore.setClock E st t).core.latest_stable = st.core.latest_stable := rfl

/-- Stamping a named store with the time `t` leaves its `latest_confirmed` unchanged. -/
theorem setClock_core_latest_confirmed (E : Env V) (st : Protocol.NamedStore V) (t : Int) :
    (Protocol.NamedStore.setClock E st t).core.latest_confirmed = st.core.latest_confirmed := rfl

/-- Stamping a named store with the time `t` sets its slot to the slot of `t`. -/
theorem setClock_core_s (E : Env V) (st : Protocol.NamedStore V) (t : Int) :
    (Protocol.NamedStore.setClock E st t).core.s = E.slotOf t := rfl

/-- Stamping a named store with the time `t` sets its clock to `t`. -/
theorem setClock_core_t (E : Env V) (st : Protocol.NamedStore V) (t : Int) :
    (Protocol.NamedStore.setClock E st t).core.t = t := rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The SG rows of the named store `setClock E st t` are the SG rows of `st`. -/
theorem setClock_sg_rows (E : Env V) (st : Protocol.NamedStore V) (t : Int) :
    (Protocol.NamedStore.setClock E st t).sg_rows = st.sg_rows := rfl

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Stamping a named store with the time `t` leaves the SG-vote lists of its core store unchanged. -/
theorem setClock_core_sg_votes (E : Env V) (st : Protocol.NamedStore V) (t : Int) :
    (Protocol.NamedStore.setClock E st t).core.sg_votes = st.core.sg_votes := rfl

end DecoupledConsensusModel.Sts
