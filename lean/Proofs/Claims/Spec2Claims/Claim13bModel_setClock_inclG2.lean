module
public import Model.Vocabulary.Protocol.Handlers
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.NamedStore.setClock`: the fields the proposal duty reads

The clock stamp keeps the Goldfish vote buckets, the pool read off them, and the vote and block
stamp maps.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedStore.setClock
  DecoupledConsensusModel.Protocol.Store.pool

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Stamping a named store with the time `t` leaves its Goldfish vote bucket of every slot `s`
    unchanged. -/
theorem setClock_core_gf_votes (E : Env V) (st : Protocol.NamedStore V) (t : Int) (s : Slot) :
    (Protocol.NamedStore.setClock E st t).core.gf_votes s = st.core.gf_votes s := rfl

/-- Stamping a named store with the time `t` leaves the set of Goldfish votes it pools for every
    slot `s` unchanged. -/
theorem setClock_core_pool (E : Env V) (st : Protocol.NamedStore V) (t : Int) (s : Slot) :
    (Protocol.NamedStore.setClock E st t).core.pool s = st.core.pool s := rfl

/-- Stamping a named store with the time `t` leaves the stamp it records for every Goldfish vote
    unchanged. -/
theorem setClock_core_timestamp_vote (E : Env V) (st : Protocol.NamedStore V) (t : Int) :
    (Protocol.NamedStore.setClock E st t).core.timestamp_vote = st.core.timestamp_vote := rfl

/-- Stamping a named store with the time `t` leaves the stamp it records for every block unchanged. -/
theorem setClock_core_timestamp_block (E : Env V) (st : Protocol.NamedStore V) (t : Int) :
    (Protocol.NamedStore.setClock E st t).core.timestamp_block = st.core.timestamp_block := rfl

end DecoupledConsensusModel.Sts
