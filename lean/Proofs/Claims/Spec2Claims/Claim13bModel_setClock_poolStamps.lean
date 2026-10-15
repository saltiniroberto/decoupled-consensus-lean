module
public import Proofs.Vocabulary.Protocol.Handlers.Pool
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.NamedStore.setClock`: the pool's stamp invariant

Stamping a store with a later time keeps `Protocol.PoolStamps`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedStore.setClock

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the core store of the named store `st` satisfies `Protocol.PoolStamps` and its clock is at
    most `t`, then the core store of `st` stamped with `t` satisfies it too. -/
theorem poolStamps_setClock (E : Env V) (st : Protocol.NamedStore V) (t : Int)
    (hle : st.core.t ≤ t) (h : Protocol.PoolStamps st.core) :
    Protocol.PoolStamps (Protocol.NamedStore.setClock E st t).core :=
  (Protocol.poolStep_tickStore st.core t (E.slotOf t) hle h).2

end DecoupledConsensusModel.Sts
