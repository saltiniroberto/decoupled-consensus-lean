module

public import Model.Vocabulary.Protocol.Store
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.Store.pool`

The pool of a store: the set its Goldfish vote bucket of a slot lists.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.Store.pool

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- A vote is in a store's pool for slot `s` exactly when it is in that store's Goldfish vote bucket
    of slot `s`. -/
theorem mem_store_pool_iff (st : Protocol.Store V) (s : Slot) (u : GoldfishVote V) :
    u ∈ st.pool s ↔ u ∈ st.gf_votes s := by
  unfold Protocol.Store.pool
  exact List.mem_toFinset

/-- Setting a store's clock and slot leaves its vote pool of every slot unchanged. -/
theorem pool_set_clock_slot (st : Protocol.Store V) (t : Int) (s k : Slot) :
    ({ st with t := t, s := s } : Protocol.Store V).pool k = st.pool k := rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- Two stores with the same Goldfish vote buckets have the same vote pool of every slot. -/
theorem pool_eq_of_gf_votes_eq {st st' : Protocol.Store V} (h : st.gf_votes = st'.gf_votes)
    (k : Slot) : st.pool k = st'.pool k := by
  unfold Protocol.Store.pool
  rw [h]

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]


end DecoupledConsensusModel.Sts
