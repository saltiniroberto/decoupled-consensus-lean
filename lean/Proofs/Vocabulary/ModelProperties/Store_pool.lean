module
public import Model.Vocabulary.Protocol.Store

@[expose] public section

/-!
# Facts about `Protocol.Store.pool`

A slot's processed Goldfish votes of a store, read as a set.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V]

/-- A Goldfish vote is in the pool of `st` at slot `k` exactly when it is in the list
    `st.gf_votes k`. -/
theorem mem_pool_iff (st : Protocol.Store V) (k : Slot) (u : GoldfishVote V) :
    u ∈ st.pool k ↔ u ∈ st.gf_votes k := by
  unfold Protocol.Store.pool
  exact List.mem_toFinset

end DecoupledConsensusModel.Proofs.ModelProperties

end
