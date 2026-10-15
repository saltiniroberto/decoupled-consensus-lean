module
public import Model.Vocabulary.Protocol.Store
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.Store.sg_pool`

A store's attestation pool of a round: the list `sg_votes` of that round, read as a set.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.Store.sg_pool

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- An attestation is in the store's attestation pool of round `r` exactly when it is in the list
    `sg_votes r`. -/
theorem mem_sg_pool_iff (st : Protocol.Store V) (r : Round) (c : CombinedAttestation V) :
    c ∈ st.sg_pool r ↔ c ∈ st.sg_votes r := by
  unfold Protocol.Store.sg_pool
  exact List.mem_toFinset

end DecoupledConsensusModel.Sts
