module
public import Model.Vocabulary.Protocol.Store

@[expose] public section

/-!
# Facts about `Protocol.Store.sg_pool`

A round's processed SG attestations of a store, read as a set.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V]

/-- An attestation is in the SG pool of `st` at round `r` exactly when it is in the list
    `st.sg_votes r`. -/
theorem mem_sg_pool_iff (st : Protocol.Store V) (r : Round) (b : CombinedAttestation V) :
    b ∈ st.sg_pool r ↔ b ∈ st.sg_votes r := by
  unfold Protocol.Store.sg_pool
  exact List.mem_toFinset

end DecoupledConsensusModel.Proofs.ModelProperties

end
