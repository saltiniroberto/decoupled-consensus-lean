module
public import Model.Vocabulary.Protocol.Evidence

@[expose] public section

/-!
# Facts about a store's evidence

Facts about `store_attestations`, the attestations a store holds.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V]

/-- The attestation `a` is in the evidence of the store `st` exactly when some block `B` of `st`'s
    block tree has `a` among the attestations of `B`'s chain. -/
theorem mem_store_attestations_iff (st : Protocol.Store V) (a : CombinedAttestation V) :
    a ∈ store_attestations st ↔ ∃ B ∈ st.T, a ∈ chain_attestations B := by
  unfold store_attestations
  exact Finset.mem_biUnion

end DecoupledConsensusModel.Proofs.ModelProperties

end
