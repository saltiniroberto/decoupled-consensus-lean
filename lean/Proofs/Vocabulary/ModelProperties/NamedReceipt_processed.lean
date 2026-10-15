module
public import Model.Vocabulary.Execution.Node

@[expose] public section

/-!
# Facts about `Execution.NamedReceipt.processed`

Whether a named store has processed an object.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A block is processed exactly when it is among the store's bodies. -/
theorem processed_block_eq_true_iff (st : Protocol.NamedStore V) (B : NamedBlock V) :
    NamedReceipt.processed st (.block B) = true ↔ B ∈ st.bodies := by
  simp [NamedReceipt.processed]

/-- A block is unprocessed exactly when it is not among the store's bodies. -/
theorem processed_block_eq_false_iff (st : Protocol.NamedStore V) (B : NamedBlock V) :
    NamedReceipt.processed st (.block B) = false ↔ B ∉ st.bodies := by
  simp [NamedReceipt.processed]

/-- An SG row is processed exactly when the store holds it among the SG rows of its round. -/
theorem processed_attest_eq_true_iff (st : Protocol.NamedStore V) (a : NamedAttestation V) :
    NamedReceipt.processed st (.attest a) = true ↔ a ∈ st.sg_rows a.round := by
  simp [NamedReceipt.processed]

/-- An SG row is unprocessed exactly when the store does not hold it among the SG rows of its round. -/
theorem processed_attest_eq_false_iff (st : Protocol.NamedStore V) (a : NamedAttestation V) :
    NamedReceipt.processed st (.attest a) = false ↔ a ∉ st.sg_rows a.round := by
  simp [NamedReceipt.processed]

/-- A Goldfish vote is processed exactly when it is in the pool of its slot. -/
theorem processed_gfVote_eq_true_iff (st : Protocol.NamedStore V) (u : GoldfishVote V) :
    NamedReceipt.processed st (.gfVote u) = true ↔ u ∈ st.core.pool u.slot := by
  simp [NamedReceipt.processed]

/-- A Goldfish vote is unprocessed exactly when it is not in the pool of its slot. -/
theorem processed_gfVote_eq_false_iff (st : Protocol.NamedStore V) (u : GoldfishVote V) :
    NamedReceipt.processed st (.gfVote u) = false ↔ u ∉ st.core.pool u.slot := by
  simp [NamedReceipt.processed]

end DecoupledConsensusModel.Proofs.ModelProperties

end
