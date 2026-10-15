module
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `NamedReceipt.processed`

When the store has recorded a delivered block, Goldfish vote or attestation.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Execution.NamedReceipt.processed DecoupledConsensusModel.Protocol.Store.pool DecoupledConsensusModel.Protocol.NamedStore.initial DecoupledConsensusModel.Protocol.Store.init

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- A block is recorded exactly when the store holds its named body. -/
theorem processed_block_iff (st : NamedStore V) (B : NamedBlock V) :
    NamedReceipt.processed st (.block B) = true ↔ B ∈ st.bodies := by
  simp only [NamedReceipt.processed, decide_eq_true_eq]

omit [Fintype V] in
/-- A Goldfish vote is recorded exactly when it is in its slot's vote list. -/
theorem processed_gfVote_iff (st : NamedStore V) (u : GoldfishVote V) :
    NamedReceipt.processed st (.gfVote u) = true ↔ u ∈ st.core.gf_votes u.slot := by
  simp only [NamedReceipt.processed, decide_eq_true_eq, Store.pool, List.mem_toFinset]

omit [Fintype V] in
/-- An attestation is recorded exactly when it is among its round's named rows. -/
theorem processed_attest_iff (st : NamedStore V) (a : NamedAttestation V) :
    NamedReceipt.processed st (.attest a) = true ↔ a ∈ st.sg_rows a.round := by
  simp only [NamedReceipt.processed, decide_eq_true_eq]

end DecoupledConsensusModel.Sts
