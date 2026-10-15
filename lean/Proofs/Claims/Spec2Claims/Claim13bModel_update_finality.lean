module
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.update_finality`

Lemmas that unfold the finality update of the core store.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.update_finality

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- The finality update leaves the erased tree alone. -/
theorem update_finality_T (st : Store V) (σ : ChainState V) :
    (update_finality st σ).T = st.T := by
  simp only [update_finality]; split <;> split <;> rfl

omit [Fintype V] in
/-- The finality update leaves the slot vote lists alone. -/
theorem update_finality_gf_votes (st : Store V) (σ : ChainState V) :
    (update_finality st σ).gf_votes = st.gf_votes := by
  simp only [update_finality]; split <;> split <;> rfl

omit [Fintype V] in
/-- The finality update leaves the attestation lists alone. -/
theorem update_finality_sg_votes (st : Store V) (σ : ChainState V) :
    (update_finality st σ).sg_votes = st.sg_votes := by
  simp only [update_finality]; split <;> split <;> rfl

end DecoupledConsensusModel.Sts
