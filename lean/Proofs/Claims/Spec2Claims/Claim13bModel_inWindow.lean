import Model.Vocabulary.Protocol.Duties.Proposals
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.ProposalRows.inWindow`

A lemma that unfolds the row window of a proposal.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.ProposalRows.inWindow

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type}

/-- Round `r` is in the row window of a store exactly when it lies between the store's round minus
    `η_SG` and the store's round. -/
theorem inWindow_iff (hc : Protocol.HealConfig) (st : Protocol.Store V) (r : Round) :
    Protocol.ProposalRows.inWindow hc st r = true ↔
      hc.round_of st.s - hc.η_SG ≤ r ∧ r ≤ hc.round_of st.s := by
  unfold Protocol.ProposalRows.inWindow
  exact decide_eq_true_iff

end DecoupledConsensusModel.Sts
