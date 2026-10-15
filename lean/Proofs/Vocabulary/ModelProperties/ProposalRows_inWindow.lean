module
public import Model.Vocabulary.Protocol.Duties.Proposals

@[expose] public section

/-!
# Facts about `Protocol.ProposalRows.inWindow`

Whether a round lies in a proposer's SG admission window.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type}

/-- The round `r` is in the SG admission window of `st` exactly when it is from the round of `st`'s
    slot minus `η_SG` to the round of `st`'s slot. -/
theorem inWindow_eq_true_iff (hc : Protocol.HealConfig) (st : Protocol.Store V) (r : Round) :
    Protocol.ProposalRows.inWindow hc st r = true ↔
      hc.round_of st.s - hc.η_SG ≤ r ∧ r ≤ hc.round_of st.s := by
  unfold Protocol.ProposalRows.inWindow
  exact decide_eq_true_iff

end DecoupledConsensusModel.Proofs.ModelProperties

end
