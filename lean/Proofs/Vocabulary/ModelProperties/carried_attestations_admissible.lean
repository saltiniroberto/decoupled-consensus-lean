module
public import Model.Vocabulary.Protocol.Handlers

@[expose] public section

/-!
# Facts about `Protocol.carried_attestations_admissible`

The receiver's round test on the attestations a block carries.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type}

/-- The test `carried_attestations_admissible hc B` is `true` exactly when every attestation `B`
    carries has a round at most the round of `B`'s slot. -/
theorem carried_attestations_admissible_eq_true_iff (hc : Protocol.HealConfig) (B : Block V) :
    Protocol.carried_attestations_admissible hc B = true ↔
      ∀ a ∈ B.attestations, a.round ≤ hc.round_of B.slot := by
  unfold Protocol.carried_attestations_admissible
  simp only [List.all_eq_true, decide_eq_true_eq]

end DecoupledConsensusModel.Proofs.ModelProperties

end
