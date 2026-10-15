module
public import Model.Vocabulary.Protocol.ValidatorClient

@[expose] public section

/-!
# Facts about `Protocol.own_lock`

The lock a validator holds at a height after its own finality pair.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

/-- After a finality pair of height `h` and target `J`, the validator's lock at height `h` is `J`. -/
theorem own_lock_some_self (Λ : Protocol.Record) (h : Height) (J : BlockId) :
    Protocol.own_lock Λ h (some ⟨h, J⟩) = some J := by
  simp [Protocol.own_lock]

end DecoupledConsensusModel.Proofs.ModelProperties

end
