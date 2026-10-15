module
public import Model.Vocabulary.Objects.NamedBlocks

@[expose] public section

/-!
# Facts about `NamedAttestation.erase`

The erasure of a named SG row to a combined attestation.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type}

/-- The validator of the erasure of `a` is the validator of `a`. -/
theorem erase_val_index (a : NamedAttestation V) : a.erase.val_index = a.val_index := rfl

/-- The round of the erasure of `a` is the round of `a`. -/
theorem erase_round (a : NamedAttestation V) : a.erase.round = a.round := rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
