module

public import Model.Vocabulary.Protocol.Store
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.sgVote`

Lemmas that unfold the SG vote an attestation carries: its validator, its round and its confirmed
block.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.NamedAttestation.erase
  DecoupledConsensusModel.Protocol.sgVote

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type}

/-- If the attestations `A` and `A'` have the same validator, the same round and the same confirmed
    block, then `Protocol.sgVote A = Protocol.sgVote A'`. -/
theorem sgVote_eq_of_fields {A A' : CombinedAttestation V} (h₁ : A.val_index = A'.val_index)
    (h₂ : A.round = A'.round) (h₃ : A.confirmed = A'.confirmed) :
    Protocol.sgVote A = Protocol.sgVote A' := by
  unfold Protocol.sgVote
  rw [h₁, h₂, h₃]

/-- The round of `Protocol.sgVote A` is the round of `A`. -/
theorem sgVote_round_eq_round (A : CombinedAttestation V) : (Protocol.sgVote A).round = A.round :=
  rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type}

/-- The validator of `Protocol.sgVote A` is the validator of `A`. -/
theorem sgVote_val_index_eq_val_index (A : CombinedAttestation V) :
    (Protocol.sgVote A).val_index = A.val_index :=
  rfl


end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type}


end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type}


/-- If the named attestations `a` and `b` have the same validator, the same round and the same
    confirmed block, then `Protocol.sgVote a.erase = Protocol.sgVote b.erase`. -/
theorem sgVote_erase_eq_of_fields {a b : NamedAttestation V} (h₁ : a.val_index = b.val_index)
    (h₂ : a.round = b.round) (h₃ : a.confirmed = b.confirmed) :
    Protocol.sgVote a.erase = Protocol.sgVote b.erase := by
  unfold Protocol.sgVote NamedAttestation.erase
  rw [h₁, h₂, h₃]

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type}


/-- The confirmed block of `Protocol.sgVote A` is the confirmed block of `A`. -/
theorem sgVote_confirmed_eq (A : CombinedAttestation V) :
    (Protocol.sgVote A).confirmed = A.confirmed := rfl

end DecoupledConsensusModel.Sts
