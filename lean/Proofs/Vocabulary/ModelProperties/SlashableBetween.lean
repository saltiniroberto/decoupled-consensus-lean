module
public import Model.Vocabulary.Protocol.Evidence

@[expose] public section

/-!
# Facts about `SlashableBetween`

A validator slashable between two evidence sets.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V]

/-- If `a ∈ A₁` and `b ∈ A₂` are attestations of `i` and are slashable together, then `i` is
    slashable between `A₁` and `A₂`. -/
theorem slashableBetween_intro {A₁ A₂ : Finset (CombinedAttestation V)} {i : V}
    (a : CombinedAttestation V) (ha : a ∈ A₁) (b : CombinedAttestation V) (hb : b ∈ A₂)
    (hai : a.val_index = i) (hbi : b.val_index = i) (hab : Protocol.Slashable a b) :
    SlashableBetween A₁ A₂ i :=
  ⟨a, ha, b, hb, hai, hbi, hab⟩

/-- If `i` is slashable between `A₁` and `A₂`, some `a ∈ A₁` and `b ∈ A₂` are attestations of `i`
    and are slashable together. -/
theorem slashableBetween_elim {A₁ A₂ : Finset (CombinedAttestation V)} {i : V}
    (h : SlashableBetween A₁ A₂ i) :
    ∃ a ∈ A₁, ∃ b ∈ A₂, a.val_index = i ∧ b.val_index = i ∧ Protocol.Slashable a b := h

end DecoupledConsensusModel.Proofs.ModelProperties

end
