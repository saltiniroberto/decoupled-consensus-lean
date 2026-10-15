module
public import Model.Vocabulary.Protocol.Evidence

@[expose] public section

/-!
# Facts about `HasSlashableWeightBetween`

Slashable weight between two evidence sets, introduced and eliminated through a carrying set of
validators.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the validators of `Q` have intersection weight and each is slashable between `A₁` and `A₂`,
    then `A₁` and `A₂` carry slashable weight. -/
theorem hasSlashableWeightBetween_intro {E : Env V} {A₁ A₂ : Finset (CombinedAttestation V)}
    (Q : Finset V) (hQ : HasIntersectionWeight E Q) (h : ∀ i ∈ Q, SlashableBetween A₁ A₂ i) :
    HasSlashableWeightBetween E A₁ A₂ :=
  ⟨Q, hQ, h⟩

/-- If `A₁` and `A₂` carry slashable weight, some set `Q` of intersection weight has each of its
    validators slashable between them. -/
theorem hasSlashableWeightBetween_elim {E : Env V} {A₁ A₂ : Finset (CombinedAttestation V)}
    (h : HasSlashableWeightBetween E A₁ A₂) :
    ∃ Q : Finset V, HasIntersectionWeight E Q ∧ ∀ i ∈ Q, SlashableBetween A₁ A₂ i := h

end DecoupledConsensusModel.Proofs.ModelProperties

end
