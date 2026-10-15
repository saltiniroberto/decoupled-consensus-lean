import Model.Vocabulary.Protocol.Evidence
import Proofs.Claims.ModelIrreducible

/-!
# Slashable weight between two evidence sets

An introduction rule for `HasSlashableWeightBetween`.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.HasSlashableWeightBetween

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the validators of `Q` together have the weight of an intersection of two quorums, and every
    validator of `Q` is slashable between `A₁` and `A₂`, then the evidence sets `A₁` and `A₂` carry
    slashable weight. -/
theorem hasSlashableWeightBetween_intro {E : Env V} {A₁ A₂ : Finset (CombinedAttestation V)}
    (Q : Finset V) (hQ : HasIntersectionWeight E Q) (h : ∀ i ∈ Q, SlashableBetween A₁ A₂ i) :
    HasSlashableWeightBetween E A₁ A₂ :=
  ⟨Q, hQ, h⟩

end DecoupledConsensusModel.Sts
