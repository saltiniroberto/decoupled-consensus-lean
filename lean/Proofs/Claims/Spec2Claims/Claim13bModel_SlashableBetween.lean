import Model.Vocabulary.Protocol.Evidence
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `SlashableBetween`

The slashability of a validator between two evidence sets.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.SlashableBetween

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If `a ∈ A₁` and `b ∈ A₂` are attestations of the validator `i` and are slashable together, then
    `i` is slashable between `A₁` and `A₂`. -/
theorem slashableBetween_intro {A₁ A₂ : Finset (CombinedAttestation V)} {i : V}
    (a : CombinedAttestation V) (ha : a ∈ A₁) (b : CombinedAttestation V) (hb : b ∈ A₂)
    (hai : a.val_index = i) (hbi : b.val_index = i) (hab : Protocol.Slashable a b) :
    SlashableBetween A₁ A₂ i :=
  ⟨a, ha, b, hb, hai, hbi, hab⟩

end DecoupledConsensusModel.Sts
