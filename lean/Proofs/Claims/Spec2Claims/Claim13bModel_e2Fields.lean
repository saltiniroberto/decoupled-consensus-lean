module
public import Model.Vocabulary.Protocol.ChainState
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.e2Fields`

The E2 field conflict between two attestations, before the one-signer test.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type}

section ChainStateBodies

attribute [local semireducible] Protocol.e2Fields

/-- If whenever both attestations carry a target vote at one height `h` the two targets are equal,
    then `e2Fields left right` is `false`. -/
theorem e2Fields_eq_false_of (left right : CombinedAttestation V)
    (hagree : ∀ (h : Height) (T U : BlockId), left.height_pair = .target h T →
      right.height_pair = .target h U → T = U) :
    Protocol.e2Fields left right = false := by
  unfold Protocol.e2Fields
  split
  · rename_i h₁ T h₂ U hl hr
    by_cases hh : h₁ = h₂
    · subst hh
      simp [hagree h₁ _ _ hl hr]
    · simp [hh]
  · rfl

end ChainStateBodies

end DecoupledConsensusModel.Sts
