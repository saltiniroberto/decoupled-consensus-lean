import Model.Vocabulary.Protocol.Handlers
import Proofs.Claims.ModelIrreducible

/-!
# The admission of a block's attestations

The store `admit_carried` returns is either the store obtained by admitting the block's
attestations, or the store it was given.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedAdmission.admit_carried

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- The store `admit_carried` returns is either `admit_rows hc after B.attestations`, the store
    obtained by admitting `B`'s attestations one by one from `after`, or `after` itself. -/
theorem admit_carried_cases (admission : Protocol.CarriedAdmission) (hc : Protocol.HealConfig)
    (before after : Protocol.NamedStore V) (B : NamedBlock V) :
    Protocol.NamedAdmission.admit_carried admission hc before after B =
        Protocol.NamedAdmission.admit_rows hc after B.attestations ∨
      Protocol.NamedAdmission.admit_carried admission hc before after B = after := by
  unfold Protocol.NamedAdmission.admit_carried
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

end DecoupledConsensusModel.Sts
