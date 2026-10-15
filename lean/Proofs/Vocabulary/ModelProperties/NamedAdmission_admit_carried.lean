module
public import Model.Vocabulary.Protocol.Handlers

@[expose] public section

/-!
# Facts about `Protocol.NamedAdmission.admit_carried`

The admission of carried rows after a block's core call, in the case where the block is newly held.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V]

/-- If `B` is not among the bodies of `before` and is among the bodies of `after`, the carried-row
    admission returns the store that admitting `B`'s rows one by one returns, started from `after`. -/
theorem admit_carried_of_new (admission : Protocol.CarriedAdmission) (hc : Protocol.HealConfig)
    {before after : Protocol.NamedStore V} {B : NamedBlock V}
    (hnew : B ∉ before.bodies) (hheld : B ∈ after.bodies) :
    Protocol.NamedAdmission.admit_carried admission hc before after B =
      Protocol.NamedAdmission.admit_rows hc after B.attestations := by
  unfold Protocol.NamedAdmission.admit_carried
  exact if_pos ⟨hnew, hheld⟩

end DecoupledConsensusModel.Proofs.ModelProperties

end
