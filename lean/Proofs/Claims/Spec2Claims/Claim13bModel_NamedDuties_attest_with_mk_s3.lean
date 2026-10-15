module
public import Model.Vocabulary.Protocol.Duties.Proposals
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# The attestation duty's store is a row admission

The store the named attestation duty `Protocol.NamedDuties.attest_with` returns, as the admission of
a named row.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedDuties.attest_with

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The named store the attestation duty returns is the admission of some named row into the store
    it was given. -/
theorem namedDuties_attest_with_fst_exists_row (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    ∃ row : NamedAttestation V,
      (Protocol.NamedDuties.attest_with contract E hc nd st record).1
        = Protocol.NamedAdmission.admit_row hc st row :=
  ⟨_, rfl⟩

end DecoupledConsensusModel.Sts
