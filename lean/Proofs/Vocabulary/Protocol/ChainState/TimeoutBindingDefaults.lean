module
public import Proofs.Vocabulary.Protocol.ChainState.Chain

@[expose] public section

/-!
# Facts about timeout bindings

The fields `process_attestation_with` keeps under any timeout binding, and its finality processing.
-/
namespace DecoupledConsensusModel.Proofs.TimeoutBindingDefaults
open Protocol


section Processing
variable {V Row : Type} [DecidableEq V]


/-- Under any binding, `finalize` after `process_attestation_with` is `finalize` after
    `process_attestation` on the row's base attestation. -/
theorem process_finality_eq_base (binding : TimeoutBinding V Row)
    (st : ChainState V) (row : Row) :
    (process_attestation_with binding st row).finalize =
      (process_attestation st (binding.base row)).finalize := by
  simp only [process_attestation_with, Protocol.process_attestation_finalize, TimeoutBinding.view]

/-- Under any binding, `process_attestation_with` keeps `L`, `h`, `T_h`, `J`, `h_j`, `F` and `h_F`. -/
theorem process_context_fields (binding : TimeoutBinding V Row)
    (st : ChainState V) (row : Row) :
    (process_attestation_with binding st row).L = st.L ∧
    (process_attestation_with binding st row).h = st.h ∧
    (process_attestation_with binding st row).T_h = st.T_h ∧
    (process_attestation_with binding st row).J = st.J ∧
    (process_attestation_with binding st row).h_j = st.h_j ∧
    (process_attestation_with binding st row).F = st.F ∧
    (process_attestation_with binding st row).h_F = st.h_F :=
  Protocol.process_attestation_fields st (binding.view st row)


end Processing

#print axioms process_finality_eq_base
#print axioms process_context_fields
end DecoupledConsensusModel.Proofs.TimeoutBindingDefaults

end
