module
public import Proofs.Vocabulary.Protocol.ChainState.TimeoutBindingDefaults
public import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.NamedAttestations

@[expose] public section

/-!
# Facts about the targeted timeout binding

How `process_attestation_with` under the targeted binding updates `progress` and
`target_participation`.
-/
namespace DecoupledConsensusModel.Proofs.TargetedTimeoutBinding
open Protocol
variable {V : Type}


section Processing
variable [DecidableEq V]

/-- Under the targeted binding, a row enters `progress` when its height pair matches the entry
    `(h, T_h.root)`, and enters `target_participation` when it also is a proper target. -/
theorem process_height_fields (st : ChainState V) (row : NamedAttestation V) :
    (process_attestation_with (TimeoutBinding.targeted V) st row).progress =
      (if row.height_pair.matchesEntry st.h st.T_h.root then insert row.val_index st.progress
        else st.progress) ∧
    (process_attestation_with (TimeoutBinding.targeted V) st row).target_participation =
      (if row.height_pair.matchesEntry st.h st.T_h.root && row.height_pair.properTarget then
        insert row.val_index st.target_participation else st.target_participation) := by
  cases hp : row.height_pair with
  | empty =>
    simp [process_attestation_with, TimeoutBinding.targeted, TimeoutBinding.view,
      TimeoutBinding.targetedHeightPair, NamedAttestation.erase, NamedHeightPair.matchesEntry,
      NamedHeightPair.erase, NamedHeightPair.properTarget, hp,
      Protocol.process_attestation_progress, Protocol.process_attestation_target_participation]
  | vote h entry timeout =>
    by_cases hm : h = st.h ∧ entry = st.T_h.root
    · rcases hm with ⟨rfl, rfl⟩
      cases timeout <;>
        simp [process_attestation_with, TimeoutBinding.targeted, TimeoutBinding.view,
          TimeoutBinding.targetedHeightPair, NamedAttestation.erase, NamedHeightPair.matchesEntry,
          NamedHeightPair.erase, NamedHeightPair.properTarget, hp,
          Protocol.process_attestation_progress, Protocol.process_attestation_target_participation]
    · cases timeout <;>
        simp [process_attestation_with, TimeoutBinding.targeted, TimeoutBinding.view,
          TimeoutBinding.targetedHeightPair, NamedAttestation.erase, NamedHeightPair.matchesEntry,
          NamedHeightPair.erase, NamedHeightPair.properTarget, hp, hm,
          Protocol.process_attestation_progress, Protocol.process_attestation_target_participation]

theorem process_finality_eq (st : ChainState V) (row : NamedAttestation V) :
    (process_attestation_with (TimeoutBinding.targeted V) st row).finalize =
      (process_attestation st row.erase).finalize :=
  TimeoutBindingDefaults.process_finality_eq_base (TimeoutBinding.targeted V) st row


end Processing


#print axioms process_height_fields
#print axioms process_finality_eq
end DecoupledConsensusModel.Proofs.TargetedTimeoutBinding

end
