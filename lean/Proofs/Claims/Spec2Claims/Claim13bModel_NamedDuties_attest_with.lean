import Model.Vocabulary.Protocol.Duties.Proposals
import Proofs.Claims.ModelIrreducible
import Proofs.Claims.Spec2Claims.Claim13bModel_on_sg_vote
import Proofs.Vocabulary.Protocol.Handlers.Execution

/-!
# Facts about `NamedDuties.attest_with`

The lemmas that unfold the attestation duty on a named store, `NamedDuties.attest_with`: the
attestation it signs and the store it returns.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.root
  DecoupledConsensusModel.Protocol.NamedActions.creatorInput
  DecoupledConsensusModel.Protocol.NamedActions.round_action_with
  DecoupledConsensusModel.Protocol.NamedDuties.attest_with
  DecoupledConsensusModel.Protocol.NamedRecord.create
  DecoupledConsensusModel.Protocol.NamedRecord.encodeRow
  DecoupledConsensusModel.Protocol.NamedRecord.legacyCreate
  DecoupledConsensusModel.Protocol.create_attestation
  DecoupledConsensusModel.Protocol.get_sg_vote_with
  DecoupledConsensusModel.Protocol.grade2_block_with
  DecoupledConsensusModel.Protocol.with_attestation_input

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The `confirmed` field of the attestation `attest_with` returns on `st` is the root of the block
    the contract's SG vote picks at `st`'s healing view, at the round of `st`'s slot. -/
theorem namedDuties_attest_with_confirmed (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    (Protocol.NamedDuties.attest_with contract E hc nd st record).2.2.confirmed
      = some (contract.sgVote st.core.toHealing
          (contract.read E hc st.core.toHealing (hc.round_of st.core.toHealing.s))).root := rfl

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The named store the attestation duty returns on `st` is the store `admit_row` returns when it
    admits, into `st`, the named row the same duty returns. -/
theorem namedDuties_attest_with_fst (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    (Protocol.NamedDuties.attest_with contract E hc nd st record).1 =
      Protocol.NamedAdmission.admit_row hc st
        (Protocol.NamedDuties.attest_with contract E hc nd st record).2.2 :=
  rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]
/-- The named store the attestation duty returns on `st` is the row admission, into `st`, of the
    attestation the round action builds on `st`'s healing view and the record `record`. -/
theorem namedDuties_attest_with_fst_eq_round_action (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    (Protocol.NamedDuties.attest_with contract E hc nd st record).1
      = Protocol.NamedAdmission.admit_row hc st
          (Protocol.NamedActions.round_action_with contract E hc nd st.core.toHealing record).2 :=
  rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]


end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The store the attestation duty returns holds the `latest_stable` and the `latest_confirmed` of
    the store it was given. -/
theorem attest_with_records (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    (Protocol.NamedDuties.attest_with gc E hc nd st record).1.core.latest_stable
        = st.core.latest_stable ∧
      (Protocol.NamedDuties.attest_with gc E hc nd st record).1.core.latest_confirmed
        = st.core.latest_confirmed := by
  unfold Protocol.NamedDuties.attest_with
  show (Protocol.NamedAdmission.admit_row hc st _).core.latest_stable = _ ∧
    (Protocol.NamedAdmission.admit_row hc st _).core.latest_confirmed = _
  rw [admit_row_core]
  exact on_sg_vote_latest_records hc st.core _

end DecoupledConsensusModel.Sts
