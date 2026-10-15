module
public import Model.Vocabulary.Protocol.Duties.Proposals

@[expose] public section

/-!
# Facts about `Protocol.NamedDuties.attest_with`

The attestation duty over a named store, read through the row it returns.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The row the attestation duty returns at `st` with `record` is the row the named round action
    computes at `st`'s healing view with that record. -/
theorem attest_with_row (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    (Protocol.NamedDuties.attest_with contract E hc nd st record).2.2 =
      (Protocol.NamedActions.round_action_with contract E hc nd st.core.toHealing record).2 :=
  rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
