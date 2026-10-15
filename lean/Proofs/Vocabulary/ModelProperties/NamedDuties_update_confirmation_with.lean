module
public import Model.Vocabulary.Protocol.Duties.Proposals
public import Model.Vocabulary.Execution.Node
public import Proofs.Vocabulary.Protocol.Handlers.ConfirmationMembership

@[expose] public section

/-!
# Facts about `Protocol.NamedDuties.update_confirmation_with`

The confirmation duty over a named store.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The core store the named confirmation duty returns is the core confirmation update of `st`'s
    core store, with the same arguments. -/
theorem named_update_confirmation_with_core (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) (s : Slot) :
    (Protocol.NamedDuties.update_confirmation_with contract E hc st s).core =
      Protocol.update_confirmation_with contract E hc st.core s := rfl

/-- The named confirmation duty keeps the bodies of `st`. -/
theorem named_update_confirmation_with_bodies (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) (s : Slot) :
    (Protocol.NamedDuties.update_confirmation_with contract E hc st s).bodies = st.bodies := rfl

/-- Under the grade contract of any cache `c`, the named confirmation duty keeps
    `NamedConfirmationMembership.Invariant`. -/
theorem invariant_update_gradeContract (c : DecoupledConsensusModel.Protocol.Cache V)
    (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (st : Protocol.NamedStore V) (s : Slot)
    (h : NamedConfirmationMembership.Invariant E cfg st) :
    NamedConfirmationMembership.Invariant E cfg
      (Protocol.NamedDuties.update_confirmation_with
        (Execution.NamedProfile.gradeContract c) E hc st s) :=
  NamedConfirmationMembership.invariant_update c E hc cfg st s h

end DecoupledConsensusModel.Proofs.ModelProperties

end
