module
public import Model.Vocabulary.Protocol.Duties.Proposals

@[expose] public section

/-!
# Facts about the named round action

Facts about `Protocol.NamedActions.round_action_with`, each reading one field of the row it returns.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The row the named round action returns at `st` names the validator of the node `nd`. -/
theorem round_action_with_val_index (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.HealingStore V)
    (record : Protocol.NamedRecord) :
    (Protocol.NamedActions.round_action_with contract E hc nd st record).2.val_index =
      nd.val_index := rfl

/-- The row the named round action returns at `st` is for the round of `st`'s slot. -/
theorem round_action_with_round (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.HealingStore V)
    (record : Protocol.NamedRecord) :
    (Protocol.NamedActions.round_action_with contract E hc nd st record).2.round =
      hc.round_of st.s := rfl

/-- The confirmed root of the row the named round action returns at `st` is the root of the SG vote
    the contract selects at `st` for the round of `st`'s slot, using the contract's grade-2
    candidate. -/
theorem round_action_with_confirmed (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.HealingStore V)
    (record : Protocol.NamedRecord) :
    (Protocol.NamedActions.round_action_with contract E hc nd st record).2.confirmed =
      some (Protocol.get_sg_vote_with contract E hc st (hc.round_of st.s)
        (Protocol.grade2_block_with contract E hc st (hc.round_of st.s))).root := rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
