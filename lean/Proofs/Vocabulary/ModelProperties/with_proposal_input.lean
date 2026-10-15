module
public import Model.Vocabulary.Protocol.Duties.Inputs

@[expose] public section

/-!
# Facts about the proposal input

Facts about `Protocol.with_proposal_input`, read field by field for the input itself (the
continuation `id`).
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The Goldfish votes of the proposal input built at `st` are the proposer's view of `st`'s
    Goldfish votes at `st`'s slot. -/
theorem with_proposal_input_id_gf_votes (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.HealingStore V) :
    (Protocol.with_proposal_input contract E hc nd st id).gf_votes =
      Protocol.proposer_view st.toFG.toSG.toGoldfishStore st.s := rfl

/-- The support votes of the proposal input built at `st` are the proposer's view of `st`'s support
    votes at `st`'s slot. -/
theorem with_proposal_input_id_gf_support_votes (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.HealingStore V) :
    (Protocol.with_proposal_input contract E hc nd st id).gf_support_votes =
      Protocol.proposer_support_view st.toFG.toSG.toGoldfishStore st.s := rfl

/-- The parent of the proposal input built at `st` is the head composed under `contract` at `st` for
    the slot before `st`'s slot, read with the proposer's views of `st`'s Goldfish votes and support
    votes. -/
theorem with_proposal_input_id_parent (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.HealingStore V) :
    (Protocol.with_proposal_input contract E hc nd st id).parent =
      Protocol.get_head_with contract E hc st
        (Protocol.proposer_view st.toFG.toSG.toGoldfishStore st.s).toFinset
        (Protocol.proposer_support_view st.toFG.toSG.toGoldfishStore st.s).toFinset
        (st.s - 1) := rfl

/-- The proposer of the proposal input built at `st` for the node `nd` is `nd`'s validator. -/
theorem with_proposal_input_id_proposer (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.HealingStore V) :
    (Protocol.with_proposal_input contract E hc nd st id).proposer = nd.val_index := rfl

/-- The proposal input built at `st` is for `st`'s slot. -/
theorem with_proposal_input_id_slot (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.HealingStore V) :
    (Protocol.with_proposal_input contract E hc nd st id).slot = st.s := rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
