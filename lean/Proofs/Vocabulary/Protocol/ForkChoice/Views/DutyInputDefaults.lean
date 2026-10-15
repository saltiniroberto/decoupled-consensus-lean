module
public import Proofs.Vocabulary.Internal.ModelVocabulary.Healing.Action

@[expose] public section

/-!
# Proposal input parent

The parent of a proposal input is the head computed from the proposer views.
-/
namespace DecoupledConsensusModel.Proofs.DutyInputDefaults
open Protocol
variable {V : Type} [DecidableEq V] [Fintype V]


/-- The parent of `proposal_input_with` is the head `get_head_with` computes from the proposer view
    and the proposer support view. -/
theorem proposal_input_parent (contract : GradeContract V) (E : Env V) (hc : HealConfig)
    (nd : Protocol.Node V) (st : HealingStore V) :
    (proposal_input_with contract E hc nd st).parent =
      get_head_with contract E hc st (Protocol.proposer_view st.toFG.toSG.toGoldfishStore st.s).toFinset
        (Protocol.proposer_support_view st.toFG.toSG.toGoldfishStore st.s).toFinset (st.s - 1) := rfl


#print axioms proposal_input_parent
end DecoupledConsensusModel.Proofs.DutyInputDefaults

end
