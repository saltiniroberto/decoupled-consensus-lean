module
public import Model.Vocabulary.Protocol.Duties.Proposals

@[expose] public section

/-!
# Facts about `Protocol.NamedActions.proposal_with`: the slot

The slot of the block the named proposal duty returns. This file imports the model alone.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the proposal duty under `contract` returns `B` at `st`, the slot of `B` is the slot of `st`'s
    core store. -/
theorem proposal_with_slot (contract : Protocol.GradeContract V)
    (source : Protocol.ProposalRowSource) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (h : Protocol.NamedActions.proposal_with contract source E hc nd st = some B) :
    B.slot = st.core.s := by
  unfold Protocol.NamedActions.proposal_with Protocol.with_proposal_input at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨p, -, hBeq⟩ := h
  rw [← hBeq]
  rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
