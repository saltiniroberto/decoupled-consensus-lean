module
public import Model.Vocabulary.Protocol.Duties.Proposals
public import Model.Vocabulary.Execution.Node
public import Proofs.Vocabulary.Protocol.Duties.Proposals.Actions

@[expose] public section

/-!
# Facts about `Protocol.NamedActions.proposal_with`

The named proposal duty under a grade contract, which builds the block on the retained body of the
selected parent.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the named store `st` satisfies `NamedStoreRoots.Invariant`, the proposal duty under the grade
    contract of any cache `c` returns some block at `st`. -/
theorem proposal_with_gradeContract_isSome (c : DecoupledConsensusModel.Protocol.Cache V)
    (source : Protocol.ProposalRowSource) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (h : Proofs.NamedStoreRoots.Invariant E cfg st) :
    ∃ B, Protocol.NamedActions.proposal_with (Execution.NamedProfile.gradeContract c) source E hc
      nd st = some B :=
  Proofs.NamedActions.runtime_proposal_some c source E hc cfg nd st h

/-- If the proposal duty returns `B` at `st`, then `B` has a named parent that erases to the parent
    of the proposal input built at `st`'s healing view. -/
theorem proposal_with_parent? (contract : Protocol.GradeContract V)
    (source : Protocol.ProposalRowSource) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (h : Protocol.NamedActions.proposal_with contract source E hc nd st = some B) :
    ∃ p : NamedBlock V, NamedBlock.parent? B = some p ∧
      p.erase = (Protocol.with_proposal_input contract E hc nd st.core.toHealing id).parent := by
  unfold Protocol.NamedActions.proposal_with Protocol.with_proposal_input at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨p, hp, hBeq⟩ := h
  exact ⟨p, by rw [← hBeq]; rfl, (Proofs.NamedActions.parent_body_spec _ _ p hp).2⟩

end DecoupledConsensusModel.Proofs.ModelProperties

end
