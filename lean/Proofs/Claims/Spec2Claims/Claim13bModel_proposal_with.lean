module
public import Model.Vocabulary.Protocol.Duties.Proposals
public import Proofs.Claims.ModelIrreducible
public import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.NamedBlocks

@[expose] public section

/-!
# Facts about `Protocol.NamedActions.proposal_with`

Lemmas that unfold the block a proposal duty builds, read through the votes the block includes.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.NamedBlock.gf_votes
  DecoupledConsensusModel.Protocol.NamedActions.parentBody?
  DecoupledConsensusModel.Protocol.NamedActions.proposal_with
  DecoupledConsensusModel.Protocol.Store.toHealing
  DecoupledConsensusModel.Protocol.get_head_in_tree_with_layer
  DecoupledConsensusModel.Protocol.get_head_with
  DecoupledConsensusModel.Protocol.proposer_support_view
  DecoupledConsensusModel.Protocol.proposer_view
  DecoupledConsensusModel.Protocol.with_proposal_input

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the named proposal read under `contract`, with the row source `source`, builds the block `B`
    at the named store `st`, then every support vote `B` includes is among the Goldfish votes `B`
    includes. -/
theorem proposal_with_gf_support_subset (contract : Protocol.GradeContract V)
    (source : Protocol.ProposalRowSource) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) {B : NamedBlock V}
    (h : Protocol.NamedActions.proposal_with contract source E hc nd st = some B) :
    ∀ u ∈ B.gf_support_votes, u ∈ B.gf_votes := by
  simp only [Protocol.NamedActions.proposal_with, Protocol.with_proposal_input,
    Option.map_eq_some_iff] at h
  obtain ⟨parent, -, hBeq⟩ := h
  rw [← hBeq]
  intro u hu
  exact (List.mem_filter.mp hu).1

end DecoupledConsensusModel.Sts
