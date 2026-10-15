import Model.Vocabulary.Protocol.Duties.Proposals
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.NamedProposalRows.select`

A lemma that unfolds the rows a proposal selects, through its pool rows.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedProposalRows.poolRows
  DecoupledConsensusModel.Protocol.NamedProposalRows.processedRows
  DecoupledConsensusModel.Protocol.NamedProposalRows.select

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- A row among a store's processed rows whose round is in the store's row window is among the rows
    a proposal on that store selects, from either row source. -/
theorem mem_select_of_processed_inWindow (source : Protocol.ProposalRowSource)
    (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) {a : NamedAttestation V}
    (hproc : a ∈ Protocol.NamedProposalRows.processedRows hc st)
    (hw : Protocol.ProposalRows.inWindow hc st.core a.round = true) :
    a ∈ Protocol.NamedProposalRows.select source hc st := by
  apply List.mem_append_left
  simp only [Protocol.NamedProposalRows.poolRows, List.mem_filter]
  exact ⟨hproc, hw⟩

end DecoupledConsensusModel.Sts
