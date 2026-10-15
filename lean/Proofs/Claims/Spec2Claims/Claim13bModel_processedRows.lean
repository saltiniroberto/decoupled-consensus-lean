import Model.Vocabulary.Protocol.Duties.Proposals
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.NamedProposalRows.processedRows`

A lemma that unfolds the rows a proposer has processed, its SG rows of every round up to its store's
round.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedProposalRows.processedRows

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type}

/-- A processed row of the named store `st` is among `st`'s SG rows of some round. -/
theorem exists_sg_rows_of_mem_processedRows (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) {a : NamedAttestation V}
    (h : a ∈ Protocol.NamedProposalRows.processedRows hc st) :
    ∃ k : Round, a ∈ st.sg_rows k := by
  unfold Protocol.NamedProposalRows.processedRows at h
  obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp h
  exact ⟨k, hk⟩

end DecoupledConsensusModel.Sts
