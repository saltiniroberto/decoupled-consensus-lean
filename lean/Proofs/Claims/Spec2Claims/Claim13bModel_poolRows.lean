import Model.Vocabulary.Protocol.Duties.Proposals
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.NamedProposalRows.poolRows`

A lemma that unfolds the pool rows of a proposal, the processed rows whose round is in the row
window.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedProposalRows.poolRows

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type}

/-- A pool row of the named store `st` is among `st`'s processed rows. -/
theorem mem_processedRows_of_mem_poolRows (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) {a : NamedAttestation V}
    (h : a ∈ Protocol.NamedProposalRows.poolRows hc st) :
    a ∈ Protocol.NamedProposalRows.processedRows hc st := by
  unfold Protocol.NamedProposalRows.poolRows at h
  exact (List.mem_filter.mp h).1

end DecoupledConsensusModel.Sts
