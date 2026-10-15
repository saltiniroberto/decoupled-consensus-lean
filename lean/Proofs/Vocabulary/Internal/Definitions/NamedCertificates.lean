module
public import Proofs.Vocabulary.Internal.ModelVocabulary.FinalityGadget.Crossing

@[expose] public section

/-!
# Named chain attestations

The named attestations included in the blocks of a chain.
-/


namespace DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The named attestations included in the blocks of a chain. -/
def named_chain_attestations : NamedBlock V → Finset (NamedAttestation V)
  | .genesis => ∅
  | .node p _ _ _ _ ats _ => named_chain_attestations p ∪ ats.toFinset


end DecoupledConsensusModel.Protocol

end
