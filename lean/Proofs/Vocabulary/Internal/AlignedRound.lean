module
public import Proofs.Vocabulary.Internal.Execution.Assumptions
public import Proofs.Vocabulary.Internal.ModelVocabulary.Protocol.NamedStoreReads

@[expose] public section

/-!
# Targets carried by an attestation

The set `targetsAt a h` of the nonempty targets an attestation carries at height `h`.
-/


namespace DecoupledConsensusModel
namespace Internal

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The nonempty targets an attestation carries at height `h`, in its height pair or its finality
    pair. -/
def targetsAt (a : CombinedAttestation V) (h : Height) : Set BlockId :=
  {T | a.height_pair = HeightPair.target h T} ∪
    {T | a.finality_pair = some ⟨h, T⟩}


end Internal
end DecoupledConsensusModel

end
