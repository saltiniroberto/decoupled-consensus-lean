module
public import Proofs.Vocabulary.Internal.Definitions.Evidence
public import Proofs.Vocabulary.Internal.ModelVocabulary.FGForkChoice.Finality

@[expose] public section

/-!
# Store-finality properties

The predicate `JustificationBelowMax` on a store.
-/

namespace DecoupledConsensusModel
namespace Internal

open Protocol (HeightConfig)

variable {V : Type} [DecidableEq V] [Fintype V]


/-- The store's justified height is less than its maximum chain-state height. -/
def JustificationBelowMax (st : Protocol.Store V) : Prop :=
  st.h_j < st.h_max

end Internal
end DecoupledConsensusModel

end
