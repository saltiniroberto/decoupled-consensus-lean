module
public import Proofs.Vocabulary.Internal.Definitions.Evidence
public import Proofs.Vocabulary.Internal.ModelVocabulary.Goldfish.Store
public import Proofs.Vocabulary.Internal.ModelVocabulary.Protocol.Store

@[expose] public section

/-!
# Store predicates

Predicates on store fields.
-/

namespace DecoupledConsensusModel
namespace Internal

open Protocol (HeightConfig)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The processed tree is parent closed. -/
def ParentClosed (st : Protocol.Store V) : Prop :=
  Protocol.GoldfishStore.parent_closed st.toHealing.toFG.toSG.toGoldfishStore

end Internal
end DecoupledConsensusModel

end
