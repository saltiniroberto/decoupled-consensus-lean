module
public import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.Weights
public import Model.Vocabulary.Protocol.Store

@[expose] public section

/-!
# Committee-pool invariant

The predicate `CommitteePools` on a store.
-/

namespace DecoupledConsensusModel

namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

end Protocol

namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

def CommitteePools (E : Env V) (st : Protocol.Store V) : Prop :=
  ∀ (k : Slot) (u : GoldfishVote V), u ∈ st.gf_votes k →
    u.val_index ∈ E.committee k

end Protocol

end DecoupledConsensusModel

end
