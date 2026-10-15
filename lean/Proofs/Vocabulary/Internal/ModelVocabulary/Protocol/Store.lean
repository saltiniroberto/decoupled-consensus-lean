module
public import Model.Vocabulary.Protocol.Store

@[expose] public section

/-!
# The node store

The processed attestations of the store, as the proposal duty reads them.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (ChainState)
open Protocol (SGVote)

namespace Store

variable {V : Type} [DecidableEq V]

/-- The processed attestations of the store, by ascending round up to the round of `st.s`. -/
def processed_attestations (hc : Protocol.HealConfig) (st : Store V) :
    List (CombinedAttestation V) :=
  (List.range (hc.round_of st.s + 1)).flatMap st.sg_votes

end Store

end Protocol
end DecoupledConsensusModel

end
