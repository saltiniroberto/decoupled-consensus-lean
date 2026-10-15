module
public import Model.Vocabulary.Execution.Setup
public import Model.Vocabulary.Protocol.Store

@[expose] public section

/-!
# Latest SG inputs

The SG inputs of maximal round in a finite set.
-/


namespace DecoupledConsensusModel
namespace Internal.OutageEntryRevision
open Execution DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The inputs of maximal round in `inputs`, all kept when several share it. -/
def latest (inputs : Finset (Protocol.SGVote V)) : Finset (Protocol.SGVote V) :=
  inputs.filter (fun u => ∀ x ∈ inputs, x.round ≤ u.round)

end Internal.OutageEntryRevision
end DecoupledConsensusModel

end
