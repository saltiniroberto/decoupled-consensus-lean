module
public import Model.Vocabulary.Execution.Run

@[expose] public section

open DecoupledConsensusModel
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

namespace DecoupledConsensusModel.Internal.NamedOutageEntry.History
variable {V : Type} [DecidableEq V] [Fintype V]

/-- `i` is at most the number of events of the run, and every event before index `i` has time at
    most `t`. -/
def PrefixThrough (rho : NamedRun V) (i : Nat) (t : Time) : Prop :=
  i ≤ rho.events.length ∧
    ∀ j : Nat, j < i → ∀ e : NamedEvent V,
      rho.events[j]? = some e → e.time ≤ t


end DecoupledConsensusModel.Internal.NamedOutageEntry.History

end
