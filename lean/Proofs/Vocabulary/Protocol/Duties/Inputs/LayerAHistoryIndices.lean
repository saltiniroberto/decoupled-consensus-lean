module
public import Proofs.Vocabulary.Internal.Definitions.NamedOutageEntry
public import Proofs.Vocabulary.Internal.ModelVocabulary.Healing.Action

@[expose] public section

/-!
# Event-index boundaries

`boundaryIdx`, the number of events of a run timed at most `t`.
-/


namespace DecoupledConsensusModel.Internal.NamedOutageEntry.History
open Execution Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The number of events of `rho` timed at most `t`, a prefix of the sorted event list. -/
def boundaryIdx (rho : NamedRun V) (t : Time) : Nat :=
  (rho.events.filter fun e => decide (e.time ≤ t)).length


end DecoupledConsensusModel.Internal.NamedOutageEntry.History

end
