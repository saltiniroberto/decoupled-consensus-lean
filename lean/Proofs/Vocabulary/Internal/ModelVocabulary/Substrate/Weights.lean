module
public import Model.Vocabulary.Objects.Weights
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

@[expose] public section

/-!
# Quorums

The quorum predicate on validator sets.
-/

namespace DecoupledConsensusModel
namespace Electorate

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A quorum is a validator set of total weight at least the finality threshold. -/
def IsQuorum (E : Electorate V) (S : Finset V) : Prop :=
  E.finalityThreshold ≤ E.weightOf S

end Electorate
end DecoupledConsensusModel

end
