module
public import Model.Vocabulary.Objects.Weights
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

@[expose] public section

/-!
# The strict-majority threshold of an electorate

The threshold `⌊W/2⌋ + 1` of an electorate's total weight `W`.
-/

open scoped BigOperators

namespace DecoupledConsensusModel

namespace Electorate

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The strict-majority threshold `⌊W/2⌋ + 1` of the electorate's total weight `W`. -/
def strictMajorityThreshold (E : Electorate V) : Nat :=
  E.totalWeight / 2 + 1

end Electorate

end DecoupledConsensusModel

end
