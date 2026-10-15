module
public import Proofs.Vocabulary.ModelVocabulary.Substrate.Weights
public import Model.Vocabulary.Objects.Parameters
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

@[expose] public section

/-!
# The strict-majority threshold of an environment

The threshold `m = ⌊W/2⌋ + 1` of an environment's electorate.
-/

namespace DecoupledConsensusModel

namespace Env

variable {V : Type} [DecidableEq V] [Fintype V] (E : Env V)

/-- The strict-majority threshold `m = ⌊W/2⌋ + 1` of the environment's electorate. -/
def m : Nat :=
  E.electorate.strictMajorityThreshold

end Env

end DecoupledConsensusModel

end
