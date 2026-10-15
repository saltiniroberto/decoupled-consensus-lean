module
public import Model.Vocabulary.Objects.Blocks
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

@[expose] public section

namespace DecoupledConsensusModel.Block

variable {V : Type} [DecidableEq V]

/-- Two blocks conflict when neither is an ancestor of the other. -/
def conflicts (B C : Block V) : Bool :=
  !compatible B C

end DecoupledConsensusModel.Block

end
