module
public import Model.Vocabulary.Objects.NamedBlocks
public import Mathlib.Tactic.ToAdditive
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

@[expose] public section

namespace DecoupledConsensusModel.NamedHeightPair

def properTarget : NamedHeightPair → Bool
  | .empty => false
  | .vote _ _ timeout => !timeout

end DecoupledConsensusModel.NamedHeightPair

end
