module
public import Model.Vocabulary.Objects.Blocks
public import Mathlib.Tactic.ToAdditive
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

@[expose] public section

/-!
# Height pairs

The height of a height pair.
-/

namespace DecoupledConsensusModel

namespace HeightPair

/-- The height of a height pair, `⊥` for the empty pair. -/
def height? : HeightPair → Option Height
  | .empty => none
  | .timeout height => some height
  | .target height _ => some height

end HeightPair

end DecoupledConsensusModel

end
