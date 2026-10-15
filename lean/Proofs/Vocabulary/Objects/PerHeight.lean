module
public import Proofs.Vocabulary.Internal.HealingSurface
public import Proofs.Vocabulary.Internal.Legacy.Assumptions.Weight
import Proofs.Vocabulary.Objects.Weights
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Quorum threshold arithmetic

The bound `2W ≤ 3q` for the quorum threshold `q = ⌈2W/3⌉`.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The quorum threshold `q = ⌈2W/3⌉` satisfies `2W ≤ 3q`. -/
theorem two_mul_W_le_three_mul_q (E : Env V) : 2 * E.W ≤ 3 * E.q := by
  unfold Env.q Env.W Electorate.finalityThreshold Electorate.totalWeight
  omega

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
