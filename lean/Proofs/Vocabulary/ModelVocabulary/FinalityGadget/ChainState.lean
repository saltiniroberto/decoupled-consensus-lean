module
public import Model.Vocabulary.Protocol.ChainState
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

@[expose] public section

/-!
# Lower bounds on the height constants

The bounds `K ≥ 3`, `K ≥ 2` and `D ≥ 1` on a height configuration, consequences of `K ≥ 4` and
`D ≥ 2`.
-/

namespace DecoupledConsensusModel

namespace Protocol

namespace HeightConfig


/-- `K ≥ 3`, a consequence of `K ≥ 4`. -/
theorem K_ge_three (cfg : HeightConfig) : 3 ≤ cfg.K :=
  Nat.le_of_succ_le cfg.K_ge_four

/-- `K ≥ 2`, a consequence of `K ≥ 3`. -/
theorem K_ge_two (cfg : HeightConfig) : 2 ≤ cfg.K :=
  Nat.le_of_succ_le cfg.K_ge_three

/-- `D ≥ 1`, a consequence of `D ≥ 2`. -/
theorem D_ge_one (cfg : HeightConfig) : 1 ≤ cfg.D :=
  Nat.le_of_succ_le cfg.D_ge_two

end HeightConfig

namespace ChainState

variable {V : Type}

variable [DecidableEq V] [Fintype V]

end ChainState

end Protocol

end DecoupledConsensusModel

end
