module
public import Model.Vocabulary.Statements.Instantiation.Certificates
public import Proofs.Vocabulary.Protocol.ChainState.NamedNjGap
public import Proofs.Vocabulary.Execution.BodyRetention
public import Mathlib.Order.Lattice.Nat
import Proofs.Vocabulary.Execution.Runtime
import Proofs.Vocabulary.ModelVocabulary.FinalityGadget.ChainState
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

/-!
# Bounded recovery heights

For any height `lower`, some recovery height lies between `lower + D + 1` and `lower + D + K`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (HeightConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


/-- For `hF ≤ lower`, some recovery height `blocked` for the baseline `hF` satisfies
    `lower + D + 1 ≤ blocked ≤ lower + D + K`. -/
theorem exists_recoveryHeight_between
    (cfg : HeightConfig) (hF lower : Height) (hhF : hF ≤ lower) :
    ∃ blocked : Height,
      lower + cfg.D + 1 ≤ blocked ∧
      blocked ≤ lower + cfg.D + cfg.K ∧
      NjGap.RecoveryHeight cfg hF blocked := by
  let base : Nat := lower + cfg.D
  let blocked : Nat := cfg.K * (base / cfg.K + 1)
  have hK : 0 < cfg.K :=
    lt_of_lt_of_le (by decide : 0 < 3) cfg.K_ge_three
  have hmod : base % cfg.K < cfg.K := Nat.mod_lt base hK
  have hlowerBase : base + 1 ≤ blocked := by
    calc
      base + 1 =
          (base % cfg.K + cfg.K * (base / cfg.K)) + 1 := by
            rw [Nat.mod_add_div]
      _ ≤ cfg.K * (base / cfg.K) + cfg.K := by omega
      _ = blocked := by simp [blocked, Nat.mul_add]
  have hupperBase : blocked ≤ base + cfg.K := by
    calc
      blocked = cfg.K * (base / cfg.K) + cfg.K := by
        simp [blocked, Nat.mul_add]
      _ ≤ (base % cfg.K + cfg.K * (base / cfg.K)) + cfg.K := by omega
      _ = base + cfg.K := by rw [Nat.mod_add_div]
  have hlower : lower + cfg.D + 1 ≤ blocked := by
    simpa only [base] using hlowerBase
  have hupper : blocked ≤ lower + cfg.D + cfg.K := by
    simpa only [base] using hupperBase
  have hdebtAdd : hF + cfg.D < blocked := by
    exact (Nat.add_le_add_right hhF cfg.D).trans_lt
      ((Nat.lt_succ_self (lower + cfg.D)).trans_le hlower)
  have hdebt : cfg.D < blocked - hF :=
    Nat.lt_sub_of_add_lt (by
      simpa only [Nat.add_comm] using hdebtAdd)
  exact ⟨blocked, hlower, hupper,
    dvd_mul_right cfg.K (base / cfg.K + 1), hdebt⟩


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
