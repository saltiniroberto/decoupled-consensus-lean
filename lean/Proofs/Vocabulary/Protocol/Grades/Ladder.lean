module
public import Proofs.Vocabulary.Internal.HealingSurface
public import Proofs.Vocabulary.Objects.ActionRound
public import Proofs.Vocabulary.ModelVocabulary.Healing.Schedule
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Proofs.Vocabulary.Internal.Internal.GradeReads

@[expose] public section


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (GradeView HealConfig)
open Internal
open Execution
open Internal.HealingSurface (HonestGradeDelivery GradeRoundReady
  gradeViewAt healStoreAt gstLagged readyLag readyLag_pos)
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The cutoff arithmetic of one `Δ` hop -/

/-- `Γ_r^0 + Δ = Γ_r^1`. -/
theorem Γ_0_add_Δ (hc : HealConfig) (Δ : Time) (r : Round) :
    hc.Γ_0 Δ r + Δ = hc.Γ_1 Δ r := rfl


/-- The action of round `r` is at or before the earliest grade cutoff of round `r + 1`. -/
theorem a_le_Γ_neg1_succ (hc : HealConfig) {Δ : Time} (hΔ : 0 < Δ)
    (r : Round) : hc.a Δ r ≤ hc.Γ_neg1 Δ (r + 1) := by
  have hR : (2 : Time) ≤ (hc.R : Nat) := by
    exact_mod_cast hc.R_ge_two
  unfold HealConfig.a HealConfig.Γ_neg1 HealConfig.opening_slot slotStart
  push_cast
  have hfactor : (0 : Time) ≤ 4 * (hc.R : Nat) - 7 := by
    have key : ∀ R : Int, 2 ≤ R → (0 : Int) ≤ 4 * R - 7 := by
      intro R hR'
      omega
    exact key (hc.R : Nat) hR
  have hprod : (0 : Time) ≤ Δ * (4 * (hc.R : Nat) - 7) :=
    Int.mul_nonneg (le_of_lt hΔ) hfactor
  calc
    4 * Δ * (r * hc.R) + 6 * Δ ≤
        4 * Δ * (r * hc.R) + 6 * Δ + Δ * (4 * hc.R - 7) :=
      Int.le_add_of_nonneg_right hprod
    _ = 4 * Δ * ((r + 1) * hc.R) - Δ := by ring


/-- `t_GST ≤ gstLagged S`. -/
theorem t_GST_le_gstLagged (S : Setup V) : S.E.t_GST ≤ gstLagged S := by
  have h1 : (0 : Time) ≤ S.E.Δ := le_of_lt S.E.Δ_pos
  have h2 : (0 : Time) ≤ (S.hc.R * readyLag : Nat) := Int.natCast_nonneg _
  have h3 : (0 : Time) ≤ 4 * S.E.Δ * (S.hc.R * readyLag : Nat) :=
    mul_nonneg (mul_nonneg (by norm_num) h1) h2
  unfold gstLagged
  linarith


/-- `domain` at `.g0` is `Γ_r^1`. -/
theorem domain_g0_eq_Γ_1 (S : Setup V) (r : Round) :
    DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0 = S.hc.Γ_1 S.E.Δ r := by
  have hopen : DecoupledConsensusModel.Protocol.opening S.E S.hc r = S.hc.Γ_0 S.E.Δ r :=
    (Protocol.Γ_0_eq_proposal_time S.hc S.E r).symm
  unfold DecoupledConsensusModel.Protocol.domain DecoupledConsensusModel.Protocol.Phase.domainOffset
  rw [hopen, one_mul]
  exact Γ_0_add_Δ S.hc S.E.Δ r


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
