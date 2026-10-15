import Proofs.Vocabulary.Protocol.Grades.Ladder
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Internal_HealingSurface
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Grade cutoffs, the lagged GST and ready rounds

Orderings of the action times and the earliest grade cutoffs, and the conditions under which a round
is ready for grading, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (GradeView HealConfig)
open Internal
open Execution
open Internal.HealingSurface (HonestGradeDelivery GradeRoundReady
  gradeViewAt healStoreAt gstLagged readyLag readyLag_pos)
open Proofs.HealingLemmas

private theorem a_le_Γ_neg1_succ' (facts : Record.Facts M) (S : Setup V) (r : Round) :
    Restated.Vocabulary.Execution.Setup.a M S r ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) := by
  have h := facts.gr.action_add_delta_le_next_Γ_neg1 S r
  have hΔ := S.E.Δ_pos
  unfold Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 Restated.Vocabulary.Execution.Setup.a
  linarith

private theorem Γ_neg1_add_rounds' (facts : Record.Facts M) (hc : HealConfig) (Δ : Time)
    (r k : Round) :
    Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M hc Δ (r + k) =
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M hc Δ r + 4 * Δ * ((hc.R * k : Nat) : Time) := by
  unfold Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 slotStart
  rw [facts.gr.opening_slot_add_mk]
  push_cast
  ring

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (GradeView HealConfig)
open Internal
open Execution
open Internal.HealingSurface (HonestGradeDelivery GradeRoundReady
  gradeViewAt healStoreAt gstLagged readyLag readyLag_pos)
open Proofs.HealingLemmas

/-- For a positive delay, the earliest grade cutoff of round `r` is at or before that of any later
    round `r'`. -/
theorem Vocabulary.Proofs.HealingSurface.Γ_neg1_mono (facts : Record.Facts M) (hc : HealConfig) {Δ : Time} (hΔ : 0 < Δ)
    {r r' : Round} (h : r ≤ r') :
    Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M hc Δ r ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M hc Δ r' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Γ_neg1_add_rounds' facts]
  have hfour : (0 : Time) ≤ 4 * Δ := by
    have key : ∀ d : Int, 0 < d → (0 : Int) ≤ 4 * d := by
      intro d hd
      omega
    exact key Δ hΔ
  have hrounds : (0 : Time) ≤ (hc.R * k : Nat) := Int.natCast_nonneg _
  exact Int.le_add_of_nonneg_right (Int.mul_nonneg hfour hrounds)

/-- If round `r`'s action time is at or after the lagged GST, the lagged GST is at or before the
    earliest grade cutoff of round `r + 1`. -/
theorem Vocabulary.Proofs.HealingSurface.gstLagged_le_Γ_neg1_succ (facts : Record.Facts M) (S : Setup V) (r : Round)
    (hgst : gstLagged S ≤ (Restated.Vocabulary.Execution.Setup.a M S r)) :
    gstLagged S ≤ Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) :=
  le_trans hgst (a_le_Γ_neg1_succ' facts S r)

/-- If round `r`'s action time is at or after GST, the lagged GST is at or before the earliest grade
    cutoff of round `r + 2`. -/
theorem Vocabulary.Proofs.HealingSurface.gstLagged_le_Γ_neg1_of_gst_le_a (facts : Record.Facts M) (S : Setup V) (r : Round)
    (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r)) :
    gstLagged S ≤ Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 2) := by
  have hstep : (Restated.Vocabulary.Execution.Setup.a M S r) ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) :=
    a_le_Γ_neg1_succ' facts S r
  have hlag : gstLagged S = S.E.t_GST + 4 * S.E.Δ * (S.hc.R : Nat) := by
    simp [gstLagged, readyLag]
  have hcast : ((S.hc.R * 1 : Nat) : Time) = ((S.hc.R : Nat) : Time) := by
    push_cast
    ring
  have hsplit : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 2)
      = Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) +
        4 * S.E.Δ * (S.hc.R : Nat) := by
    rw [← hcast]
    exact Γ_neg1_add_rounds' facts S.hc S.E.Δ (r + 1) 1
  rw [hlag, hsplit]
  linarith

/-- If the lagged GST is at or before the earliest grade cutoff of round `r₀`, and round `r ≥ r₀`
    acts within `ρ`'s horizon, then round `r` is ready for grading in `ρ`. -/
theorem Vocabulary.Proofs.HealingSurface.gradeRoundReady_of_action_horizon (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V}
    {r₀ r : Round}
    (hgst : gstLagged S ≤ Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r₀)
    (hround : r₀ ≤ r) (ha : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ ρ.horizon) :
    Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S ρ r := by
  have hΔ := S.E.Δ_pos
  have hact := facts.gr.domain_add_five_delta_le_action S r .g0
  have hvote := facts.sch.Γ_1_eq_vote_time S.hc S.E r
  have hconf := facts.sch.vote_time_add_delta_le_confirmation_time S (M.opening_slot S.hc r)
  have hacon := facts.sch.a_eq_confirmation_time S.hc S.E r
  constructor
  · have hmono : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r₀ ≤
        Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r :=
      Restated.Vocabulary.Proofs.HealingSurface.Γ_neg1_mono facts S.hc S.E.Δ_pos hround
    have hlag : gstLagged S = S.E.t_GST + 4 * S.E.Δ * (S.hc.R : Nat) := by
      simp [gstLagged, readyLag]
    have hR1 : 1 ≤ S.hc.R := le_trans (by norm_num) S.hc.R_ge_two
    have hR : (1 : Time) ≤ (S.hc.R : Nat) := by exact_mod_cast hR1
    have hΔnn : (0 : Time) ≤ 4 * S.E.Δ := by linarith [S.E.Δ_pos]
    have hshift : 4 * S.E.Δ ≤ 4 * S.E.Δ * (S.hc.R : Nat) := by
      calc 4 * S.E.Δ = 4 * S.E.Δ * 1 := by ring
        _ ≤ 4 * S.E.Δ * (S.hc.R : Nat) := mul_le_mul_of_nonneg_left hR hΔnn
    have hchain : S.E.t_GST + 4 * S.E.Δ * (S.hc.R : Nat) ≤
        Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r :=
      hlag ▸ le_trans hgst hmono
    have hR2 : (2 : Time) ≤ (S.hc.R : Nat) := by exact_mod_cast S.hc.R_ge_two
    have hshift2 : 8 * S.E.Δ ≤ 4 * S.E.Δ * (S.hc.R : Nat) := by
      calc 8 * S.E.Δ = 4 * S.E.Δ * 2 := by ring
        _ ≤ 4 * S.E.Δ * (S.hc.R : Nat) := mul_le_mul_of_nonneg_left hR2 hΔnn
    unfold Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 at hchain
    rw [facts.gr.early_g2_eq]
    linarith
  · linarith

/-- If round `r₀`'s action time is at or after GST and round `r ≥ r₀ + 2` acts within `ρ`'s horizon,
    then round `r` is ready for grading in `ρ`. -/
theorem Vocabulary.Proofs.HealingSurface.gradeRoundReady_of_gst_le_a (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V} {r₀ r : Round}
    (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r₀)) (hround : r₀ + 2 ≤ r)
    (ha : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ ρ.horizon) :
    Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S ρ r :=
  Restated.Vocabulary.Proofs.HealingSurface.gradeRoundReady_of_action_horizon facts S
    (Restated.Vocabulary.Proofs.HealingSurface.gstLagged_le_Γ_neg1_of_gst_le_a facts S r₀ hgst) hround ha

end

end DecoupledConsensusModel.Sts.Restated
