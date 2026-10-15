import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Statements_Instantiation_RoundTimes
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bSGCompatible

/-!
# The switch round

The switch round's defining property, its maximality, and the bounds that make it positive; stated
over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If the switch round is not round zero, the confirmation instant of its third slot is at or
    before `tE`. -/
theorem switchRound_spec (facts : Record.Facts M) (S : Setup V) (tE : Int) (h : Restated.switchRound M S tE ≠ 0) :
    M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2) ≤ tE :=
  Nat.findGreatest_of_ne_zero rfl h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Any round whose third slot's confirmation instant is at or before `tE` is at or before the
    switch round. -/
theorem switchRound_max (facts : Record.Facts M) (S : Setup V) (tE : Int) {r : Round}
    (hr : M.confirmation_time S.E ((M.opening_slot S.hc r) + 2) ≤ tE) :
    r ≤ Restated.switchRound M S tE := by
  have hΔ : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hthird : M.a S.hc S.E.Δ r ≤ M.confirmation_time S.E ((M.opening_slot S.hc r) + 2) := by
    rw [facts.sch.a_eq_confirmation_time S.hc S.E r, facts.sch.confirmation_time_eq_support_cutoff_succ]
    have h1 : M.support_cutoff S.E ((M.opening_slot S.hc r) + 1) ≤
        M.vote_time S.E ((M.opening_slot S.hc r) + 2) :=
      facts.sch.support_cutoff_le_vote_time_succ S.E ((M.opening_slot S.hc r) + 1)
    have h2 := facts.sch.vote_time_add_delta_le_confirmation_time S ((M.opening_slot S.hc r) + 2)
    linarith
  have hlin : M.a S.hc S.E.Δ r = M.a S.hc S.E.Δ 0 + 4 * S.E.Δ * ((S.hc.R * r : Nat) : Int) := by
    simpa only [zero_add] using facts.gr.a_add_rounds S 0 r
  have ha0 : 0 < M.a S.hc S.E.Δ 0 := by
    rw [facts.sch.a_eq_confirmation_time S.hc S.E 0, facts.sch.confirmation_time_eq_support_cutoff_succ]
    exact facts.sch.support_cutoff_pos S _
  have hrnn : (0 : Int) ≤ (r : Int) := Int.natCast_nonneg r
  have hle : (r : Int) ≤ tE := by
    have hkey : (r : Int) ≤ 4 * S.E.Δ * ((S.hc.R * r : Nat) : Int) := by
      push_cast
      have hΔR : (1 : Int) ≤ 4 * S.E.Δ * (S.hc.R : Int) := by nlinarith
      nlinarith
    linarith
  exact Nat.le_findGreatest (by omega) hr

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A round's action instant is at or before the confirmation instant of its third slot. -/
theorem action_le_confirmation_third (facts : Record.Facts M) (S : Setup V) (r : Round) :
    (Restated.Vocabulary.Execution.Setup.a M S r) ≤ M.confirmation_time S.E ((M.opening_slot S.hc r) + 2) := by
  show (M.a S.hc S.E.Δ r) ≤ _
  rw [facts.sch.a_eq_confirmation_time S.hc S.E r, facts.sch.confirmation_time_eq_support_cutoff_succ]
  have h1 : M.support_cutoff S.E ((M.opening_slot S.hc r) + 1) ≤
      M.vote_time S.E ((M.opening_slot S.hc r) + 2) :=
    facts.sch.support_cutoff_le_vote_time_succ S.E ((M.opening_slot S.hc r) + 1)
  have h2 := facts.sch.vote_time_add_delta_le_confirmation_time S ((M.opening_slot S.hc r) + 2)
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The cut bound `cutBoundW M S tGAT gap` is positive. -/
theorem cutBoundW_pos (facts : Record.Facts M) (S : Setup V) (tGAT : Int) (gap : Nat) : 0 < Restated.cutBoundW M S tGAT gap := by
  unfold Restated.cutBoundW
  exact Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.le_add_right _ _)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `cutBoundW M S tGAT gap + gap` is at or before the switch round, the switch round is not
    round zero. -/
theorem switchRound_ne_zero_of_cutBoundW (facts : Record.Facts M) (S : Setup V) (tGAT tE : Int) (gap : Nat)
    (hη : Restated.cutBoundW M S tGAT gap + gap ≤ Restated.switchRound M S tE) : Restated.switchRound M S tE ≠ 0 :=
  Nat.pos_iff_ne_zero.mp
    (lt_of_lt_of_le (Restated.cutBoundW_pos facts S tGAT gap)
      (le_trans (Nat.le_add_right _ gap) hη))

end

end DecoupledConsensusModel.Sts.Restated
