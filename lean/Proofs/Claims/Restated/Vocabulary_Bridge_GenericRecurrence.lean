import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Vocabulary.Protocol.Handlers.StableOutputSeed
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Statements_Instantiation
import Model.Conditions.Vocabulary_Statements_Instantiation_OutageWindow
import Model.Conditions.Vocabulary_Statements_Instantiation_RoundTimes
import Model.Record.Wiring

/-!
# The round period and the validity of the constants

Two theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: the period
`Setup.a M S 1 - Setup.a M S 0` is positive, and the constants instantiated from a setup are valid.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution Statements
open Statements.Generic

/-- The period `Setup.a M S 1 - Setup.a M S 0` is positive. -/
theorem Vocabulary.Proofs.concretePeriod_pos (facts : Record.Facts M) (S : Setup V) : 0 < (Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0) := by
  have hper : (Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0) =
      4 * S.E.Δ * (S.hc.R : Time) := by
    have h := facts.gr.a_add_rounds S 0 1
    simp only [Nat.zero_add, Nat.mul_one] at h
    rw [Restated.Vocabulary.Execution.Setup.a, Restated.Vocabulary.Execution.Setup.a, h]
    ring
  rw [hper]
  have hR : (0 : Time) < (S.hc.R : Time) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two
  nlinarith [S.E.Δ_pos]

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution Statements
open Statements.Generic

/-- The constants instantiated from the setup `S` satisfy `Valid`. -/
theorem Vocabulary.Proofs.constants_valid (facts : Record.Facts M) (S : Setup V) :
    (Restated.Vocabulary.Statements.Instantiation.constants M S).Valid := by
  refine {
    period_pos := ?_
    participationWindow_nonneg := ?_
    participationLag_nonneg := ?_
    proposerSlots_pos := ?_
    maxGap_ge_two := ?_
    delays_nonneg := ?_
    prefixEnd_le_recoveryEnd := ?_
    outage_window_nonempty := ?_ }
  · simpa [Restated.Vocabulary.Statements.Instantiation.constants] using Restated.Vocabulary.Proofs.concretePeriod_pos facts S
  · dsimp [Restated.Vocabulary.Statements.Instantiation.constants]
    exact mul_nonneg (by positivity) (Restated.Vocabulary.Proofs.concretePeriod_pos facts S).le
  · simpa [Restated.Vocabulary.Statements.Instantiation.constants] using (Restated.Vocabulary.Proofs.concretePeriod_pos facts S).le
  · simp [Restated.Vocabulary.Statements.Instantiation.constants]
  · exact (by decide : (2 : Nat) ≤ 4).trans S.cfg.K_ge_four
  · intro gap
    have ha_le_boundary : ∀ q : Round, Restated.Vocabulary.Execution.Setup.a M S q ≤
        Restated.Vocabulary.Statements.Instantiation.healingBoundaryTime M S q := by
      intro q
      rw [Restated.Vocabulary.Execution.Setup.a, facts.sch.a_eq_confirmation_time,
        facts.sch.confirmation_time_eq_support_cutoff_succ,
        Restated.Vocabulary.Statements.Instantiation.healingBoundaryTime]
      exact facts.sch.support_cutoff_le_vote_time_succ S.E _
    have hΔ : (0 : Time) ≤ S.E.Δ := S.E.Δ_pos.le
    have hperiod : 0 < (Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0) := Restated.Vocabulary.Proofs.concretePeriod_pos facts S
    have hgap : (0 : Time) ≤ (gap : Time) := by positivity
    have hgapη : (0 : Time) ≤ (gap + S.hc.η_SG : Nat) := by positivity
    have hboundary_nonneg : ∀ k : Round,
        0 ≤ Restated.Vocabulary.Statements.Instantiation.healingBoundaryTime M S (k + 1) - (Restated.Vocabulary.Execution.Setup.a M S 0) := by
      intro k
      apply sub_nonneg.mpr
      exact (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.zero_le _)).trans
        (ha_le_boundary _)
    have hstartup : 0 ≤
        Restated.Vocabulary.Statements.Instantiation.healingBoundaryTime M S
          (Statements.Instantiation.finalityStartup S gap
            (S.cfg.timeoutDelay / S.hc.R - 2) + 1) - (Restated.Vocabulary.Execution.Setup.a M S 0) :=
      hboundary_nonneg _
    have hdeadline : 0 ≤
        Restated.Vocabulary.Statements.Instantiation.healingBoundaryTime M S
          (Statements.Instantiation.finalityDeadline S gap
            (S.cfg.timeoutDelay / S.hc.R - 2) + 1) - (Restated.Vocabulary.Execution.Setup.a M S 0) :=
      hboundary_nonneg _
    dsimp [Restated.Vocabulary.Statements.Instantiation.constants]
    exact ⟨by positivity,
      add_nonneg (mul_nonneg hgap hperiod.le) (by positivity),
      add_nonneg (mul_nonneg hgapη hperiod.le) (by positivity),
      add_nonneg (by positivity)
        (add_nonneg (mul_nonneg hgapη hperiod.le) (by positivity)),
      hstartup,
      add_nonneg hdeadline (by positivity)⟩
  · intro t₀ gap
    dsimp [Restated.Vocabulary.Statements.Instantiation.constants]
    rw [Restated.Vocabulary.Execution.Setup.a, facts.sch.a_eq_confirmation_time,
      facts.sch.confirmation_time_eq_support_cutoff_succ,
      Restated.Vocabulary.Statements.Instantiation.healingBoundaryTime]
    exact facts.sch.support_cutoff_le_vote_time_succ S.E _
  · intro T
    dsimp only [Restated.Vocabulary.Statements.Instantiation.constants]
    unfold Restated.Vocabulary.Statements.Instantiation.nextAction
    generalize hrA : roundAfter S T = rA
    have hround : (M.round_of S.hc) (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S rA)) = rA :=
      Restated.Vocabulary.Proofs.HealingLemmas.round_of_slotOf_a facts S rA
    have hstep : ∀ q k : Round, Restated.Vocabulary.Execution.Setup.a M S (q + k) =
        Restated.Vocabulary.Execution.Setup.a M S q + 4 * S.E.Δ * ((S.hc.R * k : Nat) : Time) :=
      fun q k => facts.gr.a_add_rounds S q k
    have hperiod : (Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0) =
        4 * S.E.Δ * (S.hc.R : Time) := by
      have h := hstep 0 1
      simp only [Nat.zero_add, Nat.mul_one] at h
      rw [h]
      ring
    have ha : Restated.Vocabulary.Execution.Setup.a M S (rA + S.hc.η_SG + 1) =
        Restated.Vocabulary.Execution.Setup.a M S rA +
          4 * S.E.Δ * ((S.hc.R * (S.hc.η_SG + 1) : Nat) : Time) := by
      rw [show rA + S.hc.η_SG + 1 = rA + (S.hc.η_SG + 1) from Nat.add_assoc _ _ _]
      exact hstep rA (S.hc.η_SG + 1)
    show Restated.Vocabulary.Execution.Setup.a M S rA +
        ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0)) + S.E.Δ <
      M.early S.E S.hc
        ((M.round_of S.hc) (S.E.slotOf
          (Restated.Vocabulary.Execution.Setup.a M S rA)) + S.hc.η_SG + 1) .g2
    rw [hround, facts.gr.early_g2_eq, ← Restated.Vocabulary.Execution.Setup.a, ha, hperiod]
    have hbound :
        (4 : Time) ≤ (S.hc.R : Time) * (S.hc.η_SG : Time) := by
      exact_mod_cast S.outage_window
    push_cast
    nlinarith [S.E.Δ_pos, hbound]

end

end DecoupledConsensusModel.Sts.Restated
