import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bHandover
import Proofs.Claims.Restated.Claim13bSGCompatible
import Proofs.Claims.Restated.Constants
import Model.Conditions.Claim13bHandover
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Sts_Constants
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Statements_Instantiation_RoundTimes
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bKit

/-!
# Instants of the healing schedule

Closed forms of the round length, the action instants, the finality startup and deadline lags and
the healing length, and the bounds they give on the switch round; stated over a model
`M : Record.Model V`.
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

/-- The healing length `healingLengthη M S gap` is not negative. -/
theorem healingLengthη_nonneg (facts : Record.Facts M) (S : Setup V) (gap : Nat) : 0 ≤ Restated.healingLengthη M S gap := by
  have hper : (0 : Int) < (Restated.constants M S).period := (Restated.constants_holds facts S).period_pos
  have hmul : (0 : Int) ≤ (S.hc.η_SG : Int) * (Restated.constants M S).period :=
    mul_nonneg (Int.natCast_nonneg _) (le_of_lt hper)
  have hbase := Restated.healingLength_nonneg facts S gap
  show (0 : Int) ≤ Restated.healingLength M S gap + (S.hc.η_SG : Int) * (Restated.constants M S).period
  linarith

/-- The round length in closed form: `4 * Δ * R`. -/
theorem period_eq (facts : Record.Facts M) (S : Setup V) :
    (Restated.constants M S).period = 4 * S.E.Δ * (S.hc.R : Int) := by
  show Restated.Vocabulary.Execution.Setup.a M S 1 - Restated.Vocabulary.Execution.Setup.a M S 0 = _
  have h := facts.gr.action_succ_eq_add_rounds S 0
  rw [Nat.zero_add] at h
  rw [h]
  ring

/-- `m` rounds after round `r`, the action instant is `r`'s plus `m` round lengths. -/
theorem action_add_eq_add_period_mul (facts : Record.Facts M) (S : Setup V) (r m : Round) :
    Restated.Vocabulary.Execution.Setup.a M S (r + m)
      = Restated.Vocabulary.Execution.Setup.a M S r + (m : Int) * (Restated.constants M S).period := by
  rw [Restated.period_eq facts S]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show r + (m + 1) = r + m + 1 from rfl, facts.gr.action_succ_eq_add_rounds, ih]
    push_cast
    ring

/-- Consecutive rounds' action instants are one round length apart. -/
theorem action_succ_eq_add_period (facts : Record.Facts M) (S : Setup V) (r : Round) :
    Restated.Vocabulary.Execution.Setup.a M S (r + 1)
      = Restated.Vocabulary.Execution.Setup.a M S r + (Restated.constants M S).period := by
  rw [Restated.action_add_eq_add_period_mul facts S r 1]
  push_cast
  ring

/-- The confirmation instant of the slot two after round `r`'s opening slot is `8 * Δ` after round
    `r`'s action instant. -/
theorem confirmation_third_eq (facts : Record.Facts M) (S : Setup V) (r : Round) :
    M.confirmation_time S.E ((M.opening_slot S.hc r) + 2)
      = Restated.Vocabulary.Execution.Setup.a M S r + 8 * S.E.Δ := by
  show _ = M.a S.hc S.E.Δ r + 8 * S.E.Δ
  rw [facts.sch.a_eq_confirmation_time S.hc S.E r,
    ← facts.sch.slotStart_add_six_delta_eq_confirmation_time,
    ← facts.sch.slotStart_add_six_delta_eq_confirmation_time, slotStart_add]
  push_cast
  ring

/-- The action instant of round `0` is `6Δ`. -/
private theorem action_zero_eq (facts : Record.Facts M) (S : Setup V) :
    Restated.Vocabulary.Execution.Setup.a M S 0 = 6 * S.E.Δ := by
  show M.a S.hc S.E.Δ 0 = _
  rw [facts.sch.a_eq_confirmation_time S.hc S.E 0,
    ← facts.sch.slotStart_add_six_delta_eq_confirmation_time, facts.gr.opening_slot_zero_mk]
  simp [slotStart]

/-- Every round before the round at `t` acts strictly before `t`. -/
private theorem roundAt_min_record (facts : Record.Facts M) (S : Setup V) (t : Int) {r : Round}
    (hr : r < Restated.Vocabulary.Statements.Instantiation.roundAt M S t) :
    ¬ t ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
  have hΔ : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hP : Restated.Vocabulary.Execution.Setup.a M S 1 - Restated.Vocabulary.Execution.Setup.a M S 0
      = 4 * S.E.Δ * (S.hc.R : Int) := Restated.period_eq facts S
  have hPpos : (0 : Int) < 4 * S.E.Δ * (S.hc.R : Int) := by positivity
  have hform : Restated.Vocabulary.Execution.Setup.a M S r
      = Restated.Vocabulary.Execution.Setup.a M S 0 + (r : Int) * (4 * S.E.Δ * (S.hc.R : Int)) := by
    have h := Restated.action_add_eq_add_period_mul facts S 0 r
    rw [Nat.zero_add, Restated.period_eq facts S] at h
    exact h
  by_cases h : 0 ≤ t - Restated.Vocabulary.Execution.Setup.a M S 0
  · let d : Nat := Int.toNat (t - Restated.Vocabulary.Execution.Setup.a M S 0)
    let L : Nat := Restated.Vocabulary.Statements.Instantiation.roundPeriod M S
    have hd : (d : Int) = t - Restated.Vocabulary.Execution.Setup.a M S 0 := Int.toNat_of_nonneg h
    have hLtime : (L : Int) = 4 * S.E.Δ * (S.hc.R : Int) := by
      show ((Int.toNat (Restated.Vocabulary.Execution.Setup.a M S 1
        - Restated.Vocabulary.Execution.Setup.a M S 0) : Nat) : Int) = _
      rw [Int.toNat_of_nonneg (by rw [hP]; exact hPpos.le), hP]
    have hL : 0 < L := by exact_mod_cast (show (0 : Int) < (L : Int) by rw [hLtime]; exact hPpos)
    have hnot : ¬ d ≤ L * r := by
      intro hdr
      have hqle : d ⌈/⌉ L ≤ r := (ceilDiv_le_iff_le_mul hL).2 hdr
      exact (Nat.not_lt_of_ge hqle) hr
    have hlt : L * r < d := Nat.lt_of_not_ge hnot
    have hltInt : (L : Int) * (r : Int) < (d : Int) := by exact_mod_cast hlt
    rw [hLtime, hd] at hltInt
    rw [hform]
    intro htr
    nlinarith
  · have ht : t ≤ Restated.Vocabulary.Execution.Setup.a M S 0 := by linarith
    have hd0 : Int.toNat (t - Restated.Vocabulary.Execution.Setup.a M S 0) = 0 :=
      Int.toNat_eq_zero.mpr (by linarith)
    have hq0 : Restated.Vocabulary.Statements.Instantiation.roundAt M S t = 0 := by
      show Int.toNat (t - Restated.Vocabulary.Execution.Setup.a M S 0) ⌈/⌉ _ = 0
      rw [hd0]
      simp
    rw [hq0] at hr
    exact absurd hr (Nat.not_lt_zero r)

/-- For `0 ≤ t`, the action instant of the round at `t` is less than one round length after `t`. -/
theorem action_roundAt_lt (facts : Record.Facts M) (S : Setup V) (t : Int) (ht : 0 ≤ t) :
    Restated.Vocabulary.Execution.Setup.a M S (Restated.Vocabulary.Statements.Instantiation.roundAt M S t)
      < t + (Restated.constants M S).period := by
  have hΔ : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hperiod : (Restated.constants M S).period = 4 * S.E.Δ * (S.hc.R : Int) :=
    Restated.period_eq facts S
  rcases Nat.eq_zero_or_pos (Restated.Vocabulary.Statements.Instantiation.roundAt M S t) with hz | hpos
  · rw [hz, action_zero_eq facts S, hperiod]
    nlinarith
  · have hprev : Restated.Vocabulary.Execution.Setup.a M S
        (Restated.Vocabulary.Statements.Instantiation.roundAt M S t - 1) < t :=
      lt_of_not_ge (roundAt_min_record facts S t
        (Nat.sub_lt (Nat.zero_lt_of_lt hpos) (by decide)))
    have hsucc : Restated.Vocabulary.Statements.Instantiation.roundAt M S t - 1 + 1
        = Restated.Vocabulary.Statements.Instantiation.roundAt M S t := Nat.succ_pred_eq_of_pos hpos
    have heq := Restated.action_succ_eq_add_period facts S
      (Restated.Vocabulary.Statements.Instantiation.roundAt M S t - 1)
    rw [hsucc] at heq
    rw [heq]
    linarith

/-- The finality-startup lag as an instant: `finalityStartup S gap S.extraRounds + 1` whole rounds
    and three delays. -/
theorem constants_finalityStartup_eq (facts : Record.Facts M) (S : Setup V) (gap : Nat) :
    (Restated.constants M S).finalityStartup gap
      = ((Statements.Instantiation.finalityStartup S gap S.extraRounds : Nat) : Int) *
          (Restated.constants M S).period + (Restated.constants M S).period + 3 * S.E.Δ := by
  have hFs : Statements.Instantiation.finalityStartup S gap S.extraRounds
      = DecoupledConsensusModel.Sts.finalityStartup S gap
          (S.cfg.timeoutDelay / S.hc.R - 2) := rfl
  show Restated.healingBoundaryTime M S
      (DecoupledConsensusModel.Sts.finalityStartup S gap
        (S.cfg.timeoutDelay / S.hc.R - 2) + 1) - Restated.Vocabulary.Execution.Setup.a M S 0 = _
  rw [hFs]
  generalize DecoupledConsensusModel.Sts.finalityStartup S gap (S.cfg.timeoutDelay / S.hc.R - 2) = F
  have hA : M.a S.hc S.E.Δ (F + 1) = slotStart S.E.Δ (M.opening_slot S.hc (F + 1)) + 6 * S.E.Δ := by
    rw [facts.sch.a_eq_confirmation_time S.hc S.E (F + 1),
      ← facts.sch.slotStart_add_six_delta_eq_confirmation_time]
  have hadd := Restated.action_add_eq_add_period_mul facts S 0 (F + 1)
  rw [Nat.zero_add] at hadd
  show M.vote_time S.E ((M.opening_slot S.hc (F + 1)) + 2) - M.a S.hc S.E.Δ 0 = _
  rw [← facts.sch.slotStart_add_delta_eq_vote_time, slotStart_add]
  change M.a S.hc S.E.Δ (F + 1) = M.a S.hc S.E.Δ 0 + _ at hadd
  push_cast at hadd ⊢
  linear_combination hadd - hA

/-- The finality deadline as an instant: `finalityDeadline S gap S.extraRounds + 1` whole rounds and
    six delays. -/
theorem constants_finalityDeadline_eq (facts : Record.Facts M) (S : Setup V) (gap : Nat) :
    (Restated.constants M S).finalityDeadline gap
      = ((Statements.Instantiation.finalityDeadline S gap S.extraRounds : Nat) : Int) *
          (Restated.constants M S).period + (Restated.constants M S).period + 6 * S.E.Δ := by
  have hFd : Statements.Instantiation.finalityDeadline S gap S.extraRounds
      = DecoupledConsensusModel.Sts.finalityDeadline S gap
          (S.cfg.timeoutDelay / S.hc.R - 2) := rfl
  show Restated.healingBoundaryTime M S
      (DecoupledConsensusModel.Sts.finalityDeadline S gap
        (S.cfg.timeoutDelay / S.hc.R - 2) + 1) - Restated.Vocabulary.Execution.Setup.a M S 0
        + 3 * S.E.Δ = _
  rw [hFd]
  generalize DecoupledConsensusModel.Sts.finalityDeadline S gap (S.cfg.timeoutDelay / S.hc.R - 2) = F
  have hA : M.a S.hc S.E.Δ (F + 1) = slotStart S.E.Δ (M.opening_slot S.hc (F + 1)) + 6 * S.E.Δ := by
    rw [facts.sch.a_eq_confirmation_time S.hc S.E (F + 1),
      ← facts.sch.slotStart_add_six_delta_eq_confirmation_time]
  have hadd := Restated.action_add_eq_add_period_mul facts S 0 (F + 1)
  rw [Nat.zero_add] at hadd
  show M.vote_time S.E ((M.opening_slot S.hc (F + 1)) + 2) - M.a S.hc S.E.Δ 0 + 3 * S.E.Δ = _
  rw [← facts.sch.slotStart_add_delta_eq_vote_time, slotStart_add]
  change M.a S.hc S.E.Δ (F + 1) = M.a S.hc S.E.Δ 0 + _ at hadd
  push_cast at hadd ⊢
  linear_combination hadd - hA

/-- The healing length `healingLengthη M S gap` is `Fs + Fd + gap + 3 + S.hc.η_SG` whole rounds and
    nine delays, with `Fs` and `Fd` the finality-startup and finality-deadline round counts. -/
theorem healingLengthη_eq (facts : Record.Facts M) (S : Setup V) (gap : Nat) :
    Restated.healingLengthη M S gap
      = (((Statements.Instantiation.finalityStartup S gap S.extraRounds : Nat) : Int)
          + ((Statements.Instantiation.finalityDeadline S gap S.extraRounds : Nat) : Int)
          + (gap : Int) + 3 + (S.hc.η_SG : Int)) * (Restated.constants M S).period + 9 * S.E.Δ := by
  show (Restated.constants M S).finalityStartup gap + (gap : Int) * (Restated.constants M S).period +
      (Restated.constants M S).finalityDeadline gap + (Restated.constants M S).period
      + (S.hc.η_SG : Int) * (Restated.constants M S).period = _
  rw [Restated.constants_finalityStartup_eq facts, Restated.constants_finalityDeadline_eq facts]
  ring

private theorem nat_regroup (a b c d e f : Nat) :
    a + b + c + d + e + f = a + (b + c + d + e + f) := by omega

/-- If `t_GST ≤ tGAT` and `tGAT + healingLengthη M S gap ≤ tE`, the switch round is at or after the
    round at `tGAT` plus `Fs + Fd + gap + 2 + S.hc.η_SG`, with `Fs` and `Fd` the finality-startup
    and finality-deadline round counts. -/
theorem switchRound_ge_of_healingLengthη (facts : Record.Facts M) (S : Setup V) (tGAT tE : Int)
    (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) :
    Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT
      + Statements.Instantiation.finalityStartup S gap S.extraRounds
      + Statements.Instantiation.finalityDeadline S gap S.extraRounds
      + gap + 2 + S.hc.η_SG
      ≤ Restated.switchRound M S tE := by
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have htGAT : (0 : Int) ≤ tGAT := le_trans S.E.t_GST_nonneg hgst
  have hgroup : Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT
      + Statements.Instantiation.finalityStartup S gap S.extraRounds
      + Statements.Instantiation.finalityDeadline S gap S.extraRounds
      + gap + 2 + S.hc.η_SG
      = Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT
        + (Statements.Instantiation.finalityStartup S gap S.extraRounds
          + Statements.Instantiation.finalityDeadline S gap S.extraRounds
          + gap + 2 + S.hc.η_SG) :=
    nat_regroup _ _ _ _ _ _
  rw [hgroup]
  refine Restated.switchRound_max facts S tE ?_
  rw [Restated.confirmation_third_eq facts, Restated.action_add_eq_add_period_mul facts]
  have hcast : ((Statements.Instantiation.finalityStartup S gap S.extraRounds
        + Statements.Instantiation.finalityDeadline S gap S.extraRounds
        + gap + 2 + S.hc.η_SG : Nat) : Int)
      = ((Statements.Instantiation.finalityStartup S gap S.extraRounds : Nat) : Int)
        + ((Statements.Instantiation.finalityDeadline S gap S.extraRounds : Nat) : Int)
        + (gap : Int) + 2 + (S.hc.η_SG : Int) := by
    push_cast; ring
  rw [hcast]
  have hlt : Restated.Vocabulary.Execution.Setup.a M S
        (Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT)
      < tGAT + (Restated.constants M S).period := Restated.action_roundAt_lt facts S tGAT htGAT
  rw [Restated.healingLengthη_eq facts S gap] at hlen
  nlinarith [hlen, hlt]

private theorem cut_le_target_nat (r A L Fd gap η : Nat) :
    r + 1 + 1 + (1 + A) + 2 * L + 1 + η + gap + 1
      ≤ r + (1 + A + 3 * L + gap + 5) + Fd + gap + 2 + η := by omega

/-- If `t_GST ≤ tGAT` and `tGAT + healingLengthη M S gap ≤ tE`, then
    `cutBoundW M S tGAT gap + gap + 1 ≤ switchRound M S tE`. -/
theorem hη_of_healingLengthη (facts : Record.Facts M) (S : Setup V) (tGAT tE : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) :
    Restated.cutBoundW M S tGAT gap + gap + 1 ≤ Restated.switchRound M S tE := by
  have hle : Restated.cutBoundW M S tGAT gap + gap + 1
      ≤ Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT
        + Statements.Instantiation.finalityStartup S gap S.extraRounds
        + Statements.Instantiation.finalityDeadline S gap S.extraRounds
        + gap + 2 + S.hc.η_SG := by
    unfold Restated.cutBoundW Statements.Instantiation.finalityStartup
    exact cut_le_target_nat _ _ _ _ _ _
  exact le_trans hle (Restated.switchRound_ge_of_healingLengthη facts S tGAT tE gap hgst hlen)

/-- If `t_GST ≤ tGAT` and `tGAT + healingLengthη M S gap ≤ tE`, then
    `cutBoundW M S tGAT gap + gap ≤ switchRound M S tE`. -/
theorem hη_of_healingLengthη' (facts : Record.Facts M) (S : Setup V) (tGAT tE : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) :
    Restated.cutBoundW M S tGAT gap + gap ≤ Restated.switchRound M S tE :=
  le_trans (Nat.le_succ _) (Restated.hη_of_healingLengthη facts S tGAT tE gap hgst hlen)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- After a healing phase from `tGAT` (at or after GST) of length `healingLengthη` ending at `tE`,
    every round from the switch round on is at least `η_SG`. -/
theorem eta_le_of_switchRound_le (facts : Record.Facts M) (S : Setup V) (tGAT tE : Int)
    (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    {r : Round} (hr : Restated.switchRound M S tE ≤ r) : S.hc.η_SG ≤ r :=
  le_trans (le_trans (Nat.le_add_left _ _)
    (Restated.switchRound_ge_of_healingLengthη facts S tGAT tE gap hgst hlen)) hr

/-- After a healing phase from `tGAT` (at or after GST) of length `healingLengthη` ending at `tE`,
    the switch round is at least `1`. -/
theorem one_le_switchRound (facts : Record.Facts M) (S : Setup V) (tGAT tE : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) :
    1 ≤ Restated.switchRound M S tE :=
  le_trans (Nat.le_trans (by decide : 1 ≤ 2) (Nat.le_trans (Nat.le_add_left 2 _) (Nat.le_add_right _ _)))
    (Restated.switchRound_ge_of_healingLengthη facts S tGAT tE gap hgst hlen)

/-- From the opening slot of a round `r ≥ 1` on, every slot's round is at least `1`. -/
theorem one_le_round_of_of_opening_slot_le (facts : Record.Facts M) (S : Setup V) {r : Round}
    {s : Slot} (hr : 1 ≤ r) (hs : M.opening_slot S.hc r ≤ s) : 1 ≤ M.round_of S.hc s := by
  have h := facts.gr.round_of_mono_sts S.hc hs
  rw [facts.gr.round_of_opening_slot_eq S.hc r] at h
  exact le_trans hr h

end

end DecoupledConsensusModel.Sts.Restated
