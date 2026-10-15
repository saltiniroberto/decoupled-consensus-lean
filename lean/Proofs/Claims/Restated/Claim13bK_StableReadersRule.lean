import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bKit
import Proofs.Claims.Restated.Claim13bW_Schedule
import Model.Conditions.Sts_Spec2Claims_ClaimStableLiveAfterHealing
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The round a stable reader's confirmation graded

A validator `v` that ran the confirmation duty of a slot `s_w`, with `s_w`'s confirmation instant
at or after `proposal_time s + stableInclusionDelay` and at or before `t`, and was awake throughout
that confirmation's grade-2 window (from one delay before the grade-2 first cutoff of the round of
`s_w + 1` to `s_w`'s confirmation instant), names a round `q + 1`, the round of `s_w + 1`, whose
previous round `q` opens at or after slot `s`. Stated over a model `M : Record.Model V`.

`exists_readerRound_of_confirmed_rule` takes the reader condition
`awakeThroughConfirmationWindow M S Sched (proposal_time s + stableInclusionDelay) t v`.
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

private theorem succ_le_of_not_le_srr (s s_w R : Nat) (h : ¬ s + 2 * R ≤ s_w) :
    s_w + 1 ≤ s + 2 * R := by
  omega

private theorem false_of_lt_zero_add_srr (s s_w R : Nat) (hR : 3 ≤ R) (hsw : s + 2 * R ≤ s_w)
    (h : s_w + 1 < 0 + R) : False := by
  omega

private theorem le_opening_of_lt_srr (s s_w o R : Nat) (hsw : s + 2 * R ≤ s_w)
    (h : s_w + 1 < o + R + R) : s ≤ o := by
  omega

/-- For a slot `s_w` whose confirmation instant is at or after `proposal_time s +
    stableInclusionDelay` and at or before `t`, with `v` awake throughout the grade-2 window of the
    round of `s_w + 1` to `s_w`'s confirmation instant: the round of `s_w + 1` is `q + 1` for a round
    `q` whose opening slot is at or after `s`, and `v` is awake throughout round `q + 1`'s grade-2
    window to `s_w`'s confirmation instant. -/
theorem exists_readerRound_of_confirmedAt_rule (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) {s s_w : Slot} {t : Int} {v : V}
    (hlo : M.proposal_time S.E s + Restated.stableInclusionDelay M S ≤ M.confirmation_time S.E s_w)
    (hhi : M.confirmation_time S.E s_w ≤ t)
    (hwin : v ∈ Sched.awakeThroughout
      (M.early S.E S.hc (M.round_of S.hc (s_w + 1)) .g2 - S.E.Δ) (M.confirmation_time S.E s_w)) :
    ∃ q : Round, M.round_of S.hc (s_w + 1) = q + 1 ∧ s ≤ M.opening_slot S.hc q ∧
      M.confirmation_time S.E s_w ≤ t ∧
      v ∈ Sched.awakeThroughout (M.early S.E S.hc (q + 1) .g2 - S.E.Δ) (M.confirmation_time S.E s_w) := by
  have hd := S.E.Δ_pos
  have hR3 := S.hc.R_ge_three
  have hct : ∀ s' : Slot, M.confirmation_time S.E s' = 4 * S.E.Δ * (s' : Int) + 6 * S.E.Δ := by
    intro s'
    rw [← facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E s', slotStart_closed]
  have hpt : M.proposal_time S.E s = 4 * S.E.Δ * (s : Int) := by
    have h := (facts.sch.slot_instants_l55 S.E s).2.2.2.2.2
    rw [hct s] at h
    linarith
  have hdel : Restated.stableInclusionDelay M S = 8 * S.E.Δ * (S.hc.R : Int) + 4 * S.E.Δ := by
    show 2 * (Restated.constants M S).period + 4 * S.E.Δ = _
    rw [Restated.period_eq facts S]
    ring
  rw [hpt, hdel, hct s_w] at hlo
  have hsw : s + 2 * S.hc.R ≤ s_w := by
    by_contra hcon
    have h1 : ((s_w : Nat) : Int) + 1 ≤ (s : Int) + 2 * (S.hc.R : Int) := by
      have : s_w + 1 ≤ s + 2 * S.hc.R := succ_le_of_not_le_srr _ _ _ hcon
      exact_mod_cast this
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : Int) ≤ 4 * S.E.Δ by linarith)
    nlinarith
  have h0 := facts.gr.opening_slot_round_of_le_slot S.hc (s_w + 1)
  have h1 := facts.gr.lt_opening_slot_round_of_succ S.hc (s_w + 1)
  rw [facts.gr.opening_slot_succ] at h1
  have hne : M.round_of S.hc (s_w + 1) ≠ 0 := by
    intro h
    rw [h, facts.gr.opening_slot_zero_mk] at h1
    exact false_of_lt_zero_add_srr _ _ _ hR3 hsw h1
  obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hne
  rw [hq, facts.gr.opening_slot_succ] at h1
  refine ⟨q, hq, le_opening_of_lt_srr _ _ _ _ hsw h1, hhi, ?_⟩
  rw [hq] at hwin
  exact hwin

/-- From the stable reader premise: the slot `s_w` of a confirmation `v` ran, at or after the stable
    inclusion delay of slot `s`, and the round `q + 1` of `s_w + 1`, with `v` awake throughout round
    `q + 1`'s grade-2 window to `tc s_w`, `s ≤ opening_slot q`, `tc s_w ≤ t`. -/
theorem exists_readerRound_of_confirmed_rule (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) {s : Slot} {t : Int} {v : V}
    (hreader : Restated.awakeThroughConfirmationWindow M S Sched
      (M.proposal_time S.E s + Restated.stableInclusionDelay M S) t v) :
    ∃ (q : Round) (s_w : Slot), M.round_of S.hc (s_w + 1) = q + 1 ∧ s ≤ M.opening_slot S.hc q ∧
      M.confirmation_time S.E s_w ≤ t ∧
      v ∈ Sched.awakeThroughout (M.early S.E S.hc (q + 1) .g2 - S.E.Δ) (M.confirmation_time S.E s_w) := by
  obtain ⟨s_w, hlo, hhi, hwin⟩ := hreader
  obtain ⟨q, hq, hso, hhi', hwin'⟩ := exists_readerRound_of_confirmedAt_rule facts S Sched hlo hhi hwin
  exact ⟨q, s_w, hq, hso, hhi', hwin'⟩

end

end DecoupledConsensusModel.Sts.Restated
