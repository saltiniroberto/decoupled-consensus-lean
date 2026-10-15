import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bW_Schedule
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Rounds a reader is awake through

A validator awake throughout a late enough slot's vote window is awake through a whole round after a
given slot; stated over a model `M : Record.Model V`.
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
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

private theorem reader_slot_bounds (s s' o R : Nat) (hss : s + 2 * R + 1 ≤ s') (h3 : 3 ≤ R)
    (h0 : o ≤ s' - R - 2) (h1 : s' - R - 2 < o + R) :
    s ≤ o ∧ o + R + 2 ≤ s' ∧ s' ≤ o + 2 * R + 1 := by
  omega

/-- Under `WakesAtActionInstants`, if `s + 2R + 1 ≤ s'` and `v` is awake throughout the vote window
    of slot `s'`, there is a round `q` whose opening slot is at or after `s`, whose successor's
    action instant is at or before two delays before slot `s'`'s start, and such that `v` is awake
    at every instant from `S.a q` to `S.a (q + 1)`. -/
theorem exists_readerRound_of_activeAtW (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (hw : Restated.WakesAtActionInstants M S Sched) {s s' : Slot} (hss : s + 2 * S.hc.R + 1 ≤ s')
    {v : V} (hva : v ∈ activeAtW S Sched s') :
    ∃ q : Round, s ≤ (M.opening_slot S.hc q) ∧
      (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) ≤ slotStart S.E.Δ s' - 2 * S.E.Δ ∧
      v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S q)) ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))) := by
  have hd := S.E.Δ_pos
  have hR3 := S.hc.R_ge_three
  set q := (M.round_of S.hc (s' - S.hc.R - 2)) with hqdef
  have h0 := facts.gr.opening_slot_round_of_le_slot S.hc (s' - S.hc.R - 2)
  have h1 := facts.gr.lt_opening_slot_round_of_succ S.hc (s' - S.hc.R - 2)
  rw [← hqdef] at h0 h1
  rw [facts.gr.opening_slot_succ] at h1
  obtain ⟨hso, hlo, hhi⟩ := reader_slot_bounds _ _ _ _ hss hR3 h0 h1
  have hloI : (((M.opening_slot S.hc q) : Nat) : Int) + (S.hc.R : Int) + 2 ≤ ((s' : Nat) : Int) := by
    exact_mod_cast hlo
  have hhiI : ((s' : Nat) : Int) ≤ (((M.opening_slot S.hc q) : Nat) : Int) + 2 * (S.hc.R : Int) + 1 := by
    exact_mod_cast hhi
  have h4 : (0 : Int) ≤ 4 * S.E.Δ := by linarith
  have hm0 := mul_le_mul_of_nonneg_left hloI h4
  have hm1 := mul_le_mul_of_nonneg_left hhiI h4
  have hSq : (Restated.Vocabulary.Execution.Setup.a M S q) = 4 * S.E.Δ * (((M.opening_slot S.hc q) : Nat) : Int) + 6 * S.E.Δ := by
    rw [← Restated.confirmation_time_opening_slot facts S q,
      ← facts.sch.slotStart_add_six_delta_eq_confirmation_time, slotStart_closed]
  have hSq1 : (Restated.Vocabulary.Execution.Setup.a M S (q + 1))
      = 4 * S.E.Δ * (((M.opening_slot S.hc q) : Nat) : Int) + 4 * S.E.Δ * (S.hc.R : Int)
        + 6 * S.E.Δ := by
    rw [← Restated.confirmation_time_opening_slot facts S (q + 1),
      ← facts.sch.slotStart_add_six_delta_eq_confirmation_time, slotStart_closed,
      facts.gr.opening_slot_succ]
    push_cast; ring
  have hss' := slotStart_closed S.E.Δ s'
  have hwv : wVote S = (4 * (S.hc.R : Int) + 2) * S.E.Δ := rfl
  have hva' : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s' + S.E.Δ - wVote S)
      (slotStart S.E.Δ s' + S.E.Δ) := hva
  set t₀ := slotStart S.E.Δ s' + S.E.Δ - wVote S with ht₀
  have ht₀e : t₀ = 4 * S.E.Δ * ((s' : Nat) : Int) + S.E.Δ - 4 * S.E.Δ * (S.hc.R : Int)
      - 2 * S.E.Δ := by
    rw [ht₀, hwv, hss']; ring
  have hqt₀ : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ t₀ := by rw [hSq, ht₀e]; linarith
  have ht₀q : t₀ < (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) := by rw [hSq1, ht₀e]; linarith
  have hq1s : (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) ≤ slotStart S.E.Δ s' - 2 * S.E.Δ := by rw [hSq1, hss']; linarith
  have hawt₀ : v ∈ Sched.awake t₀ :=
    mem_awake_of_awakeThroughout Sched hva' le_rfl (by rw [ht₀e, hss']; nlinarith)
  have hback := Restated.awake_since_action facts S Sched hw hqt₀ ht₀q hawt₀
  refine ⟨q, hso, hq1s, mem_awakeThroughout_of_forall Sched (fun t ht0 ht1 => ?_)⟩
  by_cases ht : t ≤ t₀
  · exact hback t ht0 ht
  · exact mem_awake_of_awakeThroughout Sched hva' (by linarith) (by linarith)

end

end DecoupledConsensusModel.Sts.Restated
