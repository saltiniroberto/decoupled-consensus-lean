import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Action instants and wake schedules

Arithmetic on the rounds' action instants and the attester window `wAttest S`. Stated over a model `M : Record.Model V`.
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

/-- Round `(r + 1)`'s action instant minus `wAttest S` is round `r`'s action instant. -/
theorem wAttest_eq_action_succ_sub (facts : Record.Facts M) (S : Setup V) (r : Round) :
    (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - wAttest S = (Restated.Vocabulary.Execution.Setup.a M S r) := by
  show M.a S.hc S.E.Δ (r + 1) - wAttest S = M.a S.hc S.E.Δ r
  rw [facts.gr.a_add_rounds S r 1]
  simp only [wAttest]
  push_cast
  ring

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- An action instant strictly before another belongs to an earlier round. -/
theorem round_lt_of_action_lt (facts : Record.Facts M) (S : Setup V) {r ρ : Round} (h : (Restated.Vocabulary.Execution.Setup.a M S r) < (Restated.Vocabulary.Execution.Setup.a M S ρ)) : r < ρ := by
  by_contra hcon
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hcon)
  change M.a S.hc S.E.Δ (ρ + k) < M.a S.hc S.E.Δ ρ at h
  rw [facts.gr.a_add_rounds S ρ k] at h
  have hd := S.E.Δ_pos
  have hk : (0 : Int) ≤ ((S.hc.R * k : Nat) : Int) := Int.natCast_nonneg _
  nlinarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A later round's action instant is not earlier. -/
theorem action_mono (facts : Record.Facts M) (S : Setup V) {r ρ : Round} (h : r ≤ ρ) : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (Restated.Vocabulary.Execution.Setup.a M S ρ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  show M.a S.hc S.E.Δ r ≤ M.a S.hc S.E.Δ (r + k)
  rw [facts.gr.a_add_rounds S r k]
  have hd := S.E.Δ_pos
  have hk : (0 : Int) ≤ ((S.hc.R * k : Nat) : Int) := Int.natCast_nonneg _
  nlinarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- No action instant lies strictly between two consecutive action instants. -/
theorem no_action_between (facts : Record.Facts M) (S : Setup V) (r ρ : Round)
    (h1 : (Restated.Vocabulary.Execution.Setup.a M S r) < (Restated.Vocabulary.Execution.Setup.a M S ρ)) (h2 : (Restated.Vocabulary.Execution.Setup.a M S ρ) < (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) : False := by
  have hlt := Restated.round_lt_of_action_lt facts S h1
  have hlt' := Restated.round_lt_of_action_lt facts S h2
  exact absurd (Nat.le_of_lt_succ hlt') (Nat.not_le.mpr hlt)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If round `ρ`'s action instant is strictly before round `r`'s, it is at or before
    `S.a r − wAttest S`, the start of round `r`'s attester window. -/
theorem action_le_sub_wAttest_of_lt (facts : Record.Facts M) (S : Setup V) {r ρ : Round} (h : (Restated.Vocabulary.Execution.Setup.a M S ρ) < (Restated.Vocabulary.Execution.Setup.a M S r)) :
    (Restated.Vocabulary.Execution.Setup.a M S ρ) ≤ (Restated.Vocabulary.Execution.Setup.a M S r) - wAttest S := by
  have hρr := Restated.round_lt_of_action_lt facts S h
  have hle : (Restated.Vocabulary.Execution.Setup.a M S ρ) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) := Restated.action_mono facts S (Nat.le_sub_one_of_lt hρr)
  have hpred := Restated.wAttest_eq_action_succ_sub facts S (r - 1)
  rw [Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le ρ) hρr))] at hpred
  linarith

end


end DecoupledConsensusModel.Sts.Restated
