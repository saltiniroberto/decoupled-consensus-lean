import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_MajoritySG_ForkChoice
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# One delay between consecutive action times

One network delay after round `r - 1`'s action time is at most round `r`'s action time, stated over
a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Protocol
open Internal
open Execution

/-- For `0 < r`, round `r - 1`'s action time plus `Δ` is at most round `r`'s action time. -/
theorem Vocabulary.Protocol.previous_action_add_delta_le_action (facts : Record.Facts M) (S : Setup V) {r : Round}
    (hr : 0 < r) : (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S r) := by
  have hre : r - 1 + 1 = r := by
    have key : ∀ n : Nat, 0 < n → n - 1 + 1 = n := by
      intro n hn
      omega
    exact key r hr
  have ha := facts.gr.a_add_rounds S (r - 1) 1
  rw [hre] at ha
  show M.a S.hc S.E.Δ (r - 1) + S.E.Δ ≤ M.a S.hc S.E.Δ r
  rw [ha]
  simp only [Nat.mul_one]
  have hfactor : (1 : Time) ≤ 4 * (S.hc.R : Time) := by
    have key : ∀ R : Nat, 2 ≤ R → 1 ≤ 4 * R := by
      intro R hR
      omega
    exact_mod_cast key S.hc.R S.hc.R_ge_two
  have hDelta : (0 : Time) ≤ S.E.Δ := le_of_lt S.E.Δ_pos
  have hmul : S.E.Δ * 1 ≤ S.E.Δ * (4 * (S.hc.R : Time)) :=
    Int.mul_le_mul_of_nonneg_left hfactor hDelta
  calc
    M.a S.hc S.E.Δ (r - 1) + S.E.Δ = M.a S.hc S.E.Δ (r - 1) + S.E.Δ * 1 := by ring
    _ ≤ M.a S.hc S.E.Δ (r - 1) + S.E.Δ * (4 * (S.hc.R : Time)) :=
      add_le_add_right hmul _
    _ = M.a S.hc S.E.Δ (r - 1) + 4 * S.E.Δ * (S.hc.R : Time) := by ring

end

end DecoupledConsensusModel.Sts.Restated
