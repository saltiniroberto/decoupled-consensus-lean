import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Sts_Constants
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Action instants are more than one delay apart

One delay after a round's action instant is strictly before any later round's action instant, stated
over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `r < r'`, then one delay after round `r`'s action instant is still strictly before round
    `r'`'s. -/
theorem action_add_delta_lt_action (facts : Record.Facts M) (S : Setup V) {r r' : Round} (hr : r < r') :
    (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ < (Restated.Vocabulary.Execution.Setup.a M S r') := by
  have hd : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have hRI : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hr
  have hm' : r' = r + (m + 1) := by omega
  subst hm'
  simp only [Restated.Vocabulary.Execution.Setup.a]
  rw [facts.gr.a_add_rounds S r (m + 1)]
  have h1 : (1 : Int) ≤ ((m + 1 : Nat) : Int) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  have hpos : (0 : Int) ≤ 4 * S.E.Δ * (S.hc.R : Int) := by nlinarith
  have h2 : (12 : Int) * S.E.Δ ≤ 4 * S.E.Δ * (S.hc.R : Int) := by nlinarith
  have h3 : 1 * (4 * S.E.Δ * (S.hc.R : Int))
      ≤ ((m + 1 : Nat) : Int) * (4 * S.E.Δ * (S.hc.R : Int)) :=
    mul_le_mul_of_nonneg_right h1 hpos
  push_cast at h3 ⊢
  linarith

end

end DecoupledConsensusModel.Sts.Restated
