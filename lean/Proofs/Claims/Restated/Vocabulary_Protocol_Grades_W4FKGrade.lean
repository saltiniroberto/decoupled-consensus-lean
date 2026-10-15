import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The previous action precedes the G2 domain time

Round `r - 1`'s action time is at most round `r`'s G2 domain time, stated over a model
`M : Record.Model V`.
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
open Internal
open Execution
open Internal.HealingSurface
open Protocol

/-- For `0 < r`, round `r - 1`'s action time is at most round `r`'s G2 domain time
    `M.domain S.E S.hc r .g2`. -/
theorem Vocabulary.Proofs.HealingSurface.action_pred_le_domain_g2 (facts : Record.Facts M) (S : Setup V) {r : Round} (hr : 0 < r) :
    (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) ≤ M.domain S.E S.hc r .g2 := by
  have hsucc : r - 1 + 1 = r := Nat.succ_pred_eq_of_pos hr
  have h := facts.gr.action_add_delta_le_next_Γ_neg1 S (r - 1)
  rw [facts.gr.gammaNeg1_eq_domain_g2_succ S (r - 1), hsucc] at h
  exact le_trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)) h

end

end DecoupledConsensusModel.Sts.Restated
