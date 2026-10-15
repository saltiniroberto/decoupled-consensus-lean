import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Constants
import Model.Conditions.Claim13beRoute3_97
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Spec2Claims_ClaimFinalityLiveAfterHealing
import Model.Record.Wiring

/-!
# Finality deadline constants

How the finality deadline constants compare with the continuation constant
`finalityPremisesContinueDirect`, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- `finalityPremisesContinueDirect S gap` equals `finalityDeadlineDirect S gap + period + 5Δ`, for
    every `gap`. -/
theorem finalityPremisesContinueDirect_eq_f4 (facts : Record.Facts M) (S : Setup V) (gap : Nat) :
    Restated.finalityPremisesContinueDirect M S gap =
      Restated.finalityDeadlineDirect M S gap + (Restated.constants M S).period + 5 * S.E.Δ := by
  have h1 : Restated.finalityPremisesContinueDirect M S gap =
      ((3 * gap + S.cfg.timeoutDelay / S.hc.R - 6 + 1 : Nat) : Int) * (Restated.constants M S).period +
        14 * S.E.Δ := rfl
  have h2 : Restated.finalityDeadlineDirect M S gap =
      ((3 * gap + S.cfg.timeoutDelay / S.hc.R - 6 : Nat) : Int) * (Restated.constants M S).period +
        9 * S.E.Δ := rfl
  rw [h1, h2]
  push_cast
  ring

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- `finalityDeadlineSharpLanded_f7 S gap ≤ finalityPremisesContinueDirect S gap`, for every `gap`. -/
theorem finalityDeadlineSharpLanded_le_continue_f4 (facts : Record.Facts M) (S : Setup V) (gap : Nat) :
    Restated.finalityDeadlineSharpLanded_f7 M S gap ≤ Restated.finalityPremisesContinueDirect M S gap := by
  have h1 : Restated.finalityPremisesContinueDirect M S gap =
      ((3 * gap + S.cfg.timeoutDelay / S.hc.R - 6 + 1 : Nat) : Int) * (Restated.constants M S).period +
        14 * S.E.Δ := rfl
  have h2 : Restated.finalityDeadlineSharpLanded_f7 M S gap =
      ((3 * gap + S.cfg.timeoutDelay / S.hc.R - 5 : Nat) : Int) * (Restated.constants M S).period +
        14 * S.E.Δ := rfl
  have hper : (0 : Int) < (Restated.constants M S).period := (Restated.constants_holds facts S).period_pos
  have hn : ((3 * gap + S.cfg.timeoutDelay / S.hc.R - 5 : Nat) : Int) ≤
      ((3 * gap + S.cfg.timeoutDelay / S.hc.R - 6 + 1 : Nat) : Int) := by
    exact_mod_cast (by omega)
  rw [h1, h2]
  have := mul_le_mul_of_nonneg_right hn hper.le
  linarith

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- `finalityDeadlineDirect S gap ≤ finalityPremisesContinueDirect S gap`, for every `gap`. -/
theorem finalityDeadlineDirect_le_continue_f4 (facts : Record.Facts M) (S : Setup V) (gap : Nat) :
    Restated.finalityDeadlineDirect M S gap ≤ Restated.finalityPremisesContinueDirect M S gap := by
  have hper : (0 : Int) < (Restated.constants M S).period := (Restated.constants_holds facts S).period_pos
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  rw [Restated.finalityPremisesContinueDirect_eq_f4 facts]
  linarith

end

end DecoupledConsensusModel.Sts.Restated
