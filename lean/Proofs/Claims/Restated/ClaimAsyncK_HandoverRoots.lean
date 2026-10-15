import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bW_Schedule
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Sts_Spec2Claims_ClaimConfirmedAfterHealing
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The switch round before a settled step

A theorem over a model `M : Record.Model V` with facts `facts : Record.Facts M`: a time between the
settle instant and `S.a r` puts `r` after the switch round.
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
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If `confirmedSettleTime S tE ≤ t ≤ S.a r`, then `switchRound S tE < r`. -/
theorem switchRound_lt_of_settle_le_action (facts : Record.Facts M) (S : Setup V) {tE t : Int} {r : Nat}
    (h0 : Restated.confirmedSettleTime M S tE ≤ t) (h1 : t ≤ (M.a S.hc S.E.Δ r)) :
    Restated.switchRound M S tE < r := by
  have hd := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hs := facts.gr.action_succ_eq_add_rounds S (Restated.switchRound M S tE)
  have hpos : 0 < 4 * (S.hc.R : Int) * S.E.Δ := by positivity
  refine Restated.round_lt_of_action_lt facts S ?_
  have h0' : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE + 1)) ≤ t := h0
  have h1' : t ≤ (Restated.Vocabulary.Execution.Setup.a M S r) := h1
  linarith

end

end DecoupledConsensusModel.Sts.Restated
