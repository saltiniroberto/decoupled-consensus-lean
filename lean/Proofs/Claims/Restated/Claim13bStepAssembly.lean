import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bKit
import Proofs.Claims.Restated.Vocabulary_Internal_Legacy_Instance
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Statements_Instantiation_RoundTimes
import Model.Record.Wiring

/-!
# GST and the switch round's opening

A round at or after the switch round opens at or after the switch round's opening, and GST is at or
before that opening; stated over a model `M : Record.Model V`.
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

/-- If `r` is at or after the switch round, `switchOpening S tE` is at or before round `r`'s
    opening. -/
theorem switchOpening_le_opening (facts : Record.Facts M) (S : Setup V) {tE : Int} {r : Round}
    (hr : Restated.switchRound M S tE ≤ r) : Restated.switchOpening M S tE ≤ M.opening S.E S.hc r :=
  facts.gr.Sts_opening_mono S hr

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

private theorem succ_le_switch_target_nat (r Fs Fd gap η : Nat) :
    r + 1 ≤ r + Fs + Fd + gap + 2 + η := by omega

/-- If `t_GST ≤ tGAT` and `tGAT + healingLengthη M S gap ≤ tE`, GST is at or before the instant the
    switch round opens at. -/
theorem gst_le_switchOpening (facts : Record.Facts M) (S : Setup V) (tGAT tE : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) :
    S.E.t_GST ≤ Restated.switchOpening M S tE := by
  have hsw : Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT + 1 ≤ Restated.switchRound M S tE :=
    le_trans (succ_le_switch_target_nat _ _ _ _ _)
      (Restated.switchRound_ge_of_healingLengthη facts S tGAT tE gap hgst hlen)
  have hopen : M.opening S.E S.hc (Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT + 1)
      ≤ Restated.switchOpening M S tE := facts.gr.Sts_opening_mono S hsw
  -- one delay after a round's action is at or before the next round's G2 early cutoff, which is at
  -- or before that round's opening
  have hnext : Restated.Vocabulary.Execution.Setup.a M S (Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT)
      ≤ M.opening S.E S.hc (Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT + 1) := by
    have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three
      (Nat.lt_succ_self (Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT))
    have h2 := facts.gr.early_g2_le_opening S
      (Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT + 1)
    have hd := S.E.Δ_pos
    show M.a S.hc S.E.Δ _ ≤ _
    linarith
  exact le_trans hgst (le_trans (Restated.Vocabulary.Statements.roundAt_spec facts S tGAT)
    (le_trans hnext hopen))

end

end DecoupledConsensusModel.Sts.Restated
