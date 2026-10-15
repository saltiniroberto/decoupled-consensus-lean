import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Internal_HealingSurface
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# A ready round from the previous action

A round whose previous action is at or after GST is ready for grading, stated over a model
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
open Internal Execution Internal.HealingSurface Internal.PhaseGrades

/-- If `0 < r`, round `r - 1`'s action time is at or after GST, and round `r`'s action time is
    within the horizon of `rho`, then round `r` is ready for grading in `rho`. -/
theorem Vocabulary.Proofs.HealingSurface.gradeRoundReady_of_previousAction (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} {r : Round} (hr : 0 < r)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (r - 1)))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon) : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r := by
  constructor
  · exact hpost.trans
      ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
        (facts.gr.action_delta_le_early S S.hc.R_ge_three
          (Nat.sub_lt hr Nat.one_pos)))
  · exact (facts.gr.domain_le_a S r .g0).trans hhor

end

end DecoupledConsensusModel.Sts.Restated
