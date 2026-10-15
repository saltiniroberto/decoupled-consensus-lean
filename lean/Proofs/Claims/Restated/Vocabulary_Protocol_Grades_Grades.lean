import Proofs.Vocabulary.Protocol.Grades.Grades
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Record.Wiring

/-!
# The earliest grade cutoff precedes the opening

Round `r`'s earliest grade cutoff `Γ_neg1` is before its opening time `Γ_0`, stated over a model
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
open DecoupledConsensusModel.Proofs.HealingLemmas
open Protocol (GradeView HealConfig)
open Protocol (SGVote)

/-- For a positive delay `Δ`, round `r`'s earliest grade cutoff `Γ_neg1` is strictly before its
    opening time `Γ_0`. -/
theorem Vocabulary.Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 (facts : Record.Facts M) (hc : HealConfig) {Δ : Time} (hΔ : 0 < Δ) (r : Round) :
    Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M hc Δ r < Restated.Vocabulary.Protocol.HealConfig.Γ_0 M hc Δ r := by
  unfold Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 Restated.Vocabulary.Protocol.HealConfig.Γ_0
  have key : ∀ a d : Int, 0 < d → a - d < a := by intro a d h; omega
  exact key (slotStart Δ ((M.opening_slot hc r))) Δ hΔ

end

end DecoupledConsensusModel.Sts.Restated
