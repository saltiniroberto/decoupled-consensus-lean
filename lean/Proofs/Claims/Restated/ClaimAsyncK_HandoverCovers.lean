import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepKitTick
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.ClaimAsyncK_HandoverCovers

/-!
# Slots before a later round's opening

A theorem over a model `M : Record.Model V` with facts `facts : Record.Facts M` placing a time at or
before `S.a r` at least two slots before the opening slot of every later round.
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

/-- If `t ≤ S.a r` and `r + 1 ≤ ρ`, then `slot(t) + 2 ≤ o_ρ`. -/
theorem slotOf_add_two_le_opening_of_le_action (facts : Record.Facts M) (S : Setup V) {t : Int} {r ρ : Nat}
    (ht : t ≤ (M.a S.hc S.E.Δ r)) (hρ : r + 1 ≤ ρ) :
    S.E.slotOf t + 2 ≤ (M.opening_slot S.hc ρ) := by
  have h1 : S.E.slotOf t ≤ (M.opening_slot S.hc r) + 1 := by
    rw [← Restated.slotOf_action facts S r]; exact slotOf_mono_sts S ht
  have h2 := facts.gr.opening_slot_succ S.hc r
  have h3 := facts.gr.opening_slot_mono S hρ
  have hR := S.hc.R_ge_three
  exact slot_gap_add_two _ _ _ _ _ h1 h2 hR h3

end

end DecoupledConsensusModel.Sts.Restated
