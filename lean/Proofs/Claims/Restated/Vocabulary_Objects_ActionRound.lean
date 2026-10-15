import Proofs.Vocabulary.Objects.ActionRound
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The action time names its own round

A theorem over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: the slot of
round `r`'s action time belongs to round `r`.
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
open DecoupledConsensusModel.Proofs.HealingLemmas.ActionRound
open Protocol (HealConfig)
open Execution (Setup)

/-- The round of the slot of round `r`'s action time is `r`. -/
theorem Vocabulary.Proofs.HealingLemmas.ActionRound.round_of_slotOf_a (facts : Record.Facts M) (S : Setup V) (r : Round) :
    (M.round_of S.hc (S.E.slotOf ((Restated.Vocabulary.Execution.Setup.a M S r)))) = r := by
  have hslot : S.E.slotOf ((Restated.Vocabulary.Execution.Setup.a M S r)) = (M.opening_slot S.hc r) + 1 := by
    rw [Restated.Vocabulary.Execution.Setup.a, Restated.Vocabulary.Protocol.a_eq_confirmation_time facts]
    exact facts.sch.ActionRound_slotOf_confirmation_time S.E ((M.opening_slot S.hc r))
  rw [hslot, facts.gr.ActionRound_round_of_opening_succ]

end

end DecoupledConsensusModel.Sts.Restated
