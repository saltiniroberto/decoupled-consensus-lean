import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Bridge_GenericRecurrence
import Model.Conditions.Sts_Constants
import Model.Conditions.Vocabulary_Statements_Instantiation
import Model.Record.Wiring

/-!
# Well-formed timing constants

A theorem over a model `M : Record.Model V` with facts `facts : Record.Facts M`: the timing
constants `Restated.constants M S` are valid.
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

/-- The timing constants `Restated.constants M S` satisfy `Constants.Valid`. -/
theorem constants_holds (facts : Record.Facts M) (S : Setup V) : (Restated.constants M S).Valid :=
  let h := Restated.Vocabulary.Proofs.constants_valid facts S
  { period_pos := h.period_pos
    participationWindow_nonneg := h.participationWindow_nonneg
    participationLag_nonneg := h.participationLag_nonneg
    proposerSlots_pos := h.proposerSlots_pos
    maxGap_ge_two := h.maxGap_ge_two
    delays_nonneg := h.delays_nonneg
    prefixEnd_le_recoveryEnd := h.prefixEnd_le_recoveryEnd
    outage_window_nonempty := h.outage_window_nonempty }

end

end DecoupledConsensusModel.Sts.Restated
