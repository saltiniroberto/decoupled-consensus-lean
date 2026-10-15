import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# A round's action precedes a later proposal

Round `r`'s action time is before the proposal time of the second slot after its opening slot,
stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Protocol
open Internal
open Execution
open Internal.NamedRecoveryRead

/-- Round `r`'s action time is strictly before the proposal time of round `r`'s opening slot plus
    two. -/
theorem Vocabulary.Protocol.action_lt_proposal_time_two_after (facts : Record.Facts M)
    (S : Setup V) (r : Round) :
    (Restated.Vocabulary.Execution.Setup.a M S r) < M.proposal_time S.E ((M.opening_slot S.hc r) + 2) := by
  show M.a S.hc S.E.Δ r < _
  rw [facts.sch.a_eq_confirmation_time S.hc S.E r]
  exact facts.sch.confirmationTime_lt_proposalTime_of_two_le S.E (le_refl _)

end

end DecoupledConsensusModel.Sts.Restated
