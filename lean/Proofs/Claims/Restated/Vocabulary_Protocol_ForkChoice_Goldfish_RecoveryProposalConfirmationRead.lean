import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.RecoveryProposalConfirmationRead
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Confirmation time of an opening slot

The confirmation time of a round's opening slot is the round's action time, stated over a model
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
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol
open Protocol
open Proofs.HealingLemmas

/-- The confirmation time of round `q`'s opening slot is round `q`'s action time. -/
theorem Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action (facts : Record.Facts M)
    (S : Setup V) (q : Round) :
    M.confirmation_time S.E ((M.opening_slot S.hc q)) = (Restated.Vocabulary.Execution.Setup.a M S q) :=
  (Restated.Vocabulary.Protocol.a_eq_confirmation_time facts S.hc S.E q).symm

end

end DecoupledConsensusModel.Sts.Restated
