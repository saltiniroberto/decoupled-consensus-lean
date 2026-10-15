import Model.Vocabulary.Statements.Instantiation.OutageWindow
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The next round action

The action time of the first round at or after a time, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Statements
open DecoupledConsensusModel.Statements.Instantiation
open Execution DecoupledConsensusModel.Protocol

/-- The action time of round `roundAfter S T`, the first round action at or after `T`. -/
def Vocabulary.Statements.Instantiation.nextAction (M : Record.Model V) (S : Setup V) (T : Time) : Time := (Restated.Vocabulary.Execution.Setup.a M S (roundAfter S T))

end

end DecoupledConsensusModel.Sts.Restated
