import Proofs.Vocabulary.Internal.Definitions.NamedJointOutage
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedOutageEntry
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Rounds inside a run

The rounds whose action instant lies in a run from a given instant on, stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.NamedJointOutage
open Execution NamedOutageEntry NamedStableChainOutage DecoupledConsensusModel.Protocol

/-- Round `r` is positive and its action instant lies between `b0` and the horizon of `rho`. -/
def Vocabulary.Internal.NamedJointOutage.RoundIncluded (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (b0 : Time) (r : Round) : Prop :=
  0 < r ∧ b0 ≤ (Restated.Vocabulary.Execution.Setup.a M S r) ∧ (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon

end

end DecoupledConsensusModel.Sts.Restated
