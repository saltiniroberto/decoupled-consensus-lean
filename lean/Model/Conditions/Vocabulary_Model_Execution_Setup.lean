import Model.Vocabulary.Execution.Setup
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Round action time

The action time of a round, over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.Setup
open Protocol (HeightConfig)

/-- The action time of round `r`, `M.a` at the setup's healing configuration and `Δ`. -/
abbrev Vocabulary.Execution.Setup.a (M : Record.Model V) (S : Setup V) (r : Round) : Time := (M.a S.hc S.E.Δ r)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.Setup
open Protocol (HeightConfig)

/-- `DecoupledConsensusModel.Execution.Setup.a` equals `Restated.Vocabulary.Execution.Setup.a` at the
    model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.Setup.a_vocabulary_eq (S : Setup V) (r : Round) :
    _root_.DecoupledConsensusModel.Execution.Setup.a (V := V) S r = Restated.Vocabulary.Execution.Setup.a (V := V) Record.Model.vocabulary S r :=
  rfl

end

end DecoupledConsensusModel.Sts.Restated
