import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Event
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring
import Proofs.Vocabulary.ModelVocabularyFacts

/-!
# World step

The set of worlds one event can lead to, over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.World

/-- The set of worlds after the event `e`, given the world `w` before it. -/
abbrev Vocabulary.Execution.World.step (M : Record.Model V) (S : Setup V) (w : V → M.N) (e : Record.Event V) :
    DC.NDR (V → M.N) :=
  Record.worldStepOf M S w e

end

end DecoupledConsensusModel.Sts.Restated
