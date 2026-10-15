import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Admissible
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Record.Wiring

/-!
# Root collision freedom

The condition that roots identify the blocks of a run, over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Execution

/-- Roots identify the blocks of `rho` read along the path `W`. -/
abbrev Vocabulary.Execution.RootCollisionFree (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) : Prop := Restated.Vocabulary.Execution.NamedRootCollisionFree M S rho W

end

end DecoupledConsensusModel.Sts.Restated
