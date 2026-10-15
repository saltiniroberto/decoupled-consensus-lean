import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bSGCompatible
import Model.Record.Wiring

/-!
# The opening time of the switch round

The time `switchOpening`, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The time at which round `switchRound M S tE` opens. -/
noncomputable def switchOpening (M : Record.Model V) (S : Setup V) (tE : Int) : Int :=
  M.opening S.E S.hc (Restated.switchRound M S tE)

end

end DecoupledConsensusModel.Sts.Restated
