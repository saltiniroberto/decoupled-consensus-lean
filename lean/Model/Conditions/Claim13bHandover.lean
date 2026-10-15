import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Sts_Constants
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bHandover

/-!
# The length of the healing phase

The length `healingLength` of the healing phase, stated over a model `M : Record.Model V`.
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

/-- The length of the healing phase for `gap`: the finality startup lag, then `gap` rounds and the
    finality deadline, then one more round. -/
noncomputable def healingLength (M : Record.Model V) (S : Setup V) (gap : Nat) : Int :=
  (Restated.constants M S).finalityStartup gap + (gap : Int) * (Restated.constants M S).period +
    (Restated.constants M S).finalityDeadline gap + (Restated.constants M S).period

end

end DecoupledConsensusModel.Sts.Restated
