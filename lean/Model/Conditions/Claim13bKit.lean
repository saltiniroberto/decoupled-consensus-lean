import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bHandover
import Model.Conditions.Sts_Constants
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bKit

/-!
# The healing length with the SG expiry rounds

The length `healingLengthη`, stated over a model `M : Record.Model V`.
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

/-- The healing length `healingLength M S gap` plus `S.hc.η_SG` more rounds. -/
noncomputable def healingLengthη (M : Record.Model V) (S : Setup V) (gap : Nat) : Int :=
  Restated.healingLength M S gap + (S.hc.η_SG : Int) * (Restated.constants M S).period

end

end DecoupledConsensusModel.Sts.Restated
