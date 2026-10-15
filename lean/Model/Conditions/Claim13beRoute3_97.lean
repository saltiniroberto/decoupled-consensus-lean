import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Sts_Constants
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_97

/-!
# The finality deadline

The finality deadline at sharp spacing, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- The finality deadline: `3 · gap + timeoutDelay / R − 5` periods, plus `14Δ`. -/
noncomputable def finalityDeadlineSharpLanded_f7 (M : Record.Model V) (S : Setup V) (gap : Nat) : Int :=
  ((3 * gap + S.cfg.timeoutDelay / S.hc.R - 5 : Nat) : Int) * (Restated.constants M S).period + 14 * S.E.Δ

end

end DecoupledConsensusModel.Sts.Restated
