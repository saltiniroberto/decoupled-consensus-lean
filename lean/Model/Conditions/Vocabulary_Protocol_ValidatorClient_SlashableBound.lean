import Proofs.Vocabulary.Protocol.ValidatorClient.SlashableBound
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# The signing record after a finality pair

The state of a signing record at a height after it emits a finality pair, stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (Record create_attestation finality_pair height_pair
  record_attestation)
open Internal
open Execution

/-- At height `h`, the signing record `Lambda` has no timeout and its lock is `T`. -/
def Vocabulary.Proofs.HealingSurface.FinalitySafeAt (M : Record.Model V) (Lambda : M.R) (h : Height) (T : BlockId) : Prop :=
  Lambda.timeout h = false ∧ Lambda.lock h = some T

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (Record create_attestation finality_pair height_pair
  record_attestation)
open Internal
open Execution

end

end DecoupledConsensusModel.Sts.Restated
