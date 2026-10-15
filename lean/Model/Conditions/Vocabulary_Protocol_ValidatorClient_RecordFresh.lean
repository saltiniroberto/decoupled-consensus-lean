import Proofs.Vocabulary.Protocol.ValidatorClient.RecordFresh
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# A signing record fresh at a height

The condition that a signing record holds its initial values at a height, stated over a model
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
open Protocol (Record create_attestation height_pair own_lock record_attestation)
open Protocol (HealConfig)
open Internal
open Execution

/-- At height `H`, the signing record `Lambda` has no target, no timeout and no lock. -/
def Vocabulary.Proofs.HealingSurface.RecordFreshAt (M : Record.Model V) (Lambda : M.R) (H : Height) : Prop :=
  Lambda.target H = none ∧ Lambda.timeout H = false ∧ Lambda.lock H = none

end

end DecoupledConsensusModel.Sts.Restated
