import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.ClaimAsyncK_GstShift

/-!
# Reading an execution at another GST

An execution read as an execution of the protocol at a setup with another GST, stated over a model
`M : Record.Model V`.
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
open DecoupledConsensusModel.Protocol

/-- Given that `Record.protocolOf M` is the same at `setupWithGST S g hg` and at `S`, the execution
    `x` read as an execution of `Record.protocolOf M (setupWithGST S g hg)`, with the same
    configuration and action at every step. -/
def toGST (M : Record.Model V) (S : Setup V) (g : Int) (hg : 0 ≤ g)
    (hprot : Record.protocolOf M (setupWithGST S g hg) = Record.protocolOf M S) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) : AtomicExec (Record.protocolOf M (setupWithGST S g hg)) Sched where
  cfg := x.cfg
  lbl := x.lbl
  init := by rw [hprot]; exact x.init
  step := by rw [hprot]; exact x.step

end

end DecoupledConsensusModel.Sts.Restated
