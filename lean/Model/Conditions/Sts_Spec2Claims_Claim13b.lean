import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# The validators active in a round

The validators awake throughout the window in which a round's attestations are formed, stated over a
model `M : Record.Model V`.
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

/-- The validators awake throughout the `4Δ` window ending at round `r`'s action instant. -/
def activeRound (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (r : Nat) : Finset V :=
  Sched.awakeThroughout ((M.a S.hc S.E.Δ r) - 4 * S.E.Δ) ((M.a S.hc S.E.Δ r))

end

end DecoupledConsensusModel.Sts.Restated
