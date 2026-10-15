import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring
import Proofs.Vocabulary.ModelVocabularyFacts

/-!
# Executions that reach every instant

The condition that an execution reaches every instant, stated over a model `M : Record.Model V`.
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

/-- Every instant is reached by the execution: for every instant `t`, some configuration of `x` has
    real time at least `t`. -/
def ReachesEveryInstant (M : Record.Model V) {S : Setup V} {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) : Prop :=
  ∀ t : Int, ∃ i : Nat, t ≤ (x[i].time : Int)

end

end DecoupledConsensusModel.Sts.Restated
