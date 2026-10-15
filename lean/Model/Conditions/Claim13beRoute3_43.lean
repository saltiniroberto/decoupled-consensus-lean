import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.RunAll
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_43

/-!
# Cutting an execution at an instant

The condition `CutAt` relating the first `m` and the first `n` steps of an execution over a model
`M : Record.Model V` at an instant `T`.
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
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- `m ≤ n`, the configuration after `m` steps is at `T`, and the events of the first `n` steps are
    those of the first `m` steps followed by events strictly after `T`. -/
structure CutAt (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (m n : Nat) (T : Int) : Prop where
  le : m ≤ n
  time_eq : (x[m].time : Int) = T
  late : ∃ l : List (Record.Event V), Restated.runEvents M S Sched x n = Restated.runEvents M S Sched x m ++ l ∧
    ∀ e ∈ l, T < Record.Event.time e

end

end DecoupledConsensusModel.Sts.Restated
