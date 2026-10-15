import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.RunAll

/-!
# The run of an execution

The run built from the events of an execution's first steps, and the path of that run the execution
follows, stated over a model `M : Record.Model V`.
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

/-- The events every validator contributes at step `k` of `x`, one validator after another in the
    order of `Finset.univ.toList`. -/
noncomputable def stepEvents (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (k : Nat) : List (Record.Event V) :=
  (Finset.univ : Finset V).toList.flatMap
    (fun v₀ => Record.actionEventsOf M S Sched v₀ (x[k].time : Int) (x.lbl k))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The events of every validator over the first `n` steps of `x`, in step order. -/
noncomputable def runEvents (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) : Nat → List (Record.Event V)
  | 0 => []
  | n + 1 => runEvents M S Sched x n ++ Restated.stepEvents M S Sched x n

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The run of every validator's events over the first `n` steps of `x`, with honest set `{v}`. -/
noncomputable def runAll (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (n : Nat) : Record.Run V :=
  { honest := {v}
    horizon := (x[n].time : Int)
    events := Restated.runEvents M S Sched x n }

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

open Classical in
/-- The path of the run `runAll M S Sched x v n` that the execution `x` follows: before the event
    `idx`, each validator `u` holds the node state `x` gives it after the steps whose events of `u`
    are `u`'s events among the first `idx` events of the run, or the woken node state
    `M.wake x[j][u].st` when the cut falls between `u`'s wake and its tick of one step `j`. -/
noncomputable def runAllPath (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (n : Nat) : Nat → V → M.N :=
  fun idx u =>
    if h : ∃ j : Nat, Record.veventsOf M S Sched x u j =
        ((Restated.runEvents M S Sched x n).take idx).filter
          (fun e => decide (Record.Event.node e = u))
    then x[Classical.choose h][u].st
    else if h' : ∃ j : Nat, ∃ t : DecoupledConsensusModel.Time,
        Record.veventsOf M S Sched x u j ++ [Record.Event.wake u t] =
          ((Restated.runEvents M S Sched x n).take idx).filter
            (fun e => decide (Record.Event.node e = u))
    then M.wake x[Classical.choose h'][u].st
    else M.initial (Setup.alwaysAwake S) u

end

end DecoupledConsensusModel.Sts.Restated
