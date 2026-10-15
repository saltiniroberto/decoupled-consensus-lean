import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bInvariant

/-!
# Tick steps and the step before a time

Which step of an execution is the framework's tick at a given time, and which step is the last one
strictly before a given time, stated over a model `M : Record.Model V`.
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

/-- The label of step `n` of `x` is the tick of every awake validator at time `t` (the label's `Nat`
    time read as an `Int`). -/
def tickStepAt (M : Record.Model V) {S : Setup V} {Sched : Schedule V} (x : AtomicExec (Record.protocolOf M S) Sched)
    (n : Nat) (t : Int) : Prop :=
  ∃ t' : Nat, x.lbl n = AtomicAction.tickAllAwake t' ∧ (t' : Int) = t

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The step `m` is the last one strictly before time `c`: every step before `m` leads to a
    configuration with time less than `c`, and every step from `m` on leads to one with time at
    least `c`. -/
def stepBeforeInstant (M : Record.Model V) {S : Setup V} {Sched : Schedule V} (x : AtomicExec (Record.protocolOf M S) Sched)
    (m : Nat) (c : Int) : Prop :=
  (∀ k : Nat, k < m → (x[k + 1].time : Int) < c) ∧
    (∀ k : Nat, m ≤ k → c ≤ (x[k + 1].time : Int))

end

end DecoupledConsensusModel.Sts.Restated
