import Proofs.Vocabulary.Protocol.Grades.RowTrace
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Record.Wiring

/-!
# The world before a time as the world before an event

In a run with sorted events, the worlds before a time are the worlds before the event whose index
counts the events strictly before that time, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution DecoupledConsensusModel.Protocol

/-- If the events of `rho` are sorted by key, the worlds before time `t` are the worlds before the
    event whose index is the number of events of `rho` strictly before `t`. -/
theorem Vocabulary.Proofs.NamedOutageClosure.strict_read_eq_index (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (t : Time) :
    Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t =
      Record.stateBeforeOf M S rho (rho.events.filter (fun e => decide (e.time < t))).length :=
  congrArg (fun events => events.foldlM (Record.worldStepOf M S) (fun v => M.initial S v))
    (Restated.filter_eq_take_of_sorted hsorted _ (Restated.downward_lt t))

end

end DecoupledConsensusModel.Sts.Restated
