import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Run
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Record.Wiring

/-!
# Run states and stores before a time

The worlds and stores that can hold before a time, and names for emission, processing, acceptance
and the blocks of a run, over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.Run

/-- Another name for `Restated.Vocabulary.Execution.NamedRun.readAt`. -/
abbrev Vocabulary.Execution.Run.stateAt (M : Record.Model V) := @Restated.Vocabulary.Execution.NamedRun.readAt _ _ _ M

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.Run

/-- Another name for `Restated.Vocabulary.Execution.NamedRun.readAt`. -/
abbrev Vocabulary.Execution.Run.readAt (M : Record.Model V) := @Restated.Vocabulary.Execution.NamedRun.readAt _ _ _ M

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.Run

/-- The set of worlds that can hold after the events of `rho` whose time is before `t`. -/
abbrev Vocabulary.Execution.Run.stateBeforeTime (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (t : Time) :
    DC.NDR (V → M.N) :=
  Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.Run

/-- Along the path `W` of `rho`, `v`'s tick at `t` sends `o`. -/
abbrev Vocabulary.Execution.Run.emits (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (v : V) (o : Object V) (t : Time) : Prop :=
  Restated.Vocabulary.Execution.NamedRun.emits M S rho W v o t

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.Run

/-- Another name for `Restated.Vocabulary.Execution.NamedRun.processes`. -/
abbrev Vocabulary.Execution.Run.processes (M : Record.Model V) := @Restated.Vocabulary.Execution.NamedRun.processes _ _ _ M

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.Run

/-- Another name for `Restated.Vocabulary.Execution.NamedRun.acceptsAt`. -/
abbrev Vocabulary.Execution.Run.acceptsAt (M : Record.Model V) := @Restated.Vocabulary.Execution.NamedRun.acceptsAt _ _ _ M

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.Run

/-- The set of `v`'s stores in every world that can hold after the events of `rho` whose time is
    before `t`. -/
def Vocabulary.Execution.Run.storeBeforeTime (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (v : V) (t : Time) :
    DC.NDR M.NS :=
  (fun w => (w v).st) '' Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t

end

section
open DecoupledConsensusModel.Execution

/-- Another name for `Restated.Vocabulary.Execution.NamedRun.blockInRun`, used as
    `RunBlock M S rho W A`. -/
abbrev Vocabulary.Execution.RunBlock (M : Record.Model V) := @Restated.Vocabulary.Execution.NamedRun.blockInRun _ _ _ M

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.Run

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Execution.Run.stateAt` is the singleton
    of `DecoupledConsensusModel.Execution.Run.stateAt`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.Run.stateAt_vocabulary_eq (S : Setup V) (rho : NamedRun V) (t : Time) :
    Restated.Vocabulary.Execution.Run.stateAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) t =
      {_root_.DecoupledConsensusModel.Execution.Run.stateAt (V := V) S rho t} :=
  Vocabulary.Execution.NamedRun.readAt_vocabulary_eq S rho t

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Execution.Run.readAt` is the singleton
    of `DecoupledConsensusModel.Execution.Run.readAt`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.Run.readAt_vocabulary_eq (S : Setup V) (rho : NamedRun V) (t : Time) :
    Restated.Vocabulary.Execution.Run.readAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) t =
      {_root_.DecoupledConsensusModel.Execution.Run.readAt (V := V) S rho t} :=
  Vocabulary.Execution.NamedRun.readAt_vocabulary_eq S rho t

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Execution.Run.stateBeforeTime` is the
    singleton of `DecoupledConsensusModel.Execution.Run.stateBeforeTime`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.Run.stateBeforeTime_vocabulary_eq (S : Setup V) (rho : Run V) (t : Time) :
    Restated.Vocabulary.Execution.Run.stateBeforeTime (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) t =
      {_root_.DecoupledConsensusModel.Execution.Run.stateBeforeTime (V := V) S rho t} :=
  Vocabulary.Execution.NamedRun.stateBeforeTime_vocabulary_eq S rho t

/-- `DecoupledConsensusModel.Execution.Run.emits` holds exactly when
    `Restated.Vocabulary.Execution.Run.emits` holds at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.Run.emits_vocabulary_eq (S : Setup V) (rho : Run V) (v : V) (o : Object V) (t : Time) :
    _root_.DecoupledConsensusModel.Execution.Run.emits (V := V) S rho v o t ↔
      Restated.Vocabulary.Execution.Run.emits (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) v o t :=
  Vocabulary.Execution.NamedRun.emits_vocabulary_eq S rho v o t

/-- `DecoupledConsensusModel.Execution.Run.processes` holds exactly when
    `Restated.Vocabulary.Execution.Run.processes` holds at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.Run.processes_vocabulary_eq (S : Setup V) (rho : NamedRun V) (v : V) (o : NamedObject V) (t : Time) :
    _root_.DecoupledConsensusModel.Execution.Run.processes (V := V) S rho v o t ↔
      Restated.Vocabulary.Execution.Run.processes (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) v o t :=
  Vocabulary.Execution.NamedRun.processes_vocabulary_eq S rho v o t

/-- `DecoupledConsensusModel.Execution.Run.acceptsAt` holds exactly when
    `Restated.Vocabulary.Execution.Run.acceptsAt` holds at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.Run.acceptsAt_vocabulary_eq (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V) (o : NamedObject V) (t : Time) :
    _root_.DecoupledConsensusModel.Execution.Run.acceptsAt (V := V) S rho i v o t ↔
      Restated.Vocabulary.Execution.Run.acceptsAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) i v o t :=
  Vocabulary.Execution.NamedRun.acceptsAt_vocabulary_eq S rho i v o t

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Execution.Run.storeBeforeTime` is the
    singleton of `DecoupledConsensusModel.Execution.Run.storeBeforeTime`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.Run.storeBeforeTime_vocabulary_eq (S : Setup V) (rho : Run V) (v : V) (t : Time) :
    Restated.Vocabulary.Execution.Run.storeBeforeTime (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) v t =
      {_root_.DecoupledConsensusModel.Execution.Run.storeBeforeTime (V := V) S rho v t} := by
  rw [Restated.Vocabulary.Execution.Run.storeBeforeTime,
    Vocabulary.Execution.NamedRun.stateBeforeTime_vocabulary_eq]
  exact Set.image_singleton

/-- `DecoupledConsensusModel.Execution.RunBlock` holds exactly when
    `Restated.Vocabulary.Execution.RunBlock` holds at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.RunBlock_vocabulary_eq (S : Setup V) (rho : NamedRun V) (A : NamedBlock V) :
    _root_.DecoupledConsensusModel.Execution.RunBlock (V := V) S rho A ↔
      Restated.Vocabulary.Execution.RunBlock (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => _root_.DecoupledConsensusModel.Execution.NamedRun.stateBefore S rho i) A :=
  Vocabulary.Execution.NamedRun.blockInRun_vocabulary_eq S rho A

end

end DecoupledConsensusModel.Sts.Restated
