import Proofs.Vocabulary.Internal.Internal.GradeReads
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Grade reads before a round's action time

The healing store and the grade view a validator can hold just before round `r`'s action time, each
as a set over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open Execution Protocol

/-- The set of healing stores `v` can hold just before round `r`'s action time. -/
def Vocabulary.Internal.HealingSurface.healStoreAt (M : Record.Model V) (S : Setup V) (ρ : Record.Run V) (v : V) (r : Round) :
    DC.NDR M.HS :=
  (fun ns => M.toHealing ns.core) ''
    Restated.Vocabulary.Execution.Run.storeBeforeTime M S ρ v ((Restated.Vocabulary.Execution.Setup.a M S r))

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open Execution Protocol

/-- The set of the grade views of the healing stores in `healStoreAt M S ρ v r`. -/
def Vocabulary.Internal.HealingSurface.gradeViewAt (M : Record.Model V) (S : Setup V) (ρ : Record.Run V) (v : V) (r : Round) :
    DC.NDR M.GV :=
  M.gradeView '' Restated.Vocabulary.Internal.HealingSurface.healStoreAt M S ρ v r

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open Execution Protocol

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Internal.HealingSurface.healStoreAt` is
    the singleton of `DecoupledConsensusModel.Internal.HealingSurface.healStoreAt`. -/
@[record_vocabulary]
theorem Vocabulary.Internal.HealingSurface.healStoreAt_vocabulary_eq (S : Setup V) (ρ : Run V) (v : V) (r : Round) :
    Restated.Vocabulary.Internal.HealingSurface.healStoreAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary ρ) v r =
      {_root_.DecoupledConsensusModel.Internal.HealingSurface.healStoreAt (V := V) S ρ v r} := by
  rw [Restated.Vocabulary.Internal.HealingSurface.healStoreAt, Vocabulary.Execution.Run.storeBeforeTime_vocabulary_eq]
  exact Set.image_singleton

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Internal.HealingSurface.gradeViewAt` is
    the singleton of `DecoupledConsensusModel.Internal.HealingSurface.gradeViewAt`. -/
@[record_vocabulary]
theorem Vocabulary.Internal.HealingSurface.gradeViewAt_vocabulary_eq (S : Setup V) (ρ : Run V) (v : V) (r : Round) :
    Restated.Vocabulary.Internal.HealingSurface.gradeViewAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary ρ) v r =
      {_root_.DecoupledConsensusModel.Internal.HealingSurface.gradeViewAt (V := V) S ρ v r} := by
  rw [Restated.Vocabulary.Internal.HealingSurface.gradeViewAt, Vocabulary.Internal.HealingSurface.healStoreAt_vocabulary_eq]
  exact Set.image_singleton

end

end DecoupledConsensusModel.Sts.Restated
