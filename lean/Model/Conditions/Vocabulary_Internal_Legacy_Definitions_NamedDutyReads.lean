import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedDutyReads
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Record.Wiring

/-!
# Duty reads

A validator's prepared node states at the Goldfish vote time, the confirmation time and a round's
action time, as sets over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open Execution Proofs.HealingSurface

/-- The set of `v`'s prepared node states at the Goldfish vote time of slot `s`. -/
def Vocabulary.Internal.NamedRecoveryRead.voteDutyRead (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (v : V) (s : Slot) :
    DC.NDR M.N :=
  Restated.Vocabulary.Execution.NamedActionReads.confirmationReadAt M S rho v (M.vote_time S.E s)

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open Execution Proofs.HealingSurface

/-- The set of `v`'s prepared node states at the confirmation time of slot `s`. -/
def Vocabulary.Internal.NamedRecoveryRead.confirmationInputRead (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (v : V) (s : Slot) :
    DC.NDR M.N :=
  Restated.Vocabulary.Execution.NamedActionReads.confirmationReadAt M S rho v (M.confirmation_time S.E s)

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open Execution Proofs.HealingSurface

/-- The set of `v`'s prepared node states at round `r`'s action time, after the confirmation duty. -/
def Vocabulary.Internal.NamedRecoveryRead.actionDutyRead (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) :
    DC.NDR M.N :=
  Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open Execution Proofs.HealingSurface

/-- At the model `Record.Model.vocabulary`,
    `Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead` is the singleton of
    `DecoupledConsensusModel.Internal.NamedRecoveryRead.voteDutyRead`. -/
@[record_vocabulary]
theorem Vocabulary.Internal.NamedRecoveryRead.voteDutyRead_vocabulary_eq (S : Setup V) (rho : Run V) (v : V) (s : Slot) :
    Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) v s =
      {_root_.DecoupledConsensusModel.Internal.NamedRecoveryRead.voteDutyRead (V := V) S rho v s} :=
  Vocabulary.Execution.NamedActionReads.confirmationReadAt_vocabulary_eq S rho v _

/-- At the model `Record.Model.vocabulary`,
    `Restated.Vocabulary.Internal.NamedRecoveryRead.confirmationInputRead` is the singleton of
    `DecoupledConsensusModel.Internal.NamedRecoveryRead.confirmationInputRead`. -/
@[record_vocabulary]
theorem Vocabulary.Internal.NamedRecoveryRead.confirmationInputRead_vocabulary_eq (S : Setup V) (rho : Run V) (v : V) (s : Slot) :
    Restated.Vocabulary.Internal.NamedRecoveryRead.confirmationInputRead (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) v s =
      {_root_.DecoupledConsensusModel.Internal.NamedRecoveryRead.confirmationInputRead (V := V) S rho v s} :=
  Vocabulary.Execution.NamedActionReads.confirmationReadAt_vocabulary_eq S rho v _

/-- At the model `Record.Model.vocabulary`,
    `Restated.Vocabulary.Internal.NamedRecoveryRead.actionDutyRead` is the singleton of
    `DecoupledConsensusModel.Internal.NamedRecoveryRead.actionDutyRead`. -/
@[record_vocabulary]
theorem Vocabulary.Internal.NamedRecoveryRead.actionDutyRead_vocabulary_eq (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Restated.Vocabulary.Internal.NamedRecoveryRead.actionDutyRead (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) v r =
      {_root_.DecoupledConsensusModel.Internal.NamedRecoveryRead.actionDutyRead (V := V) S rho v r} :=
  Vocabulary.Proofs.HealingSurface.actionReadAt_vocabulary_eq S rho v r

end

end DecoupledConsensusModel.Sts.Restated
