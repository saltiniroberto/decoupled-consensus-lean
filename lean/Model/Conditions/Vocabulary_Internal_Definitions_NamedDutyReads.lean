import Proofs.Vocabulary.Internal.Definitions.NamedDutyReads
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# Duty reads of a run

The node states a proposer hands its proposal duty and the core stores a voter's vote duty reads, as
sets over a model `M : Record.Model V`, and their counterparts at `Record.Model.vocabulary`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation
open Execution Proofs.HealingSurface

/-- The set of node states the proposer of slot `s` can hand its proposal duty in `rho`. -/
def Vocabulary.Internal.NamedRecoveryRead.proposalDutyRead (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (s : Slot) :
    DC.NDR M.N :=
  Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho s

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation
open Execution Proofs.HealingSurface

/-- The set of core stores `n.st.core`, for every node state `n` that `v`'s vote duty of slot `s`
    can read in `rho`. -/
def Vocabulary.Internal.NamedRecoveryRead.voteDutyStore (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (v : V) (s : Slot) :
    DC.NDR M.S :=
  (fun n => n.st.core) '' Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho v s

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation
open Execution Proofs.HealingSurface

/-- At `Record.Model.vocabulary` and a run embedded by `Record.Run.ofVocabulary`, the restated
    `proposalDutyRead` is the singleton of the value of
    `DecoupledConsensusModel.Internal.NamedRecoveryRead.proposalDutyRead` at the embedded run. -/
@[record_vocabulary]
theorem Vocabulary.Internal.NamedRecoveryRead.proposalDutyRead_vocabulary_eq (S : Setup V) (rho : Run V) (s : Slot) :
    Restated.Vocabulary.Internal.NamedRecoveryRead.proposalDutyRead (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) s =
      {_root_.DecoupledConsensusModel.Internal.NamedRecoveryRead.proposalDutyRead (V := V) S rho s} :=
  Vocabulary.Statements.Instantiation.proposerReadAt_vocabulary_eq S rho s

/-- At `Record.Model.vocabulary` and a run embedded by `Record.Run.ofVocabulary`, the restated
    `voteDutyStore` is the singleton of the value of
    `DecoupledConsensusModel.Internal.NamedRecoveryRead.voteDutyStore` at the embedded run. -/
@[record_vocabulary]
theorem Vocabulary.Internal.NamedRecoveryRead.voteDutyStore_vocabulary_eq (S : Setup V) (rho : Run V) (v : V) (s : Slot) :
    Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyStore (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) v s =
      {_root_.DecoupledConsensusModel.Internal.NamedRecoveryRead.voteDutyStore (V := V) S rho v s} := by
  rw [Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyStore,
    Vocabulary.Internal.NamedRecoveryRead.voteDutyRead_vocabulary_eq]
  exact Set.image_singleton

end

end DecoupledConsensusModel.Sts.Restated
