import Proofs.Vocabulary.Protocol.ValidatorClient.TickRecord
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Records
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_Record
import Model.Record.Wiring

/-!
# The invariant of a named signing record

The invariant of a named signing record, stated over a model `M : Record.Model V`, and its agreement
with the definition of the same name at `Record.Model.vocabulary`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedTickRecord

/-- The timeout history of `record` is consistent with its timeout votes (`HistoryConsistent`), and
    the signing record part of `record` is `LockCompatible`. -/
def Vocabulary.Proofs.NamedTickRecord.Invariant (M : Record.Model V) (record : M.NR) : Prop :=
  Restated.Vocabulary.Proofs.NamedRecord.HistoryConsistent M record ∧ Restated.Vocabulary.Proofs.Records.LockCompatible M record.legacy

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedTickRecord

/-- `DecoupledConsensusModel.Proofs.NamedTickRecord.Invariant` holds exactly when its form over the
    record holds at `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.NamedTickRecord.Invariant_vocabulary_eq (record : Protocol.NamedRecord) :
    _root_.DecoupledConsensusModel.Proofs.NamedTickRecord.Invariant record ↔ Restated.Vocabulary.Proofs.NamedTickRecord.Invariant (V := V) Record.Model.vocabulary record :=
  Iff.rfl

end

end DecoupledConsensusModel.Sts.Restated
