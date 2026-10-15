import Proofs.Vocabulary.Protocol.ValidatorClient.Record
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Consistency of the timeout history

The condition that a named signing record's timeout flags agree with its timeout history, stated
over a model `M : Record.Model V`, and its agreement with the definition of the same name at
`Record.Model.vocabulary`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedRecord
open Protocol
open Protocol.NamedRecord
open Proofs.HealingSurface
open Proofs.Records (LockCompatible)

/-- At every height `h`, the signing record part of `record` has voted a timeout at `h` exactly when
    the timeout history of `record` holds a pair of `h` and some block. -/
def Vocabulary.Proofs.NamedRecord.HistoryConsistent (M : Record.Model V) (record : M.NR) : Prop :=
  ∀ h, record.legacy.timeout h = true ↔ ∃ entry, (h, entry) ∈ record.timeoutHistory

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedRecord
open Protocol
open Protocol.NamedRecord
open Proofs.HealingSurface
open Proofs.Records (LockCompatible)

/-- `DecoupledConsensusModel.Proofs.NamedRecord.HistoryConsistent` holds exactly when its form over
    the record holds at `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.NamedRecord.HistoryConsistent_vocabulary_eq (record : Protocol.NamedRecord) :
    _root_.DecoupledConsensusModel.Proofs.NamedRecord.HistoryConsistent record ↔ Restated.Vocabulary.Proofs.NamedRecord.HistoryConsistent (V := V) Record.Model.vocabulary record :=
  Iff.rfl

end

end DecoupledConsensusModel.Sts.Restated
