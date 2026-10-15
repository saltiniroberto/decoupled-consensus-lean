import Proofs.Vocabulary.Protocol.Handlers.Admission
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_CarriedAdmissionChecks
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Record.Wiring

/-!
# Admitting attestation rows

Admitting a new attestation row keeps the row, and admitting rows keeps the store's clock and slot,
stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedAdmission
open Protocol.NamedAdmission
open Execution

/-- If the erasure of `row` is not in the SG pool of `st` for its round and is in the pool after
    `M.on_sg_vote`, then `row` is among the rows of its round in the store `M.admit_row hc st row`. -/
theorem Vocabulary.Proofs.NamedAdmission.admitted_original_row (facts : Record.Facts M) (hc : Protocol.HealConfig) (st : M.NS)
    (row : NamedAttestation V) (hpre : row.erase ∉ (M.store_sg_pool st.core row.round))
    (hpost : row.erase ∈ (M.store_sg_pool (M.on_sg_vote hc st.core row.erase) row.round)) :
    row ∈ (M.admit_row hc st row).sg_rows row.round :=
  facts.hd.NamedAdmission_admitted_original_row hc st row hpre hpost

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedAdmission
open Protocol.NamedAdmission
open Execution

/-- Admitting the attestation rows `rows` into `st` keeps the store's time `t` and slot `s`. -/
theorem Vocabulary.Proofs.NamedAdmission.admit_rows_clock (facts : Record.Facts M) (hc : Protocol.HealConfig) (st : M.NS)
    (rows : List (NamedAttestation V)) :
    (M.admit_rows hc st rows).core.t = st.core.t ∧ (M.admit_rows hc st rows).core.s = st.core.s := by
  have h := facts.hd.admit_rows_core hc st rows
  rw [facts.hd.sameCore_t h, facts.hd.sameCore_s h]
  exact ⟨(Restated.Vocabulary.Proofs.CarriedAdmission.fold_rows_fixed_fields facts hc (rows.map NamedAttestation.erase) st.core).1,
    (Restated.Vocabulary.Proofs.CarriedAdmission.fold_rows_fixed_fields facts hc (rows.map NamedAttestation.erase) st.core).2.1⟩

end

end DecoupledConsensusModel.Sts.Restated
