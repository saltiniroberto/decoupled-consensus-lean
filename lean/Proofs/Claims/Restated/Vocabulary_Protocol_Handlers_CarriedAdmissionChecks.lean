import Proofs.Vocabulary.Protocol.Handlers.CarriedAdmissionChecks
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_Schedule
import Model.Record.Wiring

/-!
# Fields the attestation-row fold keeps

Folding attestation rows into a store keeps its clock, slot, tree, block stamps, Goldfish votes and
vote stamps, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.CarriedAdmission
open DecoupledConsensusModel
open Protocol
open Internal Execution

/-- Folding the rows `rows` into `st` with `M.on_sg_vote` keeps the store's `t`, `s`, `T`,
    `timestamp_block`, `gf_votes` and `timestamp_vote`. -/
theorem Vocabulary.Proofs.CarriedAdmission.fold_rows_fixed_fields (facts : Record.Facts M) (hc : Protocol.HealConfig)
    (rows : List (CombinedAttestation V)) (st : M.S) :
    let out := rows.foldl (M.on_sg_vote hc) st
    out.t = st.t ∧ out.s = st.s ∧ out.T = st.T ∧
      out.timestamp_block = st.timestamp_block ∧ out.gf_votes = st.gf_votes ∧
      out.timestamp_vote = st.timestamp_vote := by
  induction rows generalizing st with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons a rows ih =>
    simpa only [List.foldl_cons, facts.hd.on_sg_vote_time, facts.hd.on_sg_vote_slot,
      facts.hd.on_sg_vote_T, facts.hd.on_sg_vote_timestamp_block,
      facts.hd.on_sg_vote_gf_votes, facts.hd.on_sg_vote_timestamp_vote]
      using ih (M.on_sg_vote hc st a)

end

end DecoupledConsensusModel.Sts.Restated
