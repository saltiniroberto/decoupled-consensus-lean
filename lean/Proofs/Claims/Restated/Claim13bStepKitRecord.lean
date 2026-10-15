import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Admission
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_Schedule_Alignment
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bStepKitRecord

/-!
# Admission of attestations and the store's round

The admission rule records an attestation, every store's slot is the slot of its clock, and its
named attestation rows project onto its core pool, stated over a model `M : Record.Model V` and its
facts `facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- An attestation whose round is within the store's expiry window, whose head the store does not
    already hold for its sender, and for whose sender the store holds fewer than two heads, is in
    the store's named bucket for its round after `M.admit_row`. -/
theorem on_sg_vote_records (facts : Record.Facts M) (hc : Protocol.HealConfig) (st : M.NS)
    (row : NamedAttestation V)
    (hwin : ¬ (row.round < (M.round_of hc st.core.s) - hc.η_SG ∨ (M.round_of hc st.core.s) < row.round))
    (hnew : row.erase.confirmed ∉ M.round_votes st.core row.erase)
    (hcard : (M.round_votes st.core row.erase).card ≠ 2) :
    row ∈ (M.admit_row hc st row).sg_rows row.round := by
  have hcond : ¬ (row.erase.round < (M.round_of hc st.core.s) - hc.η_SG ∨
      (M.round_of hc st.core.s) < row.erase.round ∨
      row.erase.confirmed ∈ M.round_votes st.core row.erase ∨
      (M.round_votes st.core row.erase).card = 2) := by
    rw [namedAttestation_erase_round]
    rintro (h | h | h | h)
    · exact hwin (Or.inl h)
    · exact hwin (Or.inr h)
    · exact hnew h
    · exact hcard h
  have hpre : row.erase ∉ (M.store_sg_pool st.core row.round) := by
    intro hmem
    exact hnew ((facts.hd.mem_round_votes_iff st.core row.erase _).mpr
      ⟨row.erase, by rw [namedAttestation_erase_round]; exact hmem, rfl, rfl⟩)
  have hgen : ∀ a : CombinedAttestation V,
      ¬ (a.round < (M.round_of hc st.core.s) - hc.η_SG ∨ (M.round_of hc st.core.s) < a.round ∨
          a.confirmed ∈ M.round_votes st.core a ∨
          (M.round_votes st.core a).card = 2) →
      a ∈ (M.store_sg_pool (M.on_sg_vote hc st.core a) a.round) := by
    intro a hg
    exact facts.hd.mem_on_sg_vote_sg_pool_of_not hc st.core a hg
  have hpost : row.erase ∈ (M.store_sg_pool (M.on_sg_vote hc st.core row.erase) row.round) := by
    have h := hgen row.erase hcond
    rwa [namedAttestation_erase_round] at h
  exact Restated.Vocabulary.Proofs.NamedAdmission.admitted_original_row facts hc st row hpre hpost

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- After any number of steps, every validator's store slot is the slot of its clock. -/
theorem slotOfClock_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (v : V) :
    (x[i][v].st).st.core.s = S.E.slotOf (x[i][v].st).st.core.t :=
  Record.inv_sts M S Sched x (fun n => n.st.core.s = S.E.slotOf n.st.core.t)
    (fun u => by
      show (M.initial (Setup.alwaysAwake S) u).st.core.s
        = S.E.slotOf (M.initial (Setup.alwaysAwake S) u).st.core.t
      rw [facts.nd.initial_st, facts.hd.initial_core_s, facts.hd.initial_core_t]
      exact (Proofs.ModelProperties.slotOf_zero (E := S.E)).symm)
    (fun m hm => by
      show (M.wake m).st.core.s = S.E.slotOf (M.wake m).st.core.t
      rw [(facts.nd.wake_st_record m).1]; exact hm)
    (fun u m t out hout _ => by
      show out.1.st.core.s = S.E.slotOf out.1.st.core.t
      rw [(facts.nd.tick_clock (Setup.alwaysAwake S) u m t out hout).1]
      exact (facts.nd.tick_clock (Setup.alwaysAwake S) u m t out hout).2)
    (fun m o m' hm' hm => by
      show m'.st.core.s = S.E.slotOf m'.st.core.t
      rw [(facts.nd.process_clock (Setup.alwaysAwake S) m o m' hm').1,
        (facts.nd.process_clock (Setup.alwaysAwake S) m o m' hm').2]
      exact hm)
    i v

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The round of a store's slot is the round of the slot of its clock. -/
theorem receiver_round_at_step (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (v : V) :
    (M.round_of S.hc (x[i][v].st).st.core.s)
      = (M.round_of S.hc (S.E.slotOf (x[i][v].st).st.core.t)) := by
  rw [Restated.slotOfClock_sts facts S Sched x i v]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every validator's store satisfies `PoolView`: the core bucket of a round is the erasure of the
    named bucket of that round. -/
theorem poolView_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (v : V) :
    Restated.Vocabulary.Proofs.NamedStore.PoolView M (x[i][v].st).st :=
  (Restated.nodeInvariant_sts facts S Sched x i v).1.1.1.2.2.2.1

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A named row a store holds in the bucket of its own round has its erasure in the core pool of
    that round. -/
theorem sgRow_erase_mem_pool_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (v : V) (row : NamedAttestation V)
    (hrow : row ∈ (x[i][v].st).st.sg_rows row.round) :
    row.erase ∈ (M.store_sg_pool (x[i][v].st).st.core row.round) :=
  facts.sto.pool_view_mem _ (Restated.poolView_sts facts S Sched x i v) row hrow

end

end DecoupledConsensusModel.Sts.Restated
