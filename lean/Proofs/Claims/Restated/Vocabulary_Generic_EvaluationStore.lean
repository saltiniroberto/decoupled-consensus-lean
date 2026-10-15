import Proofs.Vocabulary.Generic.EvaluationStore
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Internal_Definitions_NamedResult23Statements
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_Store
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Record.Wiring

/-!
# Action rounds, pooled attestations and the confirmation path

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: a round whose
action time is before a slot's proposal time is no later than that slot's round, an attestation of a
store's SG pool is in the list the proposal constructor reads, and the blocks between the
confirmation anchor and a candidate block are in the candidate tree.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Protocol
open Internal
open Execution
open Protocol (derive_named)
open Internal.NamedRecoveryRead

/-- If round `r`'s action time is before slot `s`'s proposal time, `r` is at most the round of `s`. -/
theorem Vocabulary.Protocol.action_round_le_of_lt_proposal (facts : Record.Facts M)
    (S : Setup V) {r : Round} {s : Slot}
    (hlt : (Restated.Vocabulary.Execution.Setup.a M S r) < M.proposal_time S.E s) :
    r ≤ (M.round_of S.hc s) :=
  facts.sch.action_round_le_of_lt_proposal S hlt

end

section
open DecoupledConsensusModel.Protocol
open Internal
open Execution
open Protocol (derive_named)
open Internal.NamedRecoveryRead

/-- An attestation in the store's SG pool for its round, whose round is at most the round of the
    store's current slot, is in the store's processed attestations, the list the proposal
    constructor reads. -/
theorem Vocabulary.Protocol.mem_processed_attestations_of_pool (facts : Record.Facts M)
    (hc : Protocol.HealConfig) (st : M.S)
    {a : CombinedAttestation V} (ha : a ∈ (M.store_sg_pool st a.round))
    (hr : a.round ≤ (M.round_of hc st.s)) :
    a ∈ st.processed_attestations hc := by
  unfold Record.Model.S.processed_attestations
  apply List.mem_flatMap.mpr
  refine ⟨a.round, ?_, (facts.sto.ModelProperties_mem_sg_pool_iff st a.round a).1 ha⟩
  exact List.mem_range.mpr (Nat.lt_succ_of_le hr)

end

section
open DecoupledConsensusModel.Protocol
open Internal
open Execution
open Protocol (derive_named)
open Internal.NamedRecoveryRead

/-- For every world `w` that can hold just before slot `s`'s confirmation time `t`, and every
    outcome `c` of the phase tick on `v`'s cache in `w` at `t`, if `B` is in the candidate tree of
    the store the slot-`s` evaluation reads in `w`, then for every outcome `A` of the anchor of the
    confirmation read built from `v`'s node state in `w` with the cache `c`, every block that is a
    descendant of `A`, differs from it, and is an ancestor of `B`, is in that candidate tree too. -/
theorem Vocabulary.Protocol.confPath_of_candidate (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} {s : Slot} {v : V} {B : NamedBlock V} :
    ∀ w ∈ Restated.Vocabulary.Execution.Run.stateBeforeTime M S rho (M.confirmation_time S.E s),
    ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc (w v).st.core.toHealing (M.confirmation_time S.E s) (w v).cache ⇢ c →
    B.erase ∈ Restated.Vocabulary.Protocol.confTree M
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (w v).st.core (M.confirmation_time S.E s)) →
    ∀ A : Block V,
      Restated.Vocabulary.Internal.namedConfirmationAnchor M S
        (M.mkNode (M.ns_setClock S.E (w v).st (M.confirmation_time S.E s)) (w v).record c) ⇢ A →
    ∀ C : Block V,
      Block.Preceq A C →
      C ≠ A →
      Block.Preceq C B.erase →
      C ∈ Restated.Vocabulary.Protocol.confTree M
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (w v).st.core (M.confirmation_time S.E s)) := by
  intro w hw c hc hB A hA C hAC _ hCB
  let t := M.confirmation_time S.E s
  -- the candidate tree does not read the clock or the slot `tickStore` stamps
  have hct : Restated.Vocabulary.Protocol.confTree M
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (w v).st.core t)
      = M.get_filtered_block_tree (M.toHealing (w v).st.core).toFG :=
    facts.fc.get_filtered_block_tree_toHealing_clock _ _ _
  rw [hct] at hB ⊢
  have hpc : Restated.Vocabulary.Internal.ParentClosed M (w v).st.core :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho t v w hw
  have hFJ : Block.Preceq (w v).st.core.F (w v).st.core.J :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts S rho t v w hw
  unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
  have hBT : B.erase ∈ (M.toHealing (w v).st.core).toFG.toSG.toGoldfishStore.T :=
    facts.fc.get_filtered_block_tree_subset (M.toHealing (w v).st.core).toFG hB
  have hCT : C ∈ (M.toHealing (w v).st.core).toFG.toSG.toGoldfishStore.T := by
    apply Proofs.Records.mem_of_preceq hpc.2 C B.erase
    · exact hBT
    · exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hCB
  apply facts.fc.mem_filtered_of_preceq
    (st := (M.toHealing (w v).st.core).toFG)
    (by
      rw [facts.sto.ModelProperties_toHealing_F, facts.sto.ModelProperties_toHealing_J]
      exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hFJ)
    hB hCT
    (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hCB)
  apply Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr
  -- the FG root of the stored store is the FG root of the confirmation read's store
  have hroot : M.get_fg_root (M.toHealing (w v).st.core).toFG
      = M.get_fg_root (M.toHealing (M.mkNode (M.ns_setClock S.E (w v).st t) (w v).record c).st.core).toFG := by
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.setClock_core_eq_store_with_t_s]
    exact (facts.fc.get_fg_root_toHealing_clock _ _ _).symm
  rw [hroot]
  exact Proofs.ModelProperties.Preceq_trans
    (facts.fc.fg_root_Preceq_get_sg_root_with_gradeContract
      (M.mkNode (M.ns_setClock S.E (w v).st t) (w v).record c).cache S.E S.hc
      (M.toHealing (M.mkNode (M.ns_setClock S.E (w v).st t) (w v).record c).st.core)
      ((M.round_of S.hc (M.mkNode (M.ns_setClock S.E (w v).st t) (w v).record c).st.core.s)) A hA) hAC

end

end DecoupledConsensusModel.Sts.Restated
