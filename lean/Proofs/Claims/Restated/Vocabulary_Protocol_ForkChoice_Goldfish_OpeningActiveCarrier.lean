import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_GradeFormsProducers
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# The proposal parent is in the filtered tree

The parent a proposer selects is in the filtered block tree of its store, stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal
open Execution
open Internal.HealingSurface
open Protocol

/-- For every node state `n` slot `s`'s proposer can hold at slot `s`'s proposal time, and every
    proposal input `input` computed from `n`, the parent field of `input` is in the filtered block
    tree of `n`'s store. -/
theorem Vocabulary.Proofs.HealingSurface.selectedOpeningProposedParent_mem_filtered (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (s : Slot) :
    ∀ n ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho s,
    ∀ input : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract n.cache) S.E S.hc
        (S.node (S.E.proposer s)) (M.toHealing n.st.core) ⇢ input →
    input.parent ∈
      M.get_filtered_block_tree
        (M.toHealing n.st.core).toFG := by
  intro n hn input hinput
  let st := (M.toHealing n.st.core)
  let gc := M.gradeContract n.cache
  have hroot : M.get_fg_root st.toFG ∈
      M.get_filtered_block_tree st.toFG := by
    show M.get_fg_root (M.toHealing n.st.core).toFG ∈
      M.get_filtered_block_tree (M.toHealing n.st.core).toFG
    obtain ⟨w, hw, c, -, rfl⟩ := hn
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.setClock_core_eq_store_with_t_s]
    have h1 := facts.fc.get_filtered_block_tree_toHealing_clock (w (S.E.proposer s)).st.core
      (M.proposal_time S.E s) (S.E.slotOf (M.proposal_time S.E s))
    have h2 := facts.fc.get_fg_root_toHealing_clock (w (S.E.proposer s)).st.core
      (M.proposal_time S.E s) (S.E.slotOf (M.proposal_time S.E s))
    simp only [Record.Model.S.toHealing] at h1 h2
    rw [h1, h2]
    exact Restated.Vocabulary.Proofs.HealingSurface.named_fgRoot_mem_filtered_stateBeforeTime facts S rho
      (M.proposal_time S.E s) (S.E.proposer s) w hw
  obtain ⟨L, hL⟩ := facts.fc.proposer_support_view_nonempty st.toFG.toSG.toGoldfishStore
    st.toFG.toSG.toGoldfishStore.s
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty gc S.E S.hc st
    (M.round_of S.hc st.toFG.toSG.toGoldfishStore.s)
  obtain ⟨H, hH⟩ := facts.fc.get_head_with_nonempty gc S.E S.hc st
    (M.proposer_view st.toFG.toSG.toGoldfishStore st.toFG.toSG.toGoldfishStore.s).toFinset
    L.toFinset (st.toFG.toSG.toGoldfishStore.s - 1)
  have hanchor : R ∈ M.get_filtered_block_tree st.toFG :=
    facts.fc.get_sg_root_with_gradeContract_mem_filtered n.cache S.E S.hc st _ hroot R hR
  have hhead : H ∈ M.get_filtered_block_tree st.toFG :=
    facts.fc.get_head_with_mem_filtered gc S.E S.hc st _ _ _ R hR hanchor H hH
  rw [facts.dt.with_proposal_input_id_parent gc S.E S.hc (S.node (S.E.proposer s)) st input
    hinput L hL H hH]
  exact hhead

end

end DecoupledConsensusModel.Sts.Restated
