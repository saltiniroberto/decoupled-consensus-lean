import Proofs.Vocabulary.Protocol.Grades.Q31_actionSGBlock_tiers
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The cases of a round action's SG block

The SG block a round action selects satisfies `Q31_actionSGBlock_tiers`, stated over a model
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
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.HealingLemmas.Rows
open Internal Execution Internal.PhaseGrades Proofs.HealingSurface

/-- In every run `rho`, the SG block the action selects from each node state `v` can hold at round
    `r`'s action is in one of the four cases of `Q31_actionSGBlock_tiers`. -/
theorem Vocabulary.Proofs.HealingLemmas.Rows.q31_actionsgblock_tiers (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) :
    Restated.Vocabulary.Internal.PhaseGrades.Q31_actionSGBlock_tiers M S rho := by
  intro v r n hn grades hg
  obtain ⟨w, -, hn⟩ := hn
  have hk : M.round_of S.hc (M.toHealing n.st.core).s = r := by
    obtain ⟨c, hc, st₀, hst, rfl⟩ := hn
    show M.round_of S.hc (M.toHealing (M.mkNode st₀ (w v).record c).st.core).toFG.toSG.toGoldfishStore.s = r
    rewrite [facts.sto.toHealing_s, facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [(facts.dt.named_confirmation_clock _ _ _ _ _ st₀ hst).2,
      facts.hd.ModelProperties_setClock_core_s]
    exact Restated.Vocabulary.Proofs.HealingLemmas.round_of_slotOf_a facts S r
  have hlc : (M.toHealing n.st.core).live_confirmed = n.st.core.live_confirmed :=
    facts.sto.toHealing_live_confirmed n.st.core
  dsimp only
  intro g2 hg2 B hB
  rw [hk] at hg2 hB
  have hBeq : B = M.currentSGVote (M.toHealing n.st.core) grades :=
    facts.dt.get_sg_vote_with_gradeContract_grade2 n.cache S.E S.hc (M.toHealing n.st.core) r
      g2 hg2 grades hg B hB
  subst hBeq
  set st := M.toHealing n.st.core with hst_def
  rcases hdc : M.deepest_clear (some grades.anchor) st.live_confirmed grades.clear
      with _ | B
  · rcases hq2 : grades.Q2 with _ | Q
    · by_cases hraw : grades.rawG2
      · have hval : M.currentSGVote st grades = M.get_fg_root st.toFG :=
          facts.gr.currentSGVote_of_rawG2 hdc hq2 hraw
        rw [hval]
        exact Or.inr (Or.inr (Or.inl ⟨rfl, hraw, rfl⟩))
      · have hval : M.currentSGVote st grades = grades.anchor :=
          facts.gr.currentSGVote_of_not_rawG2 hdc hq2 hraw
        rw [hval]
        exact Or.inr (Or.inr (Or.inr ⟨rfl, hraw, rfl⟩))
    · have hval : M.currentSGVote st grades = Q :=
        facts.gr.currentSGVote_of_Q2 hdc hq2
      rw [hval]
      exact Or.inr (Or.inl ⟨Q, rfl, rfl⟩)
  · have hval : M.currentSGVote st grades = B :=
      facts.gr.ModelProperties_currentSGVote_of_deepest_clear hdc
    rw [hval]
    have hlive : Block.Preceq B st.live_confirmed :=
      facts.gr.deepest_clear_Preceq hdc
    rw [hlc] at hlive
    exact Or.inl ⟨facts.gr.deepest_clear_floor_Preceq hdc, hlive,
      facts.gr.deepest_clear_test hdc⟩

end

end DecoupledConsensusModel.Sts.Restated
