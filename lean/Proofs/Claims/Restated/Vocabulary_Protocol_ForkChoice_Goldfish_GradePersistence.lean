import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Filtered-tree membership at the action read

A block in the filtered block tree of a validator's store before round `r`'s action stays in the
filtered tree of its action read, stated over a model `M : Record.Model V`.
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
open Internal
open Execution
open Internal.HealingSurface
open Proofs.HealingLemmas

/-- For every world `w` before round `r`'s action time, if `P` is in the filtered block tree of the
    healing view of `v`'s store in `w`, then `P` is in the filtered tree of every action read of
    `v`'s node state in `w` for round `r`. -/
theorem Vocabulary.Proofs.HealingSurface.activeAtAction_of_retainedAtRead (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} {v : V} {r : Round} {P : Block V} :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
        (Restated.Vocabulary.Execution.Setup.a M S r),
      P ∈ M.get_filtered_block_tree (M.toHealing (w v).st.core).toFG →
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
      P ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n := by
  intro w _ hretained n hn
  obtain ⟨c, _, st, hst, rfl⟩ := hn
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E (w v).st (Restated.Vocabulary.Execution.Setup.a M S r)).core
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  simp only [Restated.Vocabulary.Internal.PhaseGrades.filteredTree]
  rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.dt.named_update_confirmation_with_core _ _ _ _ _ st hst X hX,
    facts.dt.update_confirmation_with_toHealing_filtered _ _ _ _ _ X hX,
    facts.hd.setClock_core_eq_store_with_t_s]
  exact (congrArg (P ∈ ·) (facts.fc.get_filtered_block_tree_toHealing_clock (w v).st.core
    (Restated.Vocabulary.Execution.Setup.a M S r)
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r)))).mpr hretained

end

end DecoupledConsensusModel.Sts.Restated
