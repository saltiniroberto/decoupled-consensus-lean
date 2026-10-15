import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# Round `q` in the SG admission window of a proposer

A theorem over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: the proposer of
the second slot after round `q`'s opening slot has round `q` in the SG admission window of its store
at its proposal time.
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

/-- For every node state `w₁` that the proposer of slot `opening_slot q + 2` can hold at that slot's
    proposal time, round `q` is in the SG admission window of `w₁`'s core store. -/
theorem Vocabulary.Proofs.HealingSurface.inWindow_round_at_plusTwo (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (q : Round) : ∀ w₁ ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho ((M.opening_slot S.hc q) + 2),
    M.inWindow S.hc
      w₁.st.core q = true := by
  intro w₁ hw₁
  have hlo : q ≤ M.round_of S.hc (M.opening_slot S.hc q + 2) :=
    calc q = M.round_of S.hc (M.opening_slot S.hc q) := (facts.gr.round_of_opening_slot_eq S.hc q).symm
      _ ≤ _ := facts.gr.round_of_mono S.hc (Nat.le_add_right _ 2)
  have hhi : M.round_of S.hc (M.opening_slot S.hc q + 2) ≤ q + 1 :=
    calc M.round_of S.hc (M.opening_slot S.hc q + 2)
        ≤ M.round_of S.hc (M.opening_slot S.hc (q + 1)) := by
          apply facts.gr.round_of_mono S.hc
          rw [facts.gr.opening_slot_succ]
          exact Nat.add_le_add_left S.hc.R_ge_two _
      _ = q + 1 := facts.gr.round_of_opening_slot_eq S.hc (q + 1)
  have hslot : w₁.st.core.s = M.opening_slot S.hc q + 2 := by
    simp only [Restated.Vocabulary.Statements.Instantiation.proposerReadAt,
      Restated.Vocabulary.Execution.NamedActionReads.confirmationReadAt] at hw₁
    obtain ⟨w, -, c, -, rfl⟩ := hw₁
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_s]
    exact facts.sch.slotOf_proposal_time S.E _
  have hone : 1 ≤ S.hc.η_SG := S.hc.η_SG_ge_one
  rw [facts.dt.inWindow_eq_true_iff, hslot]
  have key : ∀ {x e q : Nat}, x ≤ q + 1 → 1 ≤ e → x - e ≤ q := by intro x e q h1 h2; omega
  exact ⟨key hhi hone, hlo⟩

end

end DecoupledConsensusModel.Sts.Restated
