import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bStepSG

/-!
# The confirmed block of a round attestation

The block a round attestation says it confirms is the SG walk's output at the round's action read,
stated over a model `M : Record.Model V`.
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

/-- For every node state `n` of the round-`r₁` action read from `before`, every outcome `D` of `q`'s
    attestation duty on `n` and every grade read `g` of the frame of `n`'s cache, the block `D`'s
    attestation says it confirms is the root of the SG walk's output at `n`'s healing store under
    `g`. -/
theorem attest_confirmed_eq_sgVote (facts : Record.Facts M) (S : Setup V) (before : M.N) (q : V)
    (r₁ : Round) (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      before r₁)
    (D : M.NS × M.NR × NamedAttestation V)
    (hD : M.duties_attest_with (M.gradeContract n.cache) (Setup.alwaysAwake S).E
      (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node q) n.st n.record ⇢ D)
    (g : Protocol.GradeRead V)
    (hg : M.frameGradeRead n.cache S.E S.hc (M.toHealing n.st.core) r₁ ⇢ g) :
    D.2.2.confirmed = some (M.currentSGVote (M.toHealing n.st.core) g).root := by
  obtain ⟨c, hc, st, hst, rfl⟩ := hn
  rewrite [facts.nd.mkNode_st] at hD hg; rewrite [facts.nd.store_with_cache_frameGradeRead] at hg
  rw [facts.nd.mkNode_cache] at hD hg
  rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
  have hs : (M.toHealing st.core).toFG.toSG.toGoldfishStore.s =
      S.E.slotOf ((Restated.Vocabulary.Execution.Setup.a M S r₁)) := by
    rw [facts.sto.toHealing_gs_s, (facts.dt.named_confirmation_clock _ _ _ _ _ st hst).2,
      facts.hd.Sts_setClock_core_s]
    rfl
  have hR : M.round_of S.hc (M.toHealing st.core).toFG.toSG.toGoldfishStore.s = r₁ := by
    rw [hs]
    exact Restated.Vocabulary.Proofs.HealingLemmas.round_of_slotOf_a facts S r₁
  have hG : (M.gradeContract c).read S.E S.hc (M.toHealing st.core)
      (M.round_of S.hc (M.toHealing st.core).toFG.toSG.toGoldfishStore.s) ⇢ g := by
    rw [hR]
    exact (facts.nd.gradeContract_read c S.E S.hc _ r₁ g).2 hg
  have hG' : (M.gradeContract c).read S.E S.hc (M.toHealing (M.store_with_cache st c).core)
      (M.round_of S.hc (M.toHealing (M.store_with_cache st c).core).toFG.toSG.toGoldfishStore.s) ⇢ g := by
    rw [facts.sto.toHealing_gs_s, facts.nd.store_with_cache_core_s, ← facts.sto.toHealing_gs_s st.core, hR]
    exact (facts.nd.gradeContract_read c S.E S.hc _ r₁ g).2
      (by rw [facts.nd.store_with_cache_frameGradeRead]; exact hg)
  rw [facts.dt.namedDuties_attest_with_confirmed _ _ _ _ _ _ D hD g hG',
    facts.nd.gradeContract_sgVote, facts.nd.store_with_cache_currentSGVote]

end

end DecoupledConsensusModel.Sts.Restated
