import Proofs.Vocabulary.Protocol.Schedule.Action
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The round and the attestation of a round action

The store of a round action's read is in that round, and the attestation it emits names the
validator, the round and the SG block's root, stated over a model `M : Record.Model V`.
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
open Protocol (HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

/-- Every store of `v`'s action read at round `r` has a slot in round `r`. -/
theorem Vocabulary.Proofs.HealingSurface.actionStoreAt_round (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) : ∀ w₁ ∈ Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M S rho v r,
    (M.round_of S.hc w₁.s) = r :=
  by
    intro w₁ hw
    obtain ⟨w, -, c, -, st, hst, rfl⟩ := hw
    show (M.round_of S.hc) (M.mkNode st (w v).record c).st.core.s = r
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [(facts.dt.named_confirmation_clock _ _ _ _ _ st hst).2,
      facts.hd.ModelProperties_setClock_core_s]
    exact Restated.Vocabulary.Proofs.HealingLemmas.round_of_slotOf_a facts S r

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

/-- For every read `n` of `v`'s action at round `r`, every outcome `D` of the attestation duty on
    `n`, every outcome `g2` of the grade-2 block of `n`'s store at its round, and every outcome `W`
    of the SG selector there on `g2`, the attestation of `D` names `v`, names round `r`, and
    confirms `W`'s root. -/
theorem Vocabulary.Proofs.HealingSurface.actionAttestationAt_shape (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M S rho v r,
      let gc := M.gradeContract n.cache
      let st := M.toHealing n.st.core
      let k := M.round_of S.hc st.s
      ∀ D, M.duties_attest_with gc S.E S.hc (S.node v) n.st n.record ⇢ D →
      ∀ g2, M.grade2_block_with gc S.E S.hc st k ⇢ g2 →
      ∀ W, M.get_sg_vote_with gc S.E S.hc st k g2 ⇢ W →
      D.2.2.val_index = v ∧ D.2.2.round = r ∧ D.2.2.confirmed = some W.root :=
  by
    intro n hn _ _ _ D hD g2 hg2 W hW
    obtain ⟨A, hA⟩ := facts.dt.round_action_with_nonempty (M.gradeContract n.cache) S.E S.hc
      (S.node v) (M.toHealing n.st.core) n.record
    have hrow := facts.dt.attest_with_row
      (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record D hD A hA
    refine ⟨?_, ?_, ?_⟩
    · rw [hrow, facts.dt.round_action_with_val_index _ _ _ _ _ _ A hA]
      exact S.node_val_index v
    · rw [hrow, facts.dt.round_action_with_round _ _ _ _ _ _ A hA,
        facts.sto.toHealing_s]
      exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_round facts S rho v r n hn
    · rw [hrow]
      exact facts.dt.round_action_with_confirmed _ _ _ _ _ _ A hA g2 hg2 W hW

end

end DecoupledConsensusModel.Sts.Restated
