import Proofs.Vocabulary.Protocol.Grades.FrameForward
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Model.Conditions.Vocabulary_Internal_Definitions_NamedJointOutage
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# The frame result at the action checkpoint

The confirmation read at round `r`'s action keeps the frame result of the node state before it,
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
open DecoupledConsensusModel.Proofs.FrameForward
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

/-- For every world `w` before round `r`'s action time, if the frame of `v`'s node state in `w` at
    round `r` has the result `root` at phase `p`, then for every outcome `c` of the phase tick at
    that time from that node state, the frame of the confirmation read built with `c` has the same
    result. -/
theorem Vocabulary.Proofs.FrameForward.frame_phase_checkpoint_eq (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (v : V) (r : Round) (p : Phase) (root : Option (Block V)) :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
        (Restated.Vocabulary.Execution.Setup.a M S r),
      M.phaseResult (M.readFrame (w v).cache (M.toHealing (w v).st.core) r) p = some root →
      ∀ c, M.onPhaseTick S.E S.hc (M.toHealing (w v).st.core)
          (Restated.Vocabulary.Execution.Setup.a M S r) (w v).cache ⇢ c →
      M.phaseResult (M.readFrame
        (M.mkNode (M.ns_setClock S.E (w v).st (Restated.Vocabulary.Execution.Setup.a M S r))
          (w v).record c).cache
        (M.toHealing
          (M.mkNode (M.ns_setClock S.E (w v).st (Restated.Vocabulary.Execution.Setup.a M S r))
            (w v).record c).st.core)
        r) p = some root := by
  intro w hw hbase c hc
  rewrite [facts.nd.mkNode_cache, facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
  exact facts.grRun.frame_phase_prepared_eq_of_outcomes S rho v r p
    (Restated.Vocabulary.Execution.Setup.a M S r)
    (Restated.Vocabulary.Proofs.HealingLemmas.round_of_slotOf_a facts S r) root w hw hbase c hc

end

end DecoupledConsensusModel.Sts.Restated
