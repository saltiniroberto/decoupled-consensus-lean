import Proofs.Vocabulary.Protocol.ChainState.NamedNjGap
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_ProposalParent
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ChainState_NjGap
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_FinalityPairCore
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# The `nj` flag at a recovery height, and the action head

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: a named block at
a recovery height whose finalized height is at most the recovery's has its `nj` flag set, and every
head the action read computes is in the block tree of the store just before the action time.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NjGap
open Protocol
open Internal
open Execution

/-- If `H` is a recovery height for `h_F0`, and the chain state derived from `B` has finalized
    height at most `h_F0` and height `H`, then its `nj` flag is `true`. -/
theorem Vocabulary.Proofs.NjGap.nj_of_cap_named (facts : Record.Facts M) (E : Env V) (cfg : HeightConfig)
    {B : NamedBlock V} {h_F0 H : Height}
    (hrec : RecoveryHeight cfg h_F0 H)
    (hcap : (M.derive_named E cfg B).h_F ≤ h_F0)
    (hh : (M.derive_named E cfg B).h = H) :
    (M.derive_named E cfg B).nj = true := by
  obtain ⟨hF', hle, heq⟩ := facts.csAdded.njEntry_derive_named E cfg B
  have hle' : hF' ≤ h_F0 := hle.trans hcap
  rw [heq, hh]
  exact facts.csAdded.nonjustifiable_of_le hle' (facts.csAdded.nonjustifiable_of hrec.1 hrec.2)

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol
open Internal
open Execution
open Protocol
open NamedActionReads

/-- For every world `w` that can hold just before round `r`'s action time, every node state `n` the
    action read from `v`'s node state in `w` can give, and every block `H` the action head computed
    on `n` can return, `H` is in the block tree of `v`'s store in `w`. -/
theorem Vocabulary.Proofs.HealingSurface.actionHeadWith_mem_storeBeforeTime (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (v : V) (r : Round) :
    ∀ w ∈ Restated.Vocabulary.Execution.Run.stateBeforeTime M S rho
        (Restated.Vocabulary.Execution.Setup.a M S r),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
    ∀ H, Restated.Vocabulary.Proofs.HealingSurface.actionHeadWith M (M.gradeContract n.cache)
        S.E S.hc (M.toHealing n.st.core) ⇢ H → H ∈ (w v).st.core.T := by
  intro w hw n hn H hH
  let t := Restated.Vocabulary.Execution.Setup.a M S r
  have hpre := (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho t v
    w hw).1
  obtain ⟨c, hc, st, hst, rfl⟩ := hn
  rewrite [facts.nd.mkNode_cache, facts.nd.mkNode_st] at hH; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hH
  have hinv : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg st :=
    facts.dt.invariant_update_gradeContract c S.E S.hc S.cfg _ _
      (facts.hd.invariant_clock S.E S.cfg _ t hpre) st hst
  have hroot : M.get_fg_root (M.toHealing st.core).toFG ∈ st.core.T :=
    Restated.Vocabulary.Proofs.NamedStoreRoots.fg_root_mem facts st hinv.1.2
  let hs := M.toHealing (M.store_with_cache st c).core
  let rd := M.round_of S.hc hs.s
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract c) S.E S.hc hs rd
  obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc hs rd (M.readFrame c hs rd).g1
  have hanchor : G.anchor ∈ hs.T := by
    rw [facts.nd.ModelProperties_gradeContract_read_anchor c S.E S.hc hs rd G hG a ha]
    exact Restated.Vocabulary.Proofs.NamedProposalParent.frame_anchor_mem facts S.E S.hc _ _ _
      (by unfold Record.Model.HS.T
          rw [facts.sto.toHealing_T, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_core_T]
          exact hroot) a ha
  obtain ⟨res, -, hres⟩ := hH
  have hhead : H ∈ hs.T :=
    Restated.Vocabulary.Proofs.NamedProposalParent.get_head_with_mem facts (M.gradeContract c)
      S.E S.hc hs _ _ _ G hG hanchor H hres
  unfold Record.Model.HS.T at hhead
  rw [facts.sto.toHealing_T, facts.nd.store_with_cache_core_T] at hhead
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E (w v).st t).core (S.E.slotOf t - 1)
  have hT : st.core.T = (w v).st.core.T := by
    rw [facts.dt.named_update_confirmation_with_core _ _ _ _ _ st hst X hX,
      facts.dt.update_confirmation_with_T _ _ _ _ _ X hX,
      facts.hd.ModelProperties_setClock_core_T]
  rw [← hT]
  exact hhead

end

end DecoupledConsensusModel.Sts.Restated
