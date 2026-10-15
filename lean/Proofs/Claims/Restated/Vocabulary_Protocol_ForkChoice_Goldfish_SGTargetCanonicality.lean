import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicality
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_FGForkChoice_Finality
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Filtered-tree membership and the cases of the SG selector

A descendant of the FG root is in the filtered block tree under a one-step height bound, and the SG
block of a round action is either a clear block or the grade-2 candidate, stated over a model
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
open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas

/-- For every world `world` before `read`, write `st` for the store `w` holds in it; if the named
    block `Bn` is among `st`'s bodies, its erasure is `B`, the FG root of `st` is `J`, `J` is an
    ancestor of `B`, and `st`'s `h_max` is at most one more than the height of `Bn`'s derived chain
    state, then `B` is in the filtered block tree of `st`. -/
theorem Vocabulary.Proofs.HealingSurface.mem_filtered_of_mem_tree_of_exactFGRoot_heightCap (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (w : V) (read : Time)
    {J B : Block V} {Bn : NamedBlock V} :
    ∀ world ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho read,
    Bn ∈ (world w).st.bodies →
    Bn.erase = B →
    M.get_fg_root (M.toHealing (world w).st.core).toFG = J →
    Block.Preceq J B →
    (world w).st.core.h_max ≤ (M.derive_named S.E S.cfg Bn).h + 1 →
    B ∈ M.get_filtered_block_tree (M.toHealing (world w).st.core).toFG := by
  intro world hworld hBn hB hroot hJB hcap
  have hinv := Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho read w
    world hworld
  have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg (world w).st := hinv.1.1.1
  have hBmem : B ∈ (world w).st.core.T := by
    rw [hcoh.1, ← hB]
    exact Finset.mem_image_of_mem NamedBlock.erase hBn
  have hFJ : Block.Preceq (world w).st.core.F (world w).st.core.J :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts S rho
      read w world hworld
  have hFroot : Block.Preceq (world w).st.core.F
      (M.get_fg_root (M.toHealing (world w).st.core).toFG) := by
    have h := facts.fc.preceq_get_fg_root_of_F (st := (M.toHealing (world w).st.core).toFG)
      (by
        rw [facts.sto.ModelProperties_toHealing_F, facts.sto.ModelProperties_toHealing_J]
        exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hFJ)
    rw [facts.sto.ModelProperties_toHealing_F] at h
    exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp h
  have hrootB : Block.Preceq
      (M.get_fg_root (M.toHealing (world w).st.core).toFG) B := by
    rw [hroot]
    exact hJB
  have hFB : Block.Preceq (world w).st.core.F B := Proofs.ModelProperties.Preceq_trans hFroot hrootB
  have hσ : (world w).st.core.σ B = M.derive_named S.E S.cfg Bn := by
    rw [← hB]
    exact Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts S rho read w
      world hworld Bn hBn
  have hheight : (world w).st.core.h_max - 1 ≤ ((world w).st.core.σ B).h := by
    rw [hσ]
    exact Nat.sub_le_iff_le_add.mpr hcap
  have hBT : B ∈ (M.toHealing (world w).st.core).toFG.toSG.toGoldfishStore.T := by
    rw [facts.sto.toHealing_T]
    exact hBmem
  exact facts.fc.mem_get_filtered_block_tree_of_parts _ hBT
    (by rw [facts.sto.ModelProperties_toHealing_F]; exact hFB) hBT
    (Proofs.ModelProperties.Preceq_self B)
    (by rw [facts.sto.ModelProperties_toHealing_h_max, facts.sto.ModelProperties_toHealing_σ]
        exact hheight)
    hrootB

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas

/-- For every world `world` before round `r`'s action time, every node state `n` of `u`'s action
    read from `world`, every outcome `g` of `n`'s grade read at round `r` whose grade-2 candidate is
    `Q`, and every block `sg` the SG selector can pick from `n`, `sg` is either a block that the
    clear walk from `g`'s anchor along `n`'s live confirmed chain returns, or `Q`. -/
theorem Vocabulary.Proofs.HealingSurface.actionSGBlockAt_clear_or_selectedG2 (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) {r : Round} {u : V} {Q : Block V} :
    ∀ world ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho (Restated.Vocabulary.Execution.Setup.a M S r),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (world u) r,
    ∀ g : Protocol.GradeRead V, Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S n r ⇢ g →
    g.Q2 = some Q →
    ∀ A2 : Option (Block V),
      M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ A2 →
    ∀ sg : Block V,
      M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) A2 ⇢ sg →
    (∃ T : Block V,
      M.deepest_clear (some g.anchor) (M.toHealing n.st.core).live_confirmed g.clear = some T ∧
      sg = T) ∨
    sg = Q := by
  intro world hworld n hn g hg hQ A2 hA2 sg hsg
  have hk : M.round_of S.hc (M.toHealing n.st.core).s = r := by
    have hs' : (M.toHealing n.st.core).s = n.st.core.s := facts.sto.toHealing_s _
    rw [hs']
    obtain ⟨c, hc, D, hD, rfl⟩ := hn
    obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E (world u).st (Restated.Vocabulary.Execution.Setup.a M S r)).core
      (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.dt.named_update_confirmation_with_core _ _ _ _ _ D hD X hX,
      facts.dt.update_confirmation_with_s _ _ _ _ _ X hX, facts.hd.Sts_setClock_core_s]
    exact Restated.Vocabulary.Proofs.HealingLemmas.round_of_slotOf_a facts S r
  rw [hk] at hA2 hsg
  have heq : sg = M.currentSGVote (M.toHealing n.st.core) g :=
    facts.dt.get_sg_vote_with_gradeContract_grade2 n.cache S.E S.hc _ r A2 hA2 g hg sg hsg
  cases hclear : M.deepest_clear (some g.anchor)
      (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.live_confirmed g.clear with
  | some T =>
      left
      exact ⟨T, hclear, heq.trans (facts.gr.ModelProperties_currentSGVote_of_deepest_clear hclear)⟩
  | none =>
      right
      exact heq.trans (facts.gr.currentSGVote_of_Q2 hclear hQ)

end

end DecoupledConsensusModel.Sts.Restated
