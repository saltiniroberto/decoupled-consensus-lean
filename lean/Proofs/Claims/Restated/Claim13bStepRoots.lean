import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_ProposalParent
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepAnchor
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Roots of blocks in play

Blocks in play with the same root have the same erasure; the consequences for the bodies of honest
validators' stores; and the SG walk's output at an action read as a block of the store's tree and as
the erasure of a block in play. Stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If the execution put the named blocks `C` and `H` in play and they carry the same root, then
    their erasures are equal. -/
theorem erase_eq_of_root_eq_inLog (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {C H : NamedBlock V} (hC : Restated.blockInLog M S Sched x C) (hH : Restated.blockInLog M S Sched x H)
    (hroot : C.root = H.root) : C.erase = H.erase := by
  have hinj := Restated.rootInjectiveOnAncestors_of_collisionFreeInLog facts S Sched x hexec.idealization
    C H hC hH
  refine RootInjectiveOnAncestors.eq_of_root_eq hinj (A := C.erase) (C := H.erase)
    (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
    (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) ?_
  rw [Proofs.NamedWire.erase_root, Proofs.NamedWire.erase_root]
  exact hroot

end

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every choice `att` of the round-`(r + 1)` action attestations, if a body `C` of the store a
    validator honest through the tick at `S.a (r + 1)` holds after that tick has the root of a named
    block `H` in play, and `H` lies on one chain with the round-`(r + 1)` anchor read along `att`,
    then `C` does too. -/
theorem rootResolves_of_collisionFree (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) :
    ∀ (r : Round) (n' : Nat) (att : V → NamedAttestation V),
      Restated.ActionAttestationsOf M S Sched x r n' att →
      ∀ (T : NamedBlock V), Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      ∀ v ∈ honestThroughSet Sched ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))), ∀ (C H : NamedBlock V),
        C ∈ (x[n' + 1][v].st).st.bodies → Restated.blockInLog M S Sched x H → C.root = H.root →
        Block.compatible H.erase (Restated.newAnchor M S Sched x r n' att T).erase = true →
        Block.compatible C.erase (Restated.newAnchor M S Sched x r n' att T).erase = true := by
  intro r n' att hatt T hn' v hv C H hC hH hroot hcomp
  have htH : (x[n' + 1].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := le_of_eq (Restated.tickStepAt_time facts x hn').1
  have hvh : Restated.HonestThrough M Sched x (n' + 1) v :=
    fun t ht => (mem_honestThroughSet.1 hv) t (le_trans ht htH)
  rw [Restated.erase_eq_of_root_eq_inLog facts S Sched x hexec (Restated.blockInLog_of_mem_bodies facts S Sched hvh hC) hH
    hroot]
  exact hcomp

end

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Two bodies of the post-tick stores of two validators honest through the tick at `S.a (r + 1)`,
    whose roots are the roots of two named blocks in play that lie on one chain, themselves lie on
    one chain. -/
theorem rootResolvesPair_of_collisionFree (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) :
    ∀ (r : Round) (n' : Nat), Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      ∀ v₁ ∈ honestThroughSet Sched ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))),
      ∀ v₂ ∈ honestThroughSet Sched ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))),
      ∀ (C₁ C₂ H₁ H₂ : NamedBlock V),
        C₁ ∈ (x[n' + 1][v₁].st).st.bodies → Restated.blockInLog M S Sched x H₁ → C₁.root = H₁.root →
        C₂ ∈ (x[n' + 1][v₂].st).st.bodies → Restated.blockInLog M S Sched x H₂ → C₂.root = H₂.root →
        Block.compatible H₁.erase H₂.erase = true →
        Block.compatible C₁.erase C₂.erase = true := by
  intro r n' hn' v₁ hv₁ v₂ hv₂ C₁ C₂ H₁ H₂ hC₁ hH₁ hr₁ hC₂ hH₂ hr₂ hcomp
  have htH : (x[n' + 1].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := le_of_eq (Restated.tickStepAt_time facts x hn').1
  have hvh₁ : Restated.HonestThrough M Sched x (n' + 1) v₁ :=
    fun t ht => (mem_honestThroughSet.1 hv₁) t (le_trans ht htH)
  have hvh₂ : Restated.HonestThrough M Sched x (n' + 1) v₂ :=
    fun t ht => (mem_honestThroughSet.1 hv₂) t (le_trans ht htH)
  rw [Restated.erase_eq_of_root_eq_inLog facts S Sched x hexec (Restated.blockInLog_of_mem_bodies facts S Sched hvh₁ hC₁) hH₁
      hr₁,
    Restated.erase_eq_of_root_eq_inLog facts S Sched x hexec (Restated.blockInLog_of_mem_bodies facts S Sched hvh₂ hC₂) hH₂
      hr₂]
  exact hcomp

end

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every node state `n` of the round-`r₁` action read from `before` and every grade read `g` of
    the frame of `n`'s cache, the block the SG walk returns at `n`'s healing store under `g` is one
    of the blocks of `before`'s store, whenever `before`'s store satisfies the
    confirmation-membership invariant `hinv0`. -/
theorem actionSGVote_mem_tree (facts : Record.Facts M) (S : Setup V) (before : M.N) (r₁ : Round)
    (hinv0 : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg before.st)
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      before r₁)
    (g : Protocol.GradeRead V)
    (hg : M.frameGradeRead n.cache S.E S.hc (M.toHealing n.st.core) r₁ ⇢ g) :
    M.currentSGVote (M.toHealing n.st.core) g ∈ before.st.core.T := by
  obtain ⟨c, -, st, hst, rfl⟩ := hn
  rewrite [facts.nd.mkNode_st] at hg; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hg; rw [facts.nd.mkNode_cache] at hg
  rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
  have hinv : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg st :=
    facts.dt.invariant_update_gradeContract c S.E S.hc S.cfg _ _
      (facts.hd.invariant_clock S.E S.cfg _ _ hinv0) st hst
  have hroot : M.get_fg_root (M.toHealing st.core).toFG ∈ (M.toHealing st.core).T := by
    rw [Record.Model.HS.T, facts.sto.toHealing_T]
    exact Restated.Vocabulary.Proofs.NamedStoreRoots.fg_root_mem facts _ hinv.1.2
  have hanc : ∀ B, Block.Preceq B (M.toHealing st.core).live_confirmed →
      B ∈ (M.toHealing st.core).T := by
    intro B hB
    rw [Record.Model.HS.live_confirmed, facts.sto.toHealing_live_confirmed] at hB
    rw [Record.Model.HS.T, facts.sto.toHealing_T]
    have hcoh := hinv.1.1
    have hclosed : ∀ C ∈ st.core.T, C.parent? = none ∨ C.parent ∈ st.core.T := by
      intro C hC
      rw [hcoh.1] at hC ⊢
      obtain ⟨N, hN, rfl⟩ := Finset.mem_image.mp hC
      right
      rw [Proofs.NamedWire.erase_parent]
      exact Finset.mem_image_of_mem NamedBlock.erase (hcoh.2.2.1.2 N hN)
    exact Proofs.Records.mem_of_preceq hclosed _ _ hinv.2.1
      (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hB)
  have hT : (M.toHealing st.core).T = before.st.core.T := by
    rw [Record.Model.HS.T, facts.sto.toHealing_T, hinv.1.1.1, hinv0.1.1.1,
      facts.dt.named_update_confirmation_with_bodies _ _ _ _ _ st hst,
      facts.hd.ModelProperties_setClock_bodies]
  rw [← hT]
  cases hB : M.deepest_clear (some g.anchor) (M.toHealing st.core).live_confirmed g.clear with
  | some B =>
    rw [facts.gr.ModelProperties_currentSGVote_of_deepest_clear hB]
    exact hanc B (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp
      (facts.gr.deepest_clear_preceq hB))
  | none =>
    cases hq : g.Q2 with
    | some q =>
      rw [facts.gr.currentSGVote_of_Q2 hB hq]
      obtain ⟨o, ho⟩ := facts.gr.grade2Block_nonempty (M.toHealing st.core)
        (M.readFrame c (M.toHealing st.core) r₁)
      have hgo : g.Q2 = o := facts.nd.ModelProperties_gradeContract_read_Q2 c S.E S.hc _ r₁ g
        ((facts.nd.gradeContract_read c S.E S.hc _ r₁ g).2 hg) o ho
      exact facts.fc.get_filtered_block_tree_subset _
        (facts.gr.mem_filtered_of_grade2Block o ho (hgo ▸ hq))
    | none =>
      by_cases hraw : g.rawG2
      · rw [facts.gr.currentSGVote_of_rawG2 hB hq hraw]
        exact hroot
      · rw [facts.gr.currentSGVote_of_not_rawG2 hB hq hraw]
        obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing st.core) r₁
          (M.readFrame c (M.toHealing st.core) r₁).g1
        rw [facts.gr.frameGradeRead_anchor c S.E S.hc _ r₁ g hg a ha]
        exact Restated.Vocabulary.Proofs.NamedProposalParent.frame_anchor_mem facts S.E S.hc _ r₁ _
          hroot a ha

end

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If the adversary has held `v` at no time up to step `n`, then for every node state `m` of `v`'s
    round-`r₁` action read from the store `v` holds after `n` steps and every grade read `g` of the
    frame of `m`'s cache, the block the SG walk returns at `m`'s healing store under `g` is the
    erasure of a named block the execution put in play. -/
theorem exists_inLog_erase_actionSGVote (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {n : Nat} {v : V} (hv : Restated.HonestThrough M Sched x n v)
    (r₁ : Round) (m : M.N)
    (hm : m ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      (x[n][v].st) r₁)
    (g : Protocol.GradeRead V)
    (hg : M.frameGradeRead m.cache S.E S.hc (M.toHealing m.st.core) r₁ ⇢ g) :
    ∃ D : NamedBlock V, Restated.blockInLog M S Sched x D ∧
      D.erase = M.currentSGVote (M.toHealing m.st.core) g := by
  have hmem := Restated.actionSGVote_mem_tree facts S (x[n][v].st) r₁
    (Restated.nodeInvariant_sts facts S Sched x n v).1 m hm g hg
  have hT : (x[n][v].st).st.core.T = (x[n][v].st).st.bodies.image NamedBlock.erase :=
    (Restated.nodeInvariant_sts facts S Sched x n v).1.1.1.1
  rw [hT, Finset.mem_image] at hmem
  obtain ⟨D, hD, hDe⟩ := hmem
  exact ⟨D, Restated.blockInLog_of_mem_bodies facts S Sched hv hD, hDe⟩

end

end DecoupledConsensusModel.Sts.Restated
