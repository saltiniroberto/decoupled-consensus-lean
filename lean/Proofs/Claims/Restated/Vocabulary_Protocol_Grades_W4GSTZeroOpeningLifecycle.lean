import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Record.Wiring

/-!
# The SG block, the confirmation anchor and the FG root at a round's action

When a round action's SG block equals its `live_confirmed` block, the confirmation anchor at a
round's opening slot equals the action read's anchor, and the FG root is an ancestor of every
anchor, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

open scoped DC in
private theorem returns_map_elim {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

open scoped DC in
private theorem returns_map_intro {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution Statements
open Proofs.HealingSurface
open Internal.NamedRecoveryRead Internal.PhaseGrades DecoupledConsensusModel.Protocol

/-- If `A ⪯ Can ⪯ D`, then for every node state `n` of `v`'s action read at round `r` whose
    `live_confirmed` block is `D`, and every outcome `G` of `n`'s round-`r` grade read whose anchor
    is `A` and whose clearance test passes `D`, every SG block selected from `n` is `D`. -/
theorem Vocabulary.Proofs.w4_actionSGBlockAt_eq_liveConfirmed (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} {v : V} {r : Round}
    {Can D A : Block V}
    (hCanD : Block.Preceq Can D)
    (hACan : Block.Preceq A Can) :
    ∀ n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M S rho v r,
    n.st.core.live_confirmed = D →
    ∀ G, Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S n r ⇢ G →
    G.anchor = A → G.clear D = true →
    (let gc := M.gradeContract n.cache
     let st := M.toHealing n.st.core
     let k := M.round_of S.hc st.s
     ∀ A2, M.grade2_block_with gc S.E S.hc st k ⇢ A2 →
     ∀ X, M.get_sg_vote_with gc S.E S.hc st k A2 ⇢ X → X = D) := by
  intro ast hast hconfirmed' G hG hanchor' hclear'
  have hanchorLive : Block.Preceq G.anchor ast.st.core.live_confirmed := by
    rw [hanchor', hconfirmed']
    exact Proofs.ModelProperties.Preceq_trans hACan hCanD
  have hclearLive : G.clear ast.st.core.live_confirmed = true := by
    rw [hconfirmed']
    exact hclear'
  have hwalk : M.deepest_clear (some G.anchor)
      (M.toHealing ast.st.core).toFG.toSG.toGoldfishStore.live_confirmed
      G.clear = some ast.st.core.live_confirmed := by
    rw [facts.sto.toHealing_live_confirmed]
    exact facts.gr.deepest_clear_eq_tip
      (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hanchorLive) hclearLive
  have hround : (M.round_of S.hc (M.toHealing ast.st.core).toFG.toSG.toGoldfishStore.s) = r := by
    rw [facts.sto.toHealing_s]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_round facts S rho v r ast hast
  have hround' : M.round_of S.hc (M.toHealing ast.st.core).s = r := hround
  dsimp only
  rw [hround']
  intro A2 _ X hX
  exact (facts.dt.get_sg_vote_with_gradeContract_of_deepest_clear ast.cache S.E S.hc
    (M.toHealing ast.st.core) r A2 G hG hwalk X hX).trans hconfirmed'

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution Statements
open Proofs.HealingSurface
open Internal.NamedRecoveryRead Internal.PhaseGrades DecoupledConsensusModel.Protocol

/-- For every world `w` before round `k`'s action time and every node state `n` of `v`'s action read
    from `w`, the confirmation anchor computed with the grade contract of `n`'s cache, on the store
    the confirmation tick of round `k`'s opening slot makes of `v`'s store in `w`, can return `X`
    exactly when `n`'s round-`k` anchor can return `X`. -/
theorem Vocabulary.Proofs.w4_confAnchorWith_eq_nodeAnchor (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) (k : Round) :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
        (Restated.Vocabulary.Execution.Setup.a M S k),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) k,
    ∀ X, Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract n.cache) S.E S.hc
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (w v).st.core
          (M.confirmation_time S.E (M.opening_slot S.hc k))) ⇢ X ↔
      Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n k ⇢ X := by
  intro w hw n hn X
  have hsc : (Restated.Vocabulary.Execution.Setup.a M S k) =
      M.support_cutoff S.E ((M.opening_slot S.hc k) + 1) :=
    Restated.Vocabulary.Protocol.a_eq_support_cutoff_succ facts S.hc S.E k
  have hslot : S.E.slotOf ((Restated.Vocabulary.Execution.Setup.a M S k)) =
      (M.opening_slot S.hc k) + 1 := by
    rw [hsc]
    exact facts.sch.slotOf_support_cutoff S.E _
  have hidx : S.E.slotOf ((Restated.Vocabulary.Execution.Setup.a M S k)) - 1 =
      (M.opening_slot S.hc k) := by
    rw [hslot]; simp
  have hconf : (Restated.Vocabulary.Execution.Setup.a M S k) =
      M.confirmation_time S.E ((M.opening_slot S.hc k)) :=
    Restated.Vocabulary.Protocol.a_eq_confirmation_time facts S.hc S.E k
  obtain ⟨c, hc, st, hst, rfl⟩ := hn
  have htick : Restated.Vocabulary.Proofs.Optimistic.tickStore M S (w v).st.core
      (M.confirmation_time S.E (M.opening_slot S.hc k)) =
      (M.ns_setClock S.E (w v).st (Restated.Vocabulary.Execution.Setup.a M S k)).core := by
    rw [facts.hd.setClock_core_eq_store_with_t_s, hconf]
    rfl
  have hst' : M.duties_update_confirmation_with (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E (w v).st (Restated.Vocabulary.Execution.Setup.a M S k))
      (M.opening_slot S.hc k) ⇢ st := by
    rw [← hidx]
    exact hst
  obtain ⟨X0, hX0⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E (w v).st (Restated.Vocabulary.Execution.Setup.a M S k)).core
    (M.opening_slot S.hc k)
  have hcore : st.core = X0 :=
    facts.dt.named_update_confirmation_with_core _ _ _ _ _ st hst' X0 hX0
  have hround0 : M.round_of S.hc
      (M.ns_setClock S.E (w v).st (Restated.Vocabulary.Execution.Setup.a M S k)).core.s = k := by
    rw [facts.hd.ModelProperties_setClock_core_s]
    exact Restated.Vocabulary.Proofs.HealingLemmas.round_of_slotOf_a facts S k
  have htree := facts.dt.update_confirmation_with_toHealing_filtered _ _ _ _ _ X0 hX0
  have hroot := facts.dt.update_confirmation_with_toHealing_fg_root _ _ _ _ _ X0 hX0
  have hF := facts.hd.update_confirmation_with_toHealing_F _ _ _ _ _ X0 hX0
  have hframe := facts.gr.readFrame_g1_eq_of_F c (r := k) hF
  rw [facts.nd.mkNode_cache, htick]
  unfold Restated.Vocabulary.Protocol.confAnchorWith
  simp only [Record.Model.S.toHealing]
  rw [hround0, facts.nd.gradeContract_sgRoot_eq_frameAnchor,
    ← facts.gr.anchor_eq_of_filtered_fg_root S.E S.hc k _ htree hroot, ← hframe]
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead
  simp only [Record.Model.S.toHealing]
  rewrite [facts.nd.mkNode_cache, facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [hcore]
  have hrd : ∀ g, (M.gradeContract c).read S.E S.hc (M.toHealing (M.store_with_cache st c).core) k ⇢ g ↔
      (M.gradeContract c).read S.E S.hc (M.toHealing X0) k ⇢ g := by
    intro g
    rw [facts.nd.gradeContract_read, facts.nd.gradeContract_read,
      facts.nd.store_with_cache_frameGradeRead, hcore]
  constructor
  · intro hX
    obtain ⟨g, hg⟩ := facts.gr.read_nonempty (M.gradeContract c) S.E S.hc (M.toHealing X0) k
    have hga := facts.gr.frameGradeRead_anchor c S.E S.hc (M.toHealing X0) k g
      ((facts.nd.gradeContract_read c S.E S.hc (M.toHealing X0) k g).1 hg) X hX
    rw [← hga]
    exact returns_map_intro _ _ g ((hrd g).2 hg)
  · intro hX
    obtain ⟨g, hg, rfl⟩ := returns_map_elim _ _ _ hX
    have hg := (hrd g).1 hg
    obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing X0) k
      (M.readFrame c (M.toHealing X0) k).g1
    rw [facts.gr.frameGradeRead_anchor c S.E S.hc (M.toHealing X0) k g
      ((facts.nd.gradeContract_read c S.E S.hc (M.toHealing X0) k g).1 hg) a ha]
    exact ha

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution Statements
open Proofs.HealingSurface
open Internal.NamedRecoveryRead Internal.PhaseGrades DecoupledConsensusModel.Protocol

/-- Every anchor `a` that `M.anchor` can return at the store `st`, round `r` and grade-1 result `g1`
    is a descendant of, or is, `st`'s FG root. -/
theorem Vocabulary.Proofs.w4_fgRoot_preceq_anchor (facts : Record.Facts M)
    (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (r : Round)
    (g1 : Option (Option (Block V))) :
    ∀ a, M.anchor E hc st r g1 ⇢ a → Block.Preceq (M.get_fg_root st.toFG) a :=
  facts.gr.preceq_anchor_of_fgRoot E hc st r g1
    (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Statements.Instantiation
open Internal Execution Statements
open Proofs.HealingSurface
open Internal.NamedRecoveryRead Internal.PhaseGrades DecoupledConsensusModel.Protocol

/-- Every anchor `A` that `nodeAnchor` can give for the node state `n` at round `r` is a descendant
    of, or is, the FG root of `n`'s store. -/
theorem Vocabulary.Proofs.w4_fgRoot_preceq_nodeAnchor (facts : Record.Facts M)
    (S : Setup V) (n : M.N) (r : Round) :
    ∀ A, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n r ⇢ A →
      Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) A := by
  intro A hA
  obtain ⟨g, hg, rfl⟩ := returns_map_elim _ _ _ hA
  have hg' := (facts.nd.gradeContract_read n.cache S.E S.hc (M.toHealing n.st.core) r g).1 hg
  obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing n.st.core) r
    (M.readFrame n.cache (M.toHealing n.st.core) r).g1
  rw [facts.gr.frameGradeRead_anchor n.cache S.E S.hc (M.toHealing n.st.core) r g hg' a ha]
  exact Restated.Vocabulary.Proofs.w4_fgRoot_preceq_anchor facts S.E S.hc (M.toHealing n.st.core) r _ a ha

end

end DecoupledConsensusModel.Sts.Restated
