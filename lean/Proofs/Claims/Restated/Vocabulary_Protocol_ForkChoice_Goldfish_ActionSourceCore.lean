import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ActionSourceCore
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Model.Conditions.Vocabulary_Internal_Definitions_NamedJointOutage
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# The action read's FG source and grade-2 candidate

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: at a round's
action read the confirmation write keeps the filtered block tree and the round frame, a block of the
filtered tree is processed, and once the round's grade-2 candidate exists the FG source exists and
descends from the candidate's ancestors, the candidate is in the filtered tree, and the SG carrier
is a processed block.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

open scoped DC in
/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

open scoped DC in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
    (m >>= k) ⇢ b ↔ ∃ a, m ⇢ a ∧ k a ⇢ b := by
  unfold Record.Returns
  simp only [ExceptT.run_bind, Set.bind_def]
  constructor
  · intro h
    obtain ⟨e, he, hb⟩ := Set.mem_iUnion₂.mp h
    cases e with
    | ok a => exact ⟨a, he, hb⟩
    | error err => simp at hb
  · rintro ⟨a, ha, hb⟩
    exact Set.mem_iUnion₂.mpr ⟨_, ha, hb⟩

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Proofs.HealingLemmas

/-- For every node state `n` that the action read from `before` can give and every outcome `X` of
    the confirmation write that built it, `n`'s store is some store `st` with some cache written
    into it, and `st`'s core store is `X`. -/
private theorem actionReadFrom_core (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r)
    (X : M.S)
    (hX : M.update_confirmation_with (M.gradeContract n.cache) S.E S.hc
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r)).core
      (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1) ⇢ X) :
    ∃ st : M.NS, ∃ c : M.Cache, n.st = M.store_with_cache st c ∧ st.core = X := by
  obtain ⟨c, hc, st, hst, rfl⟩ := hn
  rw [facts.nd.mkNode_cache] at hX
  exact ⟨st, c, facts.nd.mkNode_st _ _ _,
    facts.dt.named_update_confirmation_with_core _ _ _ _ _ st hst X hX⟩

/-- For every world `w` that can hold before round `r`'s action time and every node state `n` that
    `v`'s action read from `w` can give, the filtered block tree of `n`'s store is the filtered
    block tree of the store `v` holds in `w`. -/
theorem Vocabulary.Proofs.HealingSurface.actionStoreAt_filteredTree (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho (Restated.Vocabulary.Execution.Setup.a M S r),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
    M.get_filtered_block_tree (M.toHealing n.st.core).toFG =
      M.get_filtered_block_tree
        (M.toHealing (w v).st.core).toFG := by
  intro w hw n hn
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.ns_setClock S.E (w v).st (Restated.Vocabulary.Execution.Setup.a M S r)).core
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  obtain ⟨st, c, hnst, hcore⟩ := actionReadFrom_core facts S (w v) r n hn X hX
  rw [hnst, facts.nd.store_with_cache_get_filtered_block_tree, hcore,
    facts.dt.update_confirmation_with_toHealing_filtered _ _ _ _ _ X hX,
    facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_filtered_block_tree_toHealing_clock _ _ _

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Proofs.HealingLemmas

/-- For every world `w` that can hold before round `r`'s action time, every node state `n` that
    `v`'s action read from `w` can give and every phase `p`, the phase-`p` result of the round-`r`
    frame read from the cache and store of `n` is that of the round-`r` frame read from the cache
    and store of `v`'s confirmation read from `w` at that time with `n`'s cache. -/
theorem Vocabulary.Proofs.HealingSurface.actionRead_readFrame_eq_checkpoint (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (v : V)
    (r : Round) :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho (Restated.Vocabulary.Execution.Setup.a M S r),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
    ∀ p : DecoupledConsensusModel.Protocol.Phase,
    M.phaseResult (M.readFrame n.cache (M.toHealing n.st.core) r) p =
      M.phaseResult (M.readFrame (M.mkNode (M.ns_setClock S.E (w v).st (Restated.Vocabulary.Execution.Setup.a M S r))
          (w v).record n.cache).cache
        (M.toHealing (M.mkNode (M.ns_setClock S.E (w v).st (Restated.Vocabulary.Execution.Setup.a M S r))
          (w v).record n.cache).st.core) r) p := by
  intro w hw n hn p
  simp only [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.ns_setClock S.E (w v).st (Restated.Vocabulary.Execution.Setup.a M S r)).core
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  obtain ⟨st, c, hnst, hcore⟩ := actionReadFrom_core facts S (w v) r n hn X hX
  rw [hnst, facts.nd.store_with_cache_readFrame, hcore]
  exact facts.gr.readFrame_phase_eq_of_F _ r
    (facts.hd.update_confirmation_with_toHealing_F _ _ _ _ _ X hX) p

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Proofs.HealingLemmas

/-- A block of the filtered block tree of the healing store read from `st` is in the processed tree
    `st.T`. -/
theorem Vocabulary.Proofs.HealingSurface.mem_T_of_mem_filteredTree (facts : Record.Facts M) {st : M.S} {B : Block V}
    (h : B ∈ M.get_filtered_block_tree (M.toHealing st).toFG) : B ∈ st.T := by
  have hT := facts.fc.get_filtered_block_tree_subset _ h
  rwa [facts.sto.toHealing_T] at hT

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Proofs.HealingLemmas

/-- For every world `w` that can hold before round `r`'s action time and every node state `n` that
    `v`'s action read from `w` can give, if the round-`r` grade-2 candidate of `n` can be `Q`, `C`
    is an ancestor of `Q`, and the round-`r` FG source of `n` can be `X`, then `C` is an ancestor of
    `X`. -/
theorem Vocabulary.Proofs.HealingSurface.preceq_actionFGSource_of_actionQ2 (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (v : V)
    (r : Round) {C Q X : Block V} :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho (Restated.Vocabulary.Execution.Setup.a M S r),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
    Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q →
    Block.Preceq C Q →
    Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n r ⇢ some X →
    Block.Preceq C X := by
  intro w hw n hn hq hCQ hsource
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead at hq
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource at hsource
  obtain ⟨G, hG, hGQ⟩ := returns_map_elim _ _ _ hq
  obtain ⟨A2, hA2, hsource'⟩ := (returns_bind_iff _ _ _).1 hsource
  have hA2Q : A2 = some Q :=
    (facts.dt.grade2_block_with_eq_read_Q2 _ _ _ _ _ G hG A2 hA2).trans hGQ
  rw [hA2Q] at hsource'
  cases hwalk : M.deepest_clear (some Q)
      (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.live_confirmed G.clear with
  | none =>
      have h := facts.dt.fg_source_with_some_of_deepest_clear_none _ _ _ _ _ G hG hwalk _ hsource'
      rw [Option.some_inj.mp h]
      exact hCQ
  | some B =>
      have h := facts.dt.fg_source_with_some_of_deepest_clear _ _ _ _ _ G hG hwalk _ hsource'
      have hQB : Block.Preceq Q B := facts.gr.deepest_clear_floor_Preceq hwalk
      rw [Option.some_inj.mp h]
      exact Proofs.ModelProperties.Preceq_trans hCQ hQB

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Proofs.HealingLemmas

/-- For every world `w` that can hold before round `r`'s action time and every node state `n` that
    `v`'s action read from `w` can give, if the round-`r` grade-2 candidate of `n` can be `Q`, then
    every outcome of the round-`r` FG source of `n` is some block `X`. -/
theorem Vocabulary.Proofs.HealingSurface.exists_actionFGSource_of_actionQ2 (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (v : V)
    (r : Round) {Q : Block V} :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho (Restated.Vocabulary.Execution.Setup.a M S r),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
    Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q →
    ∀ o, Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n r ⇢ o →
    ∃ X : Block V, o = some X := by
  intro w hw n hn hq o ho
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead at hq
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource at ho
  obtain ⟨G, hG, hGQ⟩ := returns_map_elim _ _ _ hq
  obtain ⟨A2, hA2, ho'⟩ := (returns_bind_iff _ _ _).1 ho
  have hA2Q : A2 = some Q :=
    (facts.dt.grade2_block_with_eq_read_Q2 _ _ _ _ _ G hG A2 hA2).trans hGQ
  rw [hA2Q] at ho'
  cases hwalk : M.deepest_clear (some Q)
      (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.live_confirmed G.clear with
  | none =>
      exact ⟨Q, facts.dt.fg_source_with_some_of_deepest_clear_none _ _ _ _ _ G hG hwalk _ ho'⟩
  | some B =>
      exact ⟨B, facts.dt.fg_source_with_some_of_deepest_clear _ _ _ _ _ G hG hwalk _ ho'⟩

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Proofs.HealingLemmas

/-- For every world `w` that can hold before round `r`'s action time and every node state `n` that
    `v`'s action read from `w` can give, if the round-`r` grade-2 candidate of `n` can be `Q`, then
    `Q` is in the filtered block tree of `n`. -/
theorem Vocabulary.Proofs.HealingSurface.actionQ2_mem_filteredTree (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (v : V) (r : Round)
    {Q : Block V} :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho (Restated.Vocabulary.Execution.Setup.a M S r),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
    Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q →
    Q ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n := by
  intro w hw n hn hq
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead at hq
  obtain ⟨G, hG, hGQ⟩ := returns_map_elim _ _ _ hq
  obtain ⟨x, hx⟩ := facts.gr.grade2Block_nonempty (M.toHealing n.st.core)
    (M.readFrame n.cache (M.toHealing n.st.core) r)
  have hGx := facts.nd.ModelProperties_gradeContract_read_Q2 n.cache S.E S.hc _ r G hG x hx
  exact facts.gr.mem_filtered_of_grade2Block x hx (hGx.symm.trans hGQ)

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Proofs.HealingLemmas

/-- For every world `w` that can hold before round `r`'s action time and every node state `n` that
    `v`'s action read from `w` can give, if the round-`r` grade-2 candidate of `n` can be `Q`, then
    every block the SG selector can pick from `n`, under the grade contract of `n`'s cache at the
    round of `n`'s slot and with any outcome of the grade-2 block read there, is in the processed
    tree of `n`'s core store. -/
theorem Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_actionStore_of_actionQ2 (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (v : V) (r : Round) {Q : Block V} :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho (Restated.Vocabulary.Execution.Setup.a M S r),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
    Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q →
    (let gc := M.gradeContract n.cache
     let st := M.toHealing n.st.core
     let k := M.round_of S.hc st.s
     ∀ A2, M.grade2_block_with gc S.E S.hc st k ⇢ A2 →
     ∀ W, M.get_sg_vote_with gc S.E S.hc st k A2 ⇢ W → W ∈ n.st.core.T) := by
  intro w hw n hn hq gc st k A2 hA2 W hW
  have hq0 := hq
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead at hq0
  obtain ⟨G, hG, hQ2⟩ := returns_map_elim _ _ _ hq0
  obtain ⟨c, hc, ns, hns, hneq⟩ := id hn
  have hnst : n.st = M.store_with_cache ns c := by rw [hneq, facts.nd.mkNode_st]
  have hncache : n.cache = c := by rw [hneq, facts.nd.mkNode_cache]
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.ns_setClock S.E (w v).st (Restated.Vocabulary.Execution.Setup.a M S r)).core
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  obtain ⟨ns', c', hnst', hcore'⟩ := actionReadFrom_core facts S (w v) r n hn X hX
  have hcoreS : n.st.core.s = X.s := by rw [hnst', facts.nd.store_with_cache_core_s, hcore']
  have hcoreT : n.st.core.T = X.T := by rw [hnst', facts.nd.store_with_cache_core_T, hcore']
  have hk : k = r := by
    have hs : (M.toHealing n.st.core).s = n.st.core.s := facts.sto.toHealing_s _
    show M.round_of S.hc (M.toHealing n.st.core).s = r
    rw [hs, hcoreS, facts.dt.update_confirmation_with_s _ _ _ _ _ X hX,
      facts.hd.ModelProperties_setClock_core_s]
    exact Restated.Vocabulary.Proofs.HealingLemmas.round_of_slotOf_a facts S r
  have hA2' : M.grade2_block_with (M.gradeContract n.cache) S.E S.hc st r ⇢ A2 := by
    rw [← hk]; exact hA2
  have hW' : M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc st r A2 ⇢ W := by
    rw [← hk]; exact hW
  have heq : W = M.currentSGVote st G :=
    facts.dt.get_sg_vote_with_gradeContract_grade2 n.cache S.E S.hc st r A2 hA2' G hG W hW'
  have hT : n.st.core.T = (w v).st.core.T := by
    rw [hcoreT, facts.dt.update_confirmation_with_T _ _ _ _ _ X hX,
      facts.hd.ModelProperties_setClock_core_T]
  have hcl : ∀ B ∈ n.st.core.T, B.parent? = none ∨ B.parent ∈ n.st.core.T := by
    have h := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho
      (Restated.Vocabulary.Execution.Setup.a M S r) v w hw
    unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at h
    rw [facts.sto.toHealing_T] at h
    rw [hT]
    exact h.2
  have hlc : (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.live_confirmed ∈ n.st.core.T := by
    have h0 : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg (w v).st :=
      (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho
        (Restated.Vocabulary.Execution.Setup.a M S r) v w hw).1
    have h1 := facts.hd.invariant_clock S.E S.cfg _ (Restated.Vocabulary.Execution.Setup.a M S r) h0
    have h2 : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg ns :=
      facts.dt.invariant_update_gradeContract c S.E S.hc S.cfg _ _ h1 ns hns
    rw [facts.sto.toHealing_live_confirmed, hnst, facts.nd.store_with_cache_core_live_confirmed,
      facts.nd.store_with_cache_core_T]
    exact h2.2.1
  rw [heq]
  cases hdc : M.deepest_clear (some G.anchor) st.toFG.toSG.toGoldfishStore.live_confirmed
      G.clear with
  | none =>
      rw [facts.gr.currentSGVote_of_Q2 hdc hQ2]
      exact Restated.Vocabulary.Proofs.HealingSurface.mem_T_of_mem_filteredTree facts
        (Restated.Vocabulary.Proofs.HealingSurface.actionQ2_mem_filteredTree facts S rho v r w hw n hn
          hq)
  | some B =>
      rw [facts.gr.ModelProperties_currentSGVote_of_deepest_clear hdc]
      exact Proofs.Records.mem_of_preceq hcl B
        st.toFG.toSG.toGoldfishStore.live_confirmed hlc (facts.gr.deepest_clear_preceq hdc)

end

end DecoupledConsensusModel.Sts.Restated
