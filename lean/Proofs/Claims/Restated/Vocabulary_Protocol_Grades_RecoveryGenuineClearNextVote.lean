import Proofs.Vocabulary.Protocol.Grades.RecoveryGenuineClearNextVote
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_RecoveryActionLiveSourceSplit
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ActionSourceCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RecoveryCapturedActionCarrier
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Record.Wiring

/-!
# The FG source of a round action

The FG source a round action reads is either the grade-2 candidate or a block on the clear walk to a
confirmed block, stated over a model `M : Record.Model V`.
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
private theorem returns_bind_elim {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β)
    (h : (m >>= k) ⇢ b) : ∃ a, m ⇢ a ∧ k a ⇢ b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_bind, Set.bind_def] at h
  obtain ⟨e, he, hb⟩ := Set.mem_iUnion₂.mp h
  cases e with
  | ok a => exact ⟨a, he, hb⟩
  | error err => simp at hb

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Protocol
open Protocol
open scoped DC

/-- For every world `w` before round `r`'s action time and every node state `n` of `v`'s action read
    from `w`, if the grade-2 candidate of `n` can be `Q` and its FG source can be `B`, then either
    `B = Q`, or some block `C` satisfies `GenuineConfirmationWith` with the grade contract of `n`'s
    cache on the tick store of `v` in `w` at the opening slot's confirmation time, `C` is `n`'s
    `live_confirmed`, for every outcome `G` of the grade read the deepest clear walk from `Q`
    returns `B`, and `Q ⪯ B ⪯ C`. -/
theorem Vocabulary.Proofs.HealingSurface.actionFGSource_genuineClear_or_selectedG2_named (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) (r : Round)
    {Q B : Block V} :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho (Restated.Vocabulary.Execution.Setup.a M S r),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
    Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q →
    Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some B →
    (∃ C : Block V,
      Restated.Vocabulary.Protocol.GenuineConfirmationWith M
        (M.gradeContract n.cache)
        S.E S.hc
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (w v).st.core
          (M.confirmation_time S.E (M.opening_slot S.hc r)))
          ((M.opening_slot S.hc r)) C ∧
      C = n.st.core.live_confirmed ∧
      (∀ G : GradeRead V,
        (M.gradeContract n.cache).read S.E S.hc (M.toHealing n.st.core) r ⇢ G →
        M.deepest_clear (some Q) n.st.core.live_confirmed G.clear = some B) ∧
      Block.Preceq Q B ∧ Block.Preceq B C) ∨
    B = Q := by
  intro w hw n hn hQ hB
  have hast : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M S rho v r := ⟨w, hw, hn⟩
  let gc := M.gradeContract n.cache
  let st := (M.toHealing n.st.core)
  have hround : (M.round_of S.hc st.s) = r := by
    show (M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s) = r
    rw [facts.sto.toHealing_s]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_round facts S rho v r n hast
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead at hQ
  obtain ⟨G0, hG0, hG0Q⟩ := returns_map_elim _ _ _ hQ
  have hB1 : (M.grade2_block_with gc S.E S.hc st r >>= fun g =>
      M.fg_source_with gc S.E S.hc st r g) ⇢ some B := by
    have h := hB
    change (M.grade2_block_with gc S.E S.hc st (M.round_of S.hc st.s) >>= fun g =>
      M.fg_source_with gc S.E S.hc st (M.round_of S.hc st.s) g) ⇢ some B at h
    rw [hround] at h
    exact h
  obtain ⟨g, hg, hsource⟩ := returns_bind_elim _ _ _ hB1
  have hgQ : g = some Q :=
    (facts.dt.grade2_block_with_eq_read_Q2 gc S.E S.hc st r G0 hG0 g hg).trans hG0Q
  rw [hgQ] at hsource
  have hwalkB : ∀ G : GradeRead V, gc.read S.E S.hc st r ⇢ G →
      M.deepest_clear (some Q) st.toFG.toSG.toGoldfishStore.live_confirmed G.clear = none ∧
        B = Q ∨
      M.deepest_clear (some Q) st.toFG.toSG.toGoldfishStore.live_confirmed G.clear = some B := by
    intro G hG
    cases hwalk : M.deepest_clear (some Q) st.toFG.toSG.toGoldfishStore.live_confirmed G.clear with
    | none =>
        exact Or.inl ⟨rfl, Option.some_inj.mp
          (facts.dt.fg_source_with_some_of_deepest_clear_none gc S.E S.hc st r G hG hwalk _ hsource)⟩
    | some W =>
        exact Or.inr (by
          rw [← Option.some_inj.mp
            (facts.dt.fg_source_with_some_of_deepest_clear gc S.E S.hc st r G hG hwalk _ hsource)])
  have hlive : st.toFG.toSG.toGoldfishStore.live_confirmed = n.st.core.live_confirmed :=
    facts.sto.toHealing_live_confirmed _
  rcases hwalkB G0 hG0 with ⟨-, hBQ⟩ | hwalk0
  · exact Or.inr hBQ
  have hQB : Block.Preceq Q B := facts.gr.deepest_clear_floor_Preceq hwalk0
  have hBlive : Block.Preceq B n.st.core.live_confirmed := by
    have h := facts.gr.deepest_clear_Preceq hwalk0
    rw [hlive] at h
    exact h
  have hall : ∀ G : GradeRead V,
      (M.gradeContract n.cache).read S.E S.hc (M.toHealing n.st.core) r ⇢ G →
      M.deepest_clear (some Q) n.st.core.live_confirmed G.clear = some B ∨ B = Q := by
    intro G hG
    rcases hwalkB G hG with ⟨-, hBQ⟩ | hwalk
    · exact Or.inr hBQ
    · rw [← hlive]; exact Or.inl hwalk
  by_cases hBQ : B = Q
  · exact Or.inr hBQ
  have hall' : ∀ G : GradeRead V,
      (M.gradeContract n.cache).read S.E S.hc (M.toHealing n.st.core) r ⇢ G →
      M.deepest_clear (some Q) n.st.core.live_confirmed G.clear = some B :=
    fun G hG => (hall G hG).resolve_right hBQ
  rcases Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_liveConfirmed_genuine_or_fgRoot
      facts S rho v r w hw n hn with ⟨C, hC, hClive⟩ | ⟨R, hRroot, hRlive⟩
  · left
    exact ⟨C, hC, hClive, hall', hQB, hClive ▸ hBlive⟩
  ·
    exfalso
    apply hBQ
    obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract n.cache) S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (w v).st.core
        (M.confirmation_time S.E (M.opening_slot S.hc r))) (M.opening_slot S.hc r)
    have hRn : R = M.get_fg_root (M.toHealing n.st.core).toFG := by
      obtain ⟨s0, hs0, hs0X⟩ :=
        Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_eq_update_confirmation_confStore
          facts S rho v r w hw n hn X hX
      rw [hRroot, hs0, facts.nd.store_with_cache_get_fg_root, hs0X,
        facts.dt.update_confirmation_with_toHealing_fg_root _ _ _ _ _ X hX]
    have hQfiltered : Q ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n :=
      Restated.Vocabulary.Proofs.HealingSurface.actionQ2_mem_filteredTree facts S rho v r w hw n hn
        (by
          unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2
            Restated.Vocabulary.Internal.PhaseGrades.nodeRead
          exact hQ)
    have hRQ : Block.Preceq R Q := by
      rw [hRn]
      exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp
        (facts.fc.preceq_get_fg_root_of_mem_filtered hQfiltered)
    have hBR : Block.Preceq B R := by rw [hRlive]; exact hBlive
    exact Proofs.ModelProperties.Preceq_antisymm (Proofs.ModelProperties.Preceq_trans hBR hRQ) hQB

end

end DecoupledConsensusModel.Sts.Restated
