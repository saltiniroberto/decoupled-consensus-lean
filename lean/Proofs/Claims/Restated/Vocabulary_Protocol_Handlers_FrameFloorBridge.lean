import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Record.Wiring

/-!
# The anchor descends from a filtered block

The anchor a node state gives descends from a block of its filtered tree under a condition on its
frame, stated over a model `M : Record.Model V`.
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

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.NamedOutageEntry
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol

/-- If `P` is in the filtered tree of `n`'s store, and either the round-`r` frame read from `n`'s
    cache has a completed grade-1 root that is a descendant of `P` or `P` is an ancestor of the
    store's FG root, then every anchor `A0` that `n` can give at round `r` is a descendant of `P`. -/
theorem Vocabulary.Proofs.HealingSurface.anchor_preceq_of_frame_floor (facts : Record.Facts M)
    (S : Setup V) (n : M.N) (r : Round) (P : Block V)
    (hPtree : P ∈ M.get_filtered_block_tree (M.toHealing n.st.core).toFG)
    (hcase :
    (∃ root, (M.readFrame n.cache (M.toHealing n.st.core) r).g1 =
        some (some root) ∧ Block.Preceq P root) ∨
      Block.Preceq P (M.get_fg_root (M.toHealing n.st.core).toFG)) :
    ∀ A0, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n r ⇢ A0 → Block.Preceq P A0 := by
  intro A0 hA0
  obtain ⟨g, hg, rfl⟩ := returns_map_elim _ _ _ hA0
  obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing n.st.core) r
    (M.readFrame n.cache (M.toHealing n.st.core) r).g1
  rw [facts.nd.ModelProperties_gradeContract_read_anchor n.cache S.E S.hc (M.toHealing n.st.core) r
    g hg a ha]
  rcases hcase with hroot | hfg
  · obtain ⟨root, hframe, hPR⟩ := hroot
    rw [hframe] at ha
    exact facts.gr.preceq_anchor_of_g1 S.E S.hc _ r hPtree hPR a ha
  · rcases facts.gr.anchor_cases S.E S.hc (M.toHealing n.st.core) r
        (M.readFrame n.cache (M.toHealing n.st.core) r).g1 a ha with h | ⟨root, A, -, hA, h⟩
    · rw [h]
      exact hfg
    · rw [h]
      exact Proofs.ModelProperties.Preceq_trans hfg (by
        unfold Block.Preceq
        exact facts.fc.preceq_get_fg_root_of_mem_filtered (facts.gr.activePrefix_mem _ root A hA))

end

end DecoupledConsensusModel.Sts.Restated
