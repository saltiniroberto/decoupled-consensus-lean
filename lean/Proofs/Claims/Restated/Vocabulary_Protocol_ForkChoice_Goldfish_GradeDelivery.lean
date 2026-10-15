import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.GradeDelivery
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Record.Wiring

/-!
# The anchor of a grade read

The anchor that a node state's grade read gives on its active-prefix branch, stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

private theorem returns_map_elim_gd {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
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
open DecoupledConsensusModel.Proofs.HealingSurface.GradeDeliveryRun
open Internal
open Execution
open Internal.PhaseGrades
open Internal.HealingSurface

/-- If the grade-1 result of `n`'s round-`r` frame is the root `root`, and the active prefix of
    `root` in `n`'s filtered block tree is `A`, then every anchor `n` can give at round `r` is `A`. -/
theorem Vocabulary.Proofs.HealingSurface.GradeDeliveryRun.nodeAnchor_eq_of_activePrefix_some (facts : Record.Facts M)
    (S : Setup V) (n : M.N) {r : Round} {root A : Block V}
    (hframe : M.phaseResult
      (M.readFrame n.cache (M.toHealing n.st.core) r) .g1 =
        some (some root))
    (hactive : M.activePrefix
      (Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n) root = some A) :
    ∀ X, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n r ⇢ X → X = A := by
  intro X hX
  obtain ⟨g, hg, rfl⟩ := returns_map_elim_gd _ _ _ hX
  have h := facts.nd.ModelProperties_gradeContract_read_anchor n.cache S.E S.hc
    (M.toHealing n.st.core) r g hg
  rw [facts.gr.phaseResult_g1] at hframe
  rw [hframe] at h
  obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing n.st.core) r (some (some root))
  exact (h a ha).trans (facts.gr.anchor_of_activePrefix S.E S.hc _ r hactive a ha)

end

end DecoupledConsensusModel.Sts.Restated
