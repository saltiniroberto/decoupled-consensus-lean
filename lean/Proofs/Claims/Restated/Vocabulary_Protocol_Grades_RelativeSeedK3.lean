import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RelativeOneChain
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Record.Wiring

/-!
# G0 and G1 grades of one read

A block with grade G0 is in the store's tree, and two blocks with grade G1 in the same read are
compatible, stated over a model `M : Record.Model V`.
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
open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Protocol Proofs.HealingLemmas Proofs.Optimistic DecoupledConsensusModel.Protocol

/-- For every node state `n` that `w` can hold before round `r`'s G0 domain time, if the store grade
    of `n`'s store can give `Q` grade G0 at round `r`, then `Q` is in the block tree of `n`'s store. -/
theorem Vocabulary.Proofs.HealingSurface.storeGrade_g0_mem_domainTree (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) {r : Round} {w : V} {Q : Block V} :
    ∀ n ∈ Restated.Vocabulary.Internal.PhaseGrades.readAt M S rho (M.domain S.E S.hc r .g0) w,
    Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc n.st r .g0 Q ⇢ true →
    Q ∈ n.st.core.T := by
  intro n hn hG0
  obtain ⟨W, hW, rfl⟩ := hn
  have hgrade : M.gradeBool S.E
      (M.gradeView (M.toHealing (W w).st.core)) (W w).st.core.F S.hc.η_SG r
      (M.early S.E S.hc r .g0) (M.late S.E S.hc r .g0) Q ⇢ true := hG0
  obtain ⟨H, hHT, hQH⟩ :=
    facts.gr.ModelProperties_exists_mem_T_preceq_of_gradeBool _ _ _ _ _ _ _ true hgrade rfl
  have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho
    (M.domain S.E S.hc r .g0) w W hW
  unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
  have hQ := Proofs.Records.mem_of_preceq hpc.2 Q H hHT
    (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hQH)
  rw [facts.sto.toHealing_T] at hQ
  exact hQ

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Protocol Proofs.HealingLemmas Proofs.Optimistic DecoupledConsensusModel.Protocol

/-- For every node state `n` that `w` can hold before round `r`'s G1 domain time, two blocks the
    store grade of `n`'s store can give grade G1 at round `r` are compatible. -/
theorem Vocabulary.Proofs.HealingSurface.relativeSeed_sameReaderG1_compatible (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (r : Round) (w : V) {A Q : Block V} :
    ∀ n ∈ Restated.Vocabulary.Internal.PhaseGrades.readAt M S rho (M.domain S.E S.hc r .g1) w,
    Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc n.st r .g1 A ⇢ true →
    Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc n.st r .g1 Q ⇢ true →
    Block.compatible A Q = true := by
  intro n _ hA hQ
  change M.gradeBool S.E (M.gradeView (M.toHealing n.st.core)) n.st.core.F S.hc.η_SG r
    (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) A ⇢ true at hA
  change M.gradeBool S.E (M.gradeView (M.toHealing n.st.core)) n.st.core.F S.hc.η_SG r
    (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) Q ⇢ true at hQ
  exact Restated.Vocabulary.Proofs.HealingSurface.graded_oneChain_at_reader facts S.E
    (M.gradeView (M.toHealing n.st.core)) n.st.core.F S.hc.η_SG r
    (facts.gr.early_le_late S.E S.hc r .g1) true hA rfl true hQ rfl

end

end DecoupledConsensusModel.Sts.Restated
