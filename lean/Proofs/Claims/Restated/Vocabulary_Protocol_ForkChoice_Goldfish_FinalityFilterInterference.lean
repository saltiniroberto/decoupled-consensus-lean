import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.FinalityFilterInterference
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterInterference
import Model.Record.Wiring

/-!
# When finality-filter noninterference fails

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: a block `P` is
neither an ancestor of a store's FG root nor in its filtered block tree exactly when that root
conflicts with `P`, or the root is a strict ancestor of `P` and the filter removes `P`.
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

/-- For one store `st`, `P` is neither an ancestor of `st`'s FG root nor in `st`'s filtered block
    tree exactly when that root conflicts with `P`, or the root is a strict ancestor of `P` and the
    filter removes `P`. -/
private theorem not_noninterference_store_iff (facts : Record.Facts M) (st : M.NS) (P : Block V) :
    (¬ (Block.Preceq P (M.get_fg_root st.toHealing.toFG) ∨
      P ∈ M.get_filtered_block_tree st.toHealing.toFG)) ↔
      Restated.Vocabulary.Proofs.HealingSurface.FGRootInterferenceAt M st P ∨
      Restated.Vocabulary.Proofs.HealingSurface.HeightFilterInterferenceAt M st P := by
  constructor
  · intro hnot
    have hnotPRoot : ¬ Block.Preceq P
        (M.get_fg_root st.toHealing.toFG) := by
      intro hPRoot
      exact hnot (Or.inl hPRoot)
    have hnotFiltered :
        P ∉ M.get_filtered_block_tree st.toHealing.toFG := by
      intro hfiltered
      exact hnot (Or.inr hfiltered)
    by_cases hrootP : Block.Preceq
        (M.get_fg_root st.toHealing.toFG) P
    · right
      refine ⟨?_, hnotFiltered⟩
      have hne : M.get_fg_root st.toHealing.toFG ≠ P := by
        intro heq
        apply hnotPRoot
        rw [heq]
        exact Proofs.ModelProperties.Preceq_self P
      exact Proofs.ModelProperties.Prec_of_ne_of_Preceq hne hrootP
    · left
      unfold Restated.Vocabulary.Proofs.HealingSurface.FGRootInterferenceAt
      exact Proofs.ModelProperties.compatible_eq_false_of_not_Preceq hrootP hnotPRoot
  · intro hint hquiet
    rcases hint with hroot | hheight
    · unfold Restated.Vocabulary.Proofs.HealingSurface.FGRootInterferenceAt at hroot
      have hcompat : Block.compatible
          (M.get_fg_root st.toHealing.toFG) P = true := by
        rcases hquiet with hPRoot | hfiltered
        · exact Proofs.ModelProperties.compatible_eq_true_of_Preceq_symm hPRoot
        · exact Proofs.ModelProperties.compatible_eq_true_of_Preceq
            (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp
              (facts.fc.preceq_get_fg_root_of_mem_filtered hfiltered))
      rw [hcompat] at hroot
      simp at hroot
    · rcases hheight with ⟨hstrict, hnotFiltered⟩
      rcases hquiet with hPRoot | hfiltered
      · exact Proofs.ModelProperties.ne_of_Prec hstrict
          (Proofs.ModelProperties.Preceq_antisymm
            (Proofs.ModelProperties.Preceq_of_Prec hstrict) hPRoot)
      · exact hnotFiltered hfiltered

/-- In the world `wd`, `FinalityFilterNoninterferenceAtRead` fails for `P` at `w`'s store exactly
    when that store's FG root conflicts with `P`, or that root is a strict ancestor of `P` and the
    store's filter removes `P`. -/
theorem Vocabulary.Proofs.HealingSurface.not_finalityFilterNoninterferenceAtRead_iff (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (w : V) (read : Time) (wd : V → M.N) (P : Block V) :
    (¬ Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead M S rho w read wd P) ↔
      Restated.Vocabulary.Proofs.HealingSurface.FGRootInterferenceAt M (wd w).st P ∨
        Restated.Vocabulary.Proofs.HealingSurface.HeightFilterInterferenceAt M (wd w).st P :=
  not_noninterference_store_iff facts (wd w).st P

end

end DecoupledConsensusModel.Sts.Restated
