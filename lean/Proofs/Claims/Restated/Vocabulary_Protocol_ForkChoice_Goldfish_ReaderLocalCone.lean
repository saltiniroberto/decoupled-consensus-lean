import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ReaderLocalCone
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_FGForkChoice_Finality
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_ReaderLocalCone
import Model.Record.Wiring

/-!
# Canonical-cone witnesses and the filtered tree

When a block has a canonical-cone witness in a store, and which blocks this puts in the filtered
block tree, stated over a model `M : Record.Model V`.
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

/-- If `W` is in `st`'s tree, `P ⪯ W`, and `st.h_max ≤ (st.σ W).h + 1`, then `W` is a canonical-cone
    witness for `P` in `st`. -/
theorem Vocabulary.Proofs.HealingSurface.canonicalConeWitness_of_processedDescendant_and_hMax_le_succ (facts : Record.Facts M)
    {st : M.S} {P W : Block V}
    (hWT : W ∈ st.T) (hPW : Block.Preceq P W)
    (hbound : st.h_max ≤ (st.σ W).h + 1) :
    Restated.Vocabulary.Proofs.HealingSurface.CanonicalConeWitness M st P := by
  unfold Restated.Vocabulary.Proofs.HealingSurface.CanonicalConeWitness
  refine ⟨W, hWT, hPW, ?_⟩
  exact Nat.sub_le_iff_le_add.mpr hbound

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution

/-- If the FG root of `st` is an ancestor of, or is, `P`, `W` is in `st`'s tree with
    `st.h_max - 1 ≤ (st.σ W).h`, and `P ⪯ D ⪯ W`, then `D` is in the filtered block tree of `st`. -/
theorem Vocabulary.Proofs.HealingSurface.canonicalConeSegment_mem_filtered_of_root_preceq (facts : Record.Facts M)
    {st : M.S} (hpc : Restated.Vocabulary.Internal.ParentClosed M st)
    (hFJ : Block.Preceq st.F st.J)
    {P W D : Block V}
    (hrootP : Block.Preceq
      (M.get_fg_root (M.toHealing st).toFG) P)
    (hWT : W ∈ st.T)
    (hheight : st.h_max - 1 ≤ (st.σ W).h)
    (hPD : Block.Preceq P D) (hDW : Block.Preceq D W) :
    D ∈ M.get_filtered_block_tree (M.toHealing st).toFG :=
  facts.fc.canonicalConeSegment_mem_filtered_of_root_preceq hpc hFJ hrootP hWT hheight hPD hDW

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution

/-- If `P` is compatible with the FG root of `st` and has a canonical-cone witness in `st`, then `P`
    is an ancestor of, or is, the FG root, or `P` is in the filtered block tree. -/
theorem Vocabulary.Proofs.HealingSurface.canonicalFloor_preceq_root_or_mem_filtered (facts : Record.Facts M)
    {st : M.S} (hpc : Restated.Vocabulary.Internal.ParentClosed M st)
    (hFJ : Block.Preceq st.F st.J) {P : Block V}
    (hcompat : Block.compatible
      (M.get_fg_root (M.toHealing st).toFG) P = true)
    (hwitness : Restated.Vocabulary.Proofs.HealingSurface.CanonicalConeWitness M st P) :
    Block.Preceq P (M.get_fg_root (M.toHealing st).toFG) ∨
      P ∈ M.get_filtered_block_tree (M.toHealing st).toFG := by
  simp only [Block.compatible, Bool.or_eq_true] at hcompat
  rcases hcompat with hrootP | hProot
  · right
    obtain ⟨W, hWT, hPW, hheight⟩ := hwitness
    exact Restated.Vocabulary.Proofs.HealingSurface.canonicalConeSegment_mem_filtered_of_root_preceq facts hpc hFJ
      (P := P) (by unfold Block.Preceq; exact hrootP) hWT hheight
      (by unfold Block.Preceq; exact Block.preceq_self P) hPW
  · exact Or.inl (by unfold Block.Preceq; exact hProot)

end

end DecoupledConsensusModel.Sts.Restated
