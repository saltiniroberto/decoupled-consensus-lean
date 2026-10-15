module
public import Proofs.Vocabulary.Objects.Ancestry
public import Proofs.Vocabulary.Internal.Definitions.PhaseGrades
public import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.Blocks
public import Model.Vocabulary.Protocol.Grades
import Proofs.Vocabulary.ModelVocabulary.Substrate.Time
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Tactic.ENatToNat
public import Mathlib.Analysis.Convex.Cone.Basic

@[expose] public section

/-!
# Cutoff monotonicity of the grade inputs

The grade input sets grow with their cutoff, the ready view is contained in the raw view, the phase
cutoffs are nested, and a supporter of a block opposes every conflicting block.
-/


namespace DecoupledConsensusModel.Proofs.GradeCutoffMono

open Internal.PhaseGrades DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token Supports Opposes)

variable {V : Type} [DecidableEq V] [Fintype V]

theorem stampedBefore_mono {α : Type} (ts : TimestampMap α) {c d : Time} (hcd : c ≤ d)
    {x : α} (h : stampedBefore ts c x = true) : stampedBefore ts d x = true := by
  rw [stampedBefore_eq_occurrenceBefore] at h ⊢
  exact occurrenceBefore_mono hcd h

theorem rawInputs_mono (gv : Protocol.GradeView V) (eta r : Round) {c d : Time}
    (hcd : c ≤ d) (sender : V) :
    DecoupledConsensusModel.Protocol.rawInputs gv eta r c sender ⊆
      DecoupledConsensusModel.Protocol.rawInputs gv eta r d sender := by
  intro u hu
  simp only [DecoupledConsensusModel.Protocol.rawInputs, Finset.mem_filter] at hu ⊢
  exact ⟨hu.1, hu.2.1, occurrenceBefore_mono hcd hu.2.2⟩

theorem bodyReady_mono (gv : Protocol.GradeView V) (F : Block V) {c d : Time}
    (hcd : c ≤ d) (u : Protocol.SGVote V)
    (h : DecoupledConsensusModel.Protocol.bodyReady gv F c u = true) :
    DecoupledConsensusModel.Protocol.bodyReady gv F d u = true := by
  cases hconf : u.confirmed with
  | none => simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf]
  | some root =>
    simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf] at h ⊢
    cases hf : Block.find? gv.T root with
    | none => rw [hf] at h; exact absurd h (by simp)
    | some H =>
      rw [hf] at h
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨stampedBefore_mono _ hcd h.1, h.2⟩

theorem interpretedInputs_mono (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    {c d : Time} (hcd : c ≤ d) (sender : V) :
    DecoupledConsensusModel.Protocol.interpretedInputs gv F eta r c sender ⊆
      DecoupledConsensusModel.Protocol.interpretedInputs gv F eta r d sender := by
  intro u hu
  simp only [DecoupledConsensusModel.Protocol.interpretedInputs, Finset.mem_filter] at hu ⊢
  exact ⟨rawInputs_mono gv eta r hcd sender hu.1, bodyReady_mono gv F hcd u hu.2⟩

theorem readyView_mono (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    {c d : Time} (hcd : c ≤ d) (v : V) :
    readyView gv F eta r c v ⊆ readyView gv F eta r d v :=
  Finset.image_subset_image (interpretedInputs_mono gv F eta r hcd v)

theorem rawView_mono (gv : Protocol.GradeView V) (eta r : Round)
    {c d : Time} (hcd : c ≤ d) (v : V) :
    rawView gv eta r c v ⊆ rawView gv eta r d v :=
  Finset.image_subset_image (rawInputs_mono gv eta r hcd v)

theorem readyView_subset_rawView (gv : Protocol.GradeView V) (F : Block V)
    (eta r : Round) (c : Time) (v : V) :
    readyView gv F eta r c v ⊆ rawView gv eta r c v :=
  Finset.image_subset_image (Finset.filter_subset _ _)

/-! ## The nested phase windows -/

theorem early_g2_le_early_g1 (E : Env V) (hc : Protocol.HealConfig) (r : Round) :
    early E hc r .g2 ≤ early E hc r .g1 := by
  simp only [early, Phase.earlyOffset]
  exact Int.add_le_add_left
    (Int.mul_le_mul_of_nonneg_right (by decide) E.Δ_pos.le) _

theorem early_g2_le_early_g0 (E : Env V) (hc : Protocol.HealConfig) (r : Round) :
    early E hc r .g2 ≤ early E hc r .g0 := by
  simp only [early, Phase.earlyOffset]
  exact Int.add_le_add_left
    (Int.mul_le_mul_of_nonneg_right (by decide) E.Δ_pos.le) _


theorem early_le_late (E : Env V) (hc : Protocol.HealConfig) (r : Round) (p : Phase) :
    early E hc r p ≤ late E hc r p := by
  cases p <;>
    simp only [early, late, Phase.earlyOffset, Phase.lateOffset] <;>
    exact Int.add_le_add_left
      (Int.mul_le_mul_of_nonneg_right (by decide) E.Δ_pos.le) _


/-! ## Support of one block opposes any conflicting block -/

theorem opposing_of_positive_conflicts (E : Env V) (hc : Protocol.HealConfig)
    (gv : Protocol.GradeView V) (F : Block V) (r : Round) (p : Phase) (v : V)
    {B B' : Block V} (hconf : Block.conflicts B' B = true)
    (h : positive gv F hc.η_SG r (early E hc r p) (late E hc r p) v B' = true) :
    opposing gv F hc.η_SG r (early E hc r p) (late E hc r p) v B = true := by
  simp only [positive, decide_eq_true_eq] at h
  simp only [opposing, decide_eq_true_eq]
  obtain ⟨u, hu, hmax, hcov, -, -⟩ := h
  refine Or.inl ⟨u, readyView_mono gv F hc.η_SG r (early_le_late E hc r p) v hu,
    hmax, ?_⟩
  intro hcovB
  have hcompat : Block.compatible B' B = true := by
    simp only [localCovers] at hcov hcovB
    cases hkey : u.key with
    | none => simp [Protocol.head_covers, hkey] at hcov
    | some root =>
      simp only [Protocol.head_covers, hkey] at hcov hcovB
      cases hf : Block.find? gv.T root with
      | none => simp [hf] at hcov
      | some head =>
        simp only [hf] at hcov hcovB
        exact Block.compatible_of_preceq_common hcov hcovB
  simp [Block.conflicts, hcompat] at hconf

#print axioms opposing_of_positive_conflicts

end DecoupledConsensusModel.Proofs.GradeCutoffMono

end
