module
public import Model.Vocabulary.Protocol.Grades
public import Proofs.Claims.ModelIrreducible
public import Proofs.Vocabulary.Protocol.ValidatorClient.Engine
public import Proofs.Claims.Spec2Claims.Claim13bModel_compatible

@[expose] public section

/-!
# `Protocol.currentSGVote` against a fixed block

When the output of the SG walk is compatible with a given block, and the walk's output in its later
cases.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.currentSGVote

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- The SG walk's output is compatible with `T` when the store's `live_confirmed`, every grade-2
    candidate of the read, the read's anchor and the store's `get_fg_root` all are. -/
theorem sgVote_compatible {stH : Protocol.HealingStore V} {grades : Protocol.GradeRead V}
    {T : Block V}
    (hconf : Block.compatible stH.live_confirmed T = true)
    (hQ2 : ∀ Q : Block V, grades.Q2 = some Q → Block.compatible Q T = true)
    (hanchor : Block.compatible grades.anchor T = true)
    (hfg : Block.compatible (Protocol.get_fg_root stH.toFG) T = true) :
    Block.compatible (Protocol.currentSGVote stH grades) T = true := by
  unfold Protocol.currentSGVote
  cases hdc : Protocol.deepest_clear (some grades.anchor) stH.live_confirmed grades.clear with
  | some B =>
      have hB := Proofs.Engine.deepest_clear_preceq hdc
      rcases compatible_cases hconf with hlc | hlc
      · exact Block.compatible_of_preceq_common
          (Block.preceq_trans hB (preceq_eq_true_iff_Preceq.mpr hlc)) (Block.preceq_self T)
      · exact Block.compatible_of_preceq_common hB (preceq_eq_true_iff_Preceq.mpr hlc)
  | none =>
      cases hQ : grades.Q2 with
      | some Q => exact hQ2 Q hQ
      | none =>
          dsimp only
          split
          · exact hfg
          · exact hanchor

/-- If the clearing walk from the anchor finds no block and the grade read offers the grade-2
    candidate `Q`, the SG walk returns `Q`. -/
theorem currentSGVote_of_Q2 {stH : Protocol.HealingStore V} {grades : Protocol.GradeRead V}
    {Q : Block V}
    (hdc : Protocol.deepest_clear (some grades.anchor) stH.live_confirmed grades.clear = none)
    (hQ : grades.Q2 = some Q) : Protocol.currentSGVote stH grades = Q := by
  unfold Protocol.currentSGVote
  rw [hdc]
  simp only [hQ]

/-- If the clearing walk finds no block and the grade read offers no grade-2 candidate, the SG walk
    returns the store's `get_fg_root` or the grade read's anchor. -/
theorem currentSGVote_of_none_none {stH : Protocol.HealingStore V}
    {grades : Protocol.GradeRead V}
    (hdc : Protocol.deepest_clear (some grades.anchor) stH.live_confirmed grades.clear = none)
    (hQ : grades.Q2 = none) :
    Protocol.currentSGVote stH grades = Protocol.get_fg_root stH.toFG ∨
      Protocol.currentSGVote stH grades = grades.anchor := by
  unfold Protocol.currentSGVote
  rw [hdc]
  simp only [hQ]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

end DecoupledConsensusModel.Sts
