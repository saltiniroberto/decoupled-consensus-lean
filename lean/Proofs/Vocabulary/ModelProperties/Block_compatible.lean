module
public import Model.Vocabulary.Objects.Blocks
public import Proofs.Vocabulary.ModelProperties.Block_Preceq

@[expose] public section

/-!
# Facts about `Block.compatible`

The Boolean compatibility test of two blocks against the ancestry proposition, read by proofs in
place of the definition.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V]

/-- If `A` is an ancestor of `B`, the compatibility test of `A` and `B` is `true`. -/
theorem compatible_eq_true_of_Preceq {A B : Block V} (h : Block.Preceq A B) :
    Block.compatible A B = true := by
  unfold Block.compatible
  rw [preceq_eq_true_iff_Preceq.mpr h, Bool.true_or]

/-- If `B` is an ancestor of `A`, the compatibility test of `A` and `B` is `true`. -/
theorem compatible_eq_true_of_Preceq_symm {A B : Block V} (h : Block.Preceq B A) :
    Block.compatible A B = true := by
  unfold Block.compatible
  rw [preceq_eq_true_iff_Preceq.mpr h, Bool.or_true]

/-- If neither of `A` and `B` is an ancestor of the other, the compatibility test of `A` and `B` is
    `false`. -/
theorem compatible_eq_false_of_not_Preceq {A B : Block V} (h₁ : ¬ Block.Preceq A B)
    (h₂ : ¬ Block.Preceq B A) : Block.compatible A B = false := by
  unfold Block.compatible
  rw [Bool.eq_false_of_not_eq_true (fun h => h₁ (preceq_eq_true_iff_Preceq.mp h)),
    Bool.eq_false_of_not_eq_true (fun h => h₂ (preceq_eq_true_iff_Preceq.mp h)), Bool.or_false]

end DecoupledConsensusModel.Proofs.ModelProperties

end
