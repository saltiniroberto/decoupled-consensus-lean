module
public import Model.Vocabulary.Objects.Blocks

@[expose] public section

/-!
# Facts about `Block.prec`

The Boolean strict ancestry test against the ancestry proposition, read by proofs in place of the
definition.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V]

/-- If `A` and `B` differ and `A` is an ancestor of `B`, the test `Block.prec A B` is `true`. -/
theorem prec_eq_true_of_ne_of_Preceq {A B : Block V} (hne : A ≠ B) (h : Block.Preceq A B) :
    Block.prec A B = true := by
  simp only [Block.prec, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  exact ⟨hne, h⟩

/-- If `A` and `B` differ and `A` is an ancestor of `B`, then `A` is a strict ancestor of `B`. -/
theorem Prec_of_ne_of_Preceq {A B : Block V} (hne : A ≠ B) (h : Block.Preceq A B) :
    Block.Prec A B :=
  prec_eq_true_of_ne_of_Preceq hne h

/-- A strict ancestor of `B` differs from `B`. -/
theorem ne_of_Prec {A B : Block V} (h : Block.Prec A B) : A ≠ B := by
  unfold Block.Prec Block.prec at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
  exact h.1

/-- A strict ancestor of `B` is an ancestor of `B`. -/
theorem Preceq_of_Prec {A B : Block V} (h : Block.Prec A B) : Block.Preceq A B := by
  unfold Block.Prec Block.prec at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
  exact h.2

end DecoupledConsensusModel.Proofs.ModelProperties

end
