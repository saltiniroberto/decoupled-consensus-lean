module
public import Model.Vocabulary.Objects.Blocks
public import Proofs.Claims.ModelIrreducible
public import Proofs.Claims.Spec2Claims.Claim13bModel_compatible

@[expose] public section

/-!
# More facts about `Block.Prec`

When a block is a strict ancestor of another.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Prec
  DecoupledConsensusModel.Block.Preceq DecoupledConsensusModel.Block.prec

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]


/-- If `A` and `B` are compatible and `B` is not an ancestor of `A`, then `A` is a strict ancestor
    of `B`. -/
theorem prec_of_compatible_of_not_preceq {A B : Block V} (hcompat : Block.Compatible A B)
    (hnot : ¬ Block.Preceq B A) : Block.Prec A B := by
  rcases compatible_cases (compatible_iff_Compatible.mp hcompat) with hAB | hBA
  · have hne : A ≠ B := by
      rintro rfl
      exact hnot hAB
    simp only [Block.Prec, Block.prec, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not]
    exact ⟨hne, hAB⟩
  · exact absurd hBA hnot

end DecoupledConsensusModel.Sts
