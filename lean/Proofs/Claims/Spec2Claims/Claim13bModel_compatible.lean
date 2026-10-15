module
public import Model.Vocabulary.Objects.Blocks
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Proofs.Claims.ModelIrreducible
public import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq

@[expose] public section

/-!
# Facts about `Block.compatible`

Two blocks are compatible when one is an ancestor of the other.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Compatible
  DecoupledConsensusModel.Block.Preceq DecoupledConsensusModel.Block.compatible

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If `A` and `B` are compatible, then `A ⪯ B` or `B ⪯ A`. -/
theorem compatible_cases {A B : Block V} (h : Block.compatible A B = true) :
    Block.Preceq A B ∨ Block.Preceq B A := by
  simp only [Block.compatible, Bool.or_eq_true] at h
  exact h

/-- If `A ⪯ B` or `B ⪯ A`, then `A` and `B` are compatible. -/
theorem compatible_of_cases {A B : Block V} (h : Block.Preceq A B ∨ Block.Preceq B A) :
    Block.compatible A B = true := by
  simp only [Block.compatible, Bool.or_eq_true]
  exact h

/-- `Block.Compatible A B` holds exactly when `Block.compatible A B` is `true`. -/
theorem compatible_iff_Compatible {A B : Block V} :
    Block.Compatible A B ↔ Block.compatible A B = true := Iff.rfl

/-- If `X ⪯ Z` and `Y ⪯ Z`, then `X` and `Y` are compatible. -/
theorem compatible_of_preceq_common_Preceq {X Y Z : Block V} (hX : Block.Preceq X Z)
    (hY : Block.Preceq Y Z) : Block.compatible X Y = true :=
  compatible_of_cases (preceq_linear_Preceq hX hY)

end DecoupledConsensusModel.Sts
