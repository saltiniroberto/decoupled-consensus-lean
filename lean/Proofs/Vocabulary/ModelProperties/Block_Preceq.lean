module
public import Model.Vocabulary.Objects.Blocks
public import Proofs.Vocabulary.Objects.Ancestry

@[expose] public section

/-!
# Facts about `Block.Preceq`

The ancestry proposition `Block.Preceq` against the Boolean test `Block.preceq`, read by proofs in
place of the definition.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V]

/-- `Block.preceq A B` is `true` exactly when `Block.Preceq A B`. -/
theorem preceq_eq_true_iff_Preceq {A B : Block V} :
    Block.preceq A B = true ↔ Block.Preceq A B := Iff.rfl

/-- Every block is its own ancestor in the Prop form. -/
theorem Preceq_self (A : Block V) : Block.Preceq A A :=
  preceq_eq_true_iff_Preceq.mp (Block.preceq_self A)

/-- The ancestry proposition is transitive. -/
theorem Preceq_trans {A B C : Block V} (h₁ : Block.Preceq A B) (h₂ : Block.Preceq B C) :
    Block.Preceq A C :=
  preceq_eq_true_iff_Preceq.mp
    (Block.preceq_trans (preceq_eq_true_iff_Preceq.mpr h₁) (preceq_eq_true_iff_Preceq.mpr h₂))

/-- Two ancestors of one block are ordered by ancestry. -/
theorem Preceq_linear {X Y Z : Block V} (hX : Block.Preceq X Z) (hY : Block.Preceq Y Z) :
    Block.Preceq X Y ∨ Block.Preceq Y X :=
  Block.preceq_linear (preceq_eq_true_iff_Preceq.mpr hX) (preceq_eq_true_iff_Preceq.mpr hY)

/-- The ancestry proposition is antisymmetric. -/
theorem Preceq_antisymm {B C : Block V} (h₁ : Block.Preceq B C) (h₂ : Block.Preceq C B) :
    B = C :=
  Block.preceq_antisymm (preceq_eq_true_iff_Preceq.mpr h₁) (preceq_eq_true_iff_Preceq.mpr h₂)

end DecoupledConsensusModel.Proofs.ModelProperties

end
