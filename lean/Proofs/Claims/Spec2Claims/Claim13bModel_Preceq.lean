module
public import Model.Vocabulary.Objects.Blocks
public import Proofs.Vocabulary.Objects.Ancestry
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Block.Preceq`

The proposition that one block is an ancestor of another or the block itself, stated over the
Boolean `Block.preceq`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Block.preceq DecoupledConsensusModel.NamedBlock.Preceq

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- `Block.Preceq A B` holds exactly when the Boolean test `Block.preceq A B` is `true`. -/
theorem preceq_eq_true_iff_Preceq {A B : Block V} :
    Block.preceq A B = true ↔ Block.Preceq A B := by
  unfold Block.Preceq
  exact Iff.rfl

/-- `Block.Preceq` is transitive. -/
theorem preceq_trans_Preceq {A B C : Block V} (h₁ : Block.Preceq A B) (h₂ : Block.Preceq B C) :
    Block.Preceq A C :=
  preceq_eq_true_iff_Preceq.mp
    (Block.preceq_trans (preceq_eq_true_iff_Preceq.mpr h₁) (preceq_eq_true_iff_Preceq.mpr h₂))

/-- If `X ⪯ Z` and `Y ⪯ Z`, then `X ⪯ Y` or `Y ⪯ X`. -/
theorem preceq_linear_Preceq {X Y Z : Block V} (hX : Block.Preceq X Z) (hY : Block.Preceq Y Z) :
    Block.Preceq X Y ∨ Block.Preceq Y X :=
  (Block.preceq_linear (preceq_eq_true_iff_Preceq.mpr hX) (preceq_eq_true_iff_Preceq.mpr hY)).imp
    preceq_eq_true_iff_Preceq.mp preceq_eq_true_iff_Preceq.mp

/-- The only block `A` with `A ⪯ genesis` is genesis. -/
theorem eq_genesis_of_Preceq_genesis {A : Block V} (h : Block.Preceq A Block.genesis) :
    A = Block.genesis := by
  simpa only [Block.Preceq, Block.preceq, decide_eq_true_eq] using h

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

end DecoupledConsensusModel.Sts
