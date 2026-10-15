import Model.Vocabulary.Objects.Blocks
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Block.Prec`

The proposition that one block is a strict ancestor of another, stated over the Boolean
`Block.prec`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Prec
  DecoupledConsensusModel.Block.Preceq DecoupledConsensusModel.Block.prec

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- `A` is a strict ancestor of `B` exactly when `A ≠ B` and `A ⪯ B`. -/
theorem prec_iff_ne_Preceq {A B : Block V} : Block.Prec A B ↔ A ≠ B ∧ Block.Preceq A B := by
  simp only [Block.Prec, Block.prec, Block.Preceq, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not]

end DecoupledConsensusModel.Sts
