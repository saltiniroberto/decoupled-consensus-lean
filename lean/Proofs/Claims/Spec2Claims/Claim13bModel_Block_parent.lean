import Model.Vocabulary.Objects.Blocks
import Proofs.Claims.ModelIrreducible

/-!
# The partial parent of a block

A fact about `Block.parent?`, the partial parent of a block.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.parent
  DecoupledConsensusModel.Block.parent?

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type}

/-- If `C.parent?` names some block `B`, then `C` is not the genesis block. -/
theorem ne_genesis_of_parent?_eq_some {C B : Block V} (h : C.parent? = some B) :
    C ≠ Block.genesis := by
  rintro rfl
  simp [Block.parent?] at h

end DecoupledConsensusModel.Sts
