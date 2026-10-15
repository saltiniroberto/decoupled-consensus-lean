import Model.Vocabulary.Objects.Blocks
import Proofs.Claims.ModelIrreducible

/-!
# The slot of genesis

Genesis is of slot `0`.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.slot

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

/-- Genesis is of slot `0`. -/
theorem genesis_slot_inclG2 {V : Type} : (Block.genesis : Block V).slot = 0 := rfl

end DecoupledConsensusModel.Sts
