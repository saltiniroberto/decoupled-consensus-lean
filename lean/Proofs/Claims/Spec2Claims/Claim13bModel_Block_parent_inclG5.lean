import Model.Vocabulary.Objects.Blocks
import Proofs.Claims.ModelIrreducible

/-!
# The partial and total parent of a block

A block other than genesis has its total parent `Block.parent` as its partial parent
`Block.parent?`, and a block of a positive slot is not genesis.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.parent
  DecoupledConsensusModel.Block.parent? DecoupledConsensusModel.Block.slot

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type}

/-- If `C` is not the genesis block, then `C.parent?` names `C.parent`. -/
theorem parent?_eq_some_parent_of_ne_genesis {C : Block V} (h : C ≠ Block.genesis) :
    C.parent? = some C.parent := by
  cases C with
  | genesis => exact absurd rfl h
  | node p _ _ _ _ _ _ => rfl

/-- If `C`'s slot is positive, then `C` is not the genesis block. -/
theorem ne_genesis_of_slot_pos {C : Block V} (h : 0 < C.slot) : C ≠ Block.genesis := by
  rintro rfl
  exact absurd h (by simp [Block.slot])

end DecoupledConsensusModel.Sts
