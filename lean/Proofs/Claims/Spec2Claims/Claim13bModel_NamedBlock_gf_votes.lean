import Model.Vocabulary.Objects.NamedBlocks
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `NamedBlock.gf_votes`

The Goldfish votes a named block includes: none for the named genesis, the vote field of a node
otherwise.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.NamedBlock.gf_votes

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type}

/-- The named genesis includes no Goldfish vote. -/
theorem named_genesis_gf_votes : (NamedBlock.genesis : NamedBlock V).gf_votes = [] := rfl

end DecoupledConsensusModel.Sts
