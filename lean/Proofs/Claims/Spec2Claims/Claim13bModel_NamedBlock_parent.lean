import Model.Vocabulary.Objects.NamedBlocks
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `NamedBlock.parent`

The parent a named block records, with the named genesis its own parent.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.NamedBlock.parent

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type}

/-- The parent of a named node is the block `p` it was built on. -/
theorem namedBlock_parent_node (p : NamedBlock V) (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V)) (proposer : V) :
    (NamedBlock.node p s root votes support rows proposer).parent = p := rfl

/-- The named genesis is its own parent. -/
theorem namedBlock_parent_genesis :
    (NamedBlock.genesis : NamedBlock V).parent = NamedBlock.genesis := rfl

end DecoupledConsensusModel.Sts
