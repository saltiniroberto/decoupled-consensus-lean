module
public import Model.Vocabulary.Objects.NamedBlocks
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `NamedBlock.slot`

The slot a named block was proposed in: `0` for the named genesis, the slot field of a node
otherwise.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.NamedBlock.slot

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type}

/-- The named genesis is at slot `0`. -/
theorem named_genesis_slot : (NamedBlock.genesis : NamedBlock V).slot = 0 := rfl

/-- A named node is at the slot `s` it carries. -/
theorem named_node_slot (p : NamedBlock V) (s : Slot) (r : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V)) (proposer : V) :
    (NamedBlock.node p s r votes support rows proposer).slot = s := rfl

end DecoupledConsensusModel.Sts
