module
public import Model.Vocabulary.Objects.NamedBlocks

@[expose] public section

/-!
# Facts about `NamedBlock.parent`

The parent of a named block.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type}

/-- The parent of the named block built on `p` is `p`. -/
theorem named_parent_node (p : NamedBlock V) (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V)) (proposer : V) :
    (NamedBlock.node p s root votes support rows proposer).parent = p := rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
