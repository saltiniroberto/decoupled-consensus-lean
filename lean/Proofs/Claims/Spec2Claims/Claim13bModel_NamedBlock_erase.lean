import Model.Vocabulary.Objects.NamedBlocks
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `NamedBlock.erase`

The lemmas that unfold `NamedBlock.erase`, which forgets the names a named block carries and returns
the block.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.NamedBlock.erase

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type}

/-- The named genesis erases to the genesis block. -/
theorem erase_named_genesis : (NamedBlock.genesis : NamedBlock V).erase = Block.genesis := rfl

/-- Only the named genesis erases to the genesis block. -/
theorem eq_named_genesis_of_erase_eq_genesis {B : NamedBlock V} (h : B.erase = Block.genesis) :
    B = NamedBlock.genesis := by
  cases B with
  | genesis => rfl
  | node => simp [NamedBlock.erase] at h

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

/-- A named node erases to the block node with the erased parent, the same slot, root, votes,
    support votes and proposer, and the erased rows. -/
theorem erase_named_node {V : Type} (p : NamedBlock V) (s : Slot) (r : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V)) (proposer : V) :
    (NamedBlock.node p s r votes support rows proposer).erase =
      Block.node p.erase s r votes support (rows.map NamedAttestation.erase) proposer := rfl

end DecoupledConsensusModel.Sts
