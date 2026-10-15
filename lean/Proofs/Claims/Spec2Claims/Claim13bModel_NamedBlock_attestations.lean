import Model.Vocabulary.Objects.NamedBlocks
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `NamedBlock.attestations`

The named attestations a named block includes: none for the named genesis, the attestation field of
a node otherwise.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.NamedBlock.attestations

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type}

/-- The named genesis includes no attestation. -/
theorem named_genesis_attestations : (NamedBlock.genesis : NamedBlock V).attestations = [] := rfl

/-- A named node includes exactly the attestations `rows` it carries. -/
theorem named_node_attestations (p : NamedBlock V) (s : Slot) (r : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V)) (proposer : V) :
    (NamedBlock.node p s r votes support rows proposer).attestations = rows := rfl

end DecoupledConsensusModel.Sts
