module
public import Model.Vocabulary.Execution.Objects
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `NamedObject.author`

The author of a named block, Goldfish vote or attestation.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Execution.NamedObject.author

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

/-- The author of a named block, as an object, is the block's proposer. -/
theorem author_block {V : Type} (B : NamedBlock V) :
    NamedObject.author (NamedObject.block B) = B.proposer? := rfl

/-- The author of the Goldfish vote `u`, as an object, is `u.val_index`. -/
theorem author_gfVote {V : Type} (u : GoldfishVote V) :
    NamedObject.author (NamedObject.gfVote u) = some u.val_index := rfl

/-- The author of the named attestation `a`, as an object, is `a.val_index`. -/
theorem author_attest {V : Type} (a : NamedAttestation V) :
    NamedObject.author (NamedObject.attest a) = some a.val_index := rfl

end DecoupledConsensusModel.Sts
