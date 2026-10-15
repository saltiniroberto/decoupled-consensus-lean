module

public import Model.Vocabulary.Objects.NamedBlocks
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Erasing a named attestation

`NamedAttestation.erase` keeps an attestation's round, validator, confirmed block and finality pair,
and erases its height pair.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.NamedAttestation.erase

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type}

/-- Erasing the named attestation `a` keeps its round. -/
theorem namedAttestation_erase_round (a : NamedAttestation V) : a.erase.round = a.round := rfl

/-- Erasing the named attestation `a` keeps its validator. -/
theorem namedAttestation_erase_val_index (a : NamedAttestation V) :
    a.erase.val_index = a.val_index := rfl

/-- The height pair of the erasure of `a` is the erasure of `a`'s height pair. -/
theorem namedAttestation_erase_height_pair (a : NamedAttestation V) :
    a.erase.height_pair = a.height_pair.erase := rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type}

/-- Erasing the named attestation `a` keeps its confirmed block. -/
theorem namedAttestation_erase_confirmed (a : NamedAttestation V) :
    a.erase.confirmed = a.confirmed := rfl

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type}

/-- Erasing the named attestation `a` keeps its finality pair. -/
theorem namedAttestation_erase_finality_pair (a : NamedAttestation V) :
    a.erase.finality_pair = a.finality_pair := rfl


end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type}


end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type}


end DecoupledConsensusModel.Sts
