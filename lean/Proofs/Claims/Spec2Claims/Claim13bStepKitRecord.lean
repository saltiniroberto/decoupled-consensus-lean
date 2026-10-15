module
public import Proofs.Claims.Spec2Claims.Claim13bStepKitStore
public import Proofs.Claims.Spec2Claims.Claim13bInvariant
public import Proofs.Claims.Spec2Claims.Claim13bModel_gradeView
public import Proofs.Claims.Spec2Claims.Claim13bModel_Store_sg_pool
public import Proofs.Claims.Spec2Claims.Claim13bModel_sgVote
public import Proofs.Claims.Spec2Claims.Claim13bModel_confirmationReadFrom
public import Proofs.Claims.Spec2Claims.Claim13bModel_slotStart_mk
public import Proofs.Claims.Spec2Claims.Claim13bModel_support_cutoff
public import Model.Vocabulary.Protocol.ValidatorClient
public import Proofs.Claims.ModelIrreducible
public import Proofs.Claims.Spec2Claims.Claim13bModel_on_sg_vote
public import Proofs.Claims.Spec2Claims.Claim13bModel_round_votes
public import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAttestation_erase

@[expose] public section

/-!
# Imports for the attestation receipt and record facts

This file declares nothing; it gathers the imports that the facts on attestation receipt and on
records rely on.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Sts
