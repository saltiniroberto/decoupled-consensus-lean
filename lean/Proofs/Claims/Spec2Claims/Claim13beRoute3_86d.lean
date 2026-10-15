import Proofs.Claims.Spec2Claims.Claim13beRoute3_86c
import Proofs.Claims.Spec2Claims.Claim13beRoute3_72
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeView
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeContract_inclG1
import Proofs.Claims.Spec2Claims.Claim13bModel_opening
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmationReadFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_localCovers
import Proofs.Claims.Spec2Claims.Claim13bModel_actionStoreAt
import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_domain_attest
import Proofs.Vocabulary.ModelProperties.gradeBool
import Proofs.Vocabulary.ModelProperties.Store_toHealing
import Proofs.Claims.Spec2Claims.Claim13bModel_vote_time
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time
import Proofs.Claims.Spec2Claims.Claim13bModel_slotStart

/-!
# Vote and proposal instants

The vote instant of a slot is strictly before the next slot's proposal instant.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]


section FirstInteriorAnchor

/-- `vote_time s < proposal_time (s + 1)`. -/
theorem voteTime_lt_nextProposal_l86d (E : Env V) (s : Slot) :
    Protocol.vote_time E s < Protocol.proposal_time E (s + 1) := by
  rw [← slotStart_add_delta_eq_vote_time, ← slotStart_eq_proposal_time, slotStart_succ]
  nlinarith [E.Δ_pos]

end FirstInteriorAnchor

end DecoupledConsensusModel.Sts
