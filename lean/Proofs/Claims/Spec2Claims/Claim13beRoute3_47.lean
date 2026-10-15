import Proofs.Claims.Spec2Claims.Claim13beRoute3_45b
import Proofs.Vocabulary.Protocol.Handlers.Proposer
import Proofs.Claims.Spec2Claims.Claim13bModel_Block_preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_own_lock
import Proofs.Claims.Spec2Claims.Claim13bModel_derive_named
import Proofs.Claims.Spec2Claims.Claim13bModel_equivocates
import Proofs.Claims.Spec2Claims.Claim13bModel_Store_pool
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_erase
import Proofs.Claims.Spec2Claims.Claim13bModel_Block_slot
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_gf_votes
import Proofs.Claims.Spec2Claims.Claim13bModel_domain_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_opening
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmationReadFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_stampedBefore
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeContract_inclG1
import Proofs.Claims.Spec2Claims.Claim13bModel_frameGradeRead_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedDuties_goldfish_vote_with
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_with
import Proofs.Claims.Spec2Claims.Claim13bModel_propose_block_with_snd
import Proofs.Claims.Spec2Claims.Claim13bModel_beforeCutoff
import Proofs.Claims.Spec2Claims.Claim13bModel_update_confirmation_with_phase
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedNode_tick
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedDuties_attest_with
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time
import Proofs.Claims.Spec2Claims.Claim13bModel_vote_time
import Proofs.Claims.Spec2Claims.Claim13bModel_view_freeze
import Proofs.Claims.Spec2Claims.Claim13bModel_toHealing
import Proofs.Claims.Spec2Claims.Claim13bModel_resolved
import Proofs.Claims.Spec2Claims.Claim13bModel_voter_view
import Proofs.Claims.Spec2Claims.Claim13bModel_proposer_view
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time_inclG1

/-!
# Confirmation instants

Every instant is at or before some slot's confirmation instant.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]

/-- For every instant `t` there is a slot whose confirmation instant is at least `t`. -/
theorem exists_confirmation_time_ge (S : Setup V) (t : Time) :
    ∃ s : Slot, t ≤ Protocol.confirmation_time S.E s := by
  refine ⟨t.toNat, ?_⟩
  have hΔ : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have ht : t ≤ (t.toNat : Int) := Int.self_le_toNat t
  have hnn : (0 : Int) ≤ (t.toNat : Int) := Int.natCast_nonneg _
  have hp : Protocol.proposal_time S.E t.toNat = 4 * S.E.Δ * (t.toNat : Int) := by
    have h := DecoupledConsensusModel.Sts.proposal_time_add S.E 0 t.toNat
    rw [Nat.zero_add, DecoupledConsensusModel.Sts.proposal_time_zero, zero_add] at h
    exact h
  rw [← DecoupledConsensusModel.Sts.proposal_time_add_six_delta, hp]
  nlinarith


end DecoupledConsensusModel.Sts
