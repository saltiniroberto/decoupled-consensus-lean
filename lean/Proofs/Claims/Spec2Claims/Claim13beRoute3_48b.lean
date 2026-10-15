import Proofs.Claims.Spec2Claims.Claim13beRoute3_48
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmationReadFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_incl
import Proofs.Claims.Spec2Claims.Claim13bModel_actionStoreAt
import Proofs.Claims.Spec2Claims.Claim13bModel_actionReadFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_grade2Block_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_currentSGVote_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_interpretedInputs
import Proofs.Claims.Spec2Claims.Claim13bModel_voter_processed_block_tree
import Proofs.Claims.Spec2Claims.Claim13bModel_get_filtered_block_tree_from
import Proofs.Claims.Spec2Claims.Claim13bModel_voter_filtered_block_tree
import Proofs.Claims.Spec2Claims.Claim13bModel_domain_attest

/-!
# Phase domains

Every phase domain of a round is at or before its G0 domain.
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

variable {V : Type} [DecidableEq V] [Fintype V]

section ActionSourceCore

open DecoupledConsensusModel.Proofs.HealingLemmas

/-- `domain r p ≤ domain r .g0` for every phase `p`: the G0 domain is the latest of a round's phase
    domains. -/
theorem domain_le_domain_g0 (S : Setup V) (r : Round) (p : Phase) :
    domain S.E S.hc r p ≤ domain S.E S.hc r .g0 := by
  have hΔ := S.E.Δ_pos
  rw [Sts.domain_g0_eq_opening]
  cases p
  · rw [Sts.domain_g0_eq_opening]
  · rw [Sts.domain_g1_eq_opening]; linarith
  · rw [Sts.domain_g2_eq_opening]; linarith

end ActionSourceCore

end DecoupledConsensusModel.Sts
