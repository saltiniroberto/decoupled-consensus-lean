import Proofs.Claims.Spec2Claims.Claim13beRoute3_54
import Proofs.Claims.Spec2Claims.Claim13bModel_onPhaseTick_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_inWindow
import Proofs.Claims.Spec2Claims.Claim13beRoute3_53
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_Prec
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmationReadFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_incl
import Proofs.Claims.Spec2Claims.Claim13bModel_toHealing
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeContract_inclG1
import Proofs.Claims.Spec2Claims.Claim13bModel_get_head_in_tree_with_layer
import Proofs.Claims.Spec2Claims.Claim13bModel_voter_filtered_block_tree
import Proofs.Claims.Spec2Claims.Claim13bModel_Store_pool
import Proofs.Claims.Spec2Claims.Claim13bModel_beforeCutoff
import Proofs.Claims.Spec2Claims.Claim13bModel_stampedBefore
import Proofs.Claims.Spec2Claims.Claim13bModel_voter_view
import Proofs.Claims.Spec2Claims.Claim13bModel_Store_tau
import Proofs.Vocabulary.ModelProperties.NamedReceipt_processed
import Proofs.Vocabulary.ModelProperties.NamedDuties_goldfish_vote_with
import Proofs.Claims.Spec2Claims.Claim13bModel_voters_count
import Proofs.Claims.Spec2Claims.Claim13bModel_votes_by
import Proofs.Claims.Spec2Claims.Claim13bModel_equivocates
import Proofs.Claims.Spec2Claims.Claim13bModel_voter_processed_block_tree
import Proofs.Claims.Spec2Claims.Claim13bModel_get_filtered_block_tree_from
import Proofs.Vocabulary.ModelProperties.get_sg_root_with
import Proofs.Vocabulary.ModelProperties.confirmationReadFrom
import Proofs.Vocabulary.ModelProperties.Block_compatible
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_erase
import Proofs.Vocabulary.Protocol.Grades.ProposalParent
import Proofs.Claims.Spec2Claims.Claim13bModel_get_filtered_block_tree
import Proofs.Claims.Spec2Claims.Claim13bModel_get_fg_root
import Proofs.Claims.Spec2Claims.Claim13bModel_propose_block_with_snd
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG2
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG2b
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_poolStamps
import Proofs.Vocabulary.ModelProperties.NamedReceipt_process
import Proofs.Vocabulary.ModelProperties.NamedNode_tick
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time_inclG1
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time
import Proofs.Claims.Spec2Claims.Claim13bModel_vote_time
import Proofs.Claims.Spec2Claims.Claim13bModel_support_cutoff
import Proofs.Claims.Spec2Claims.Claim13bModel_view_freeze

/-!
# Slot instants

The instants of a slot in order, from its proposal instant to its confirmation instant.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

section SlotInstants

/-- `proposal_time (s + 1) = proposal_time s + 4Δ`. -/
theorem proposal_time_succ_l55 (E : Env V) (s : Slot) :
    Protocol.proposal_time E (s + 1) = Protocol.proposal_time E s + 4 * E.Δ :=
  proposal_time_succ E s

/-- The instants of slot `s` as offsets from `proposal_time s`: `vote_time s` at `Δ`,
    `support_cutoff s` at `2Δ`, `view_freeze s` at `3Δ`, `proposal_time (s + 1)` at `4Δ`,
    `vote_time (s + 1)` at `5Δ`, and `confirmation_time s` at `6Δ`. -/
theorem slot_instants_l55 (E : Env V) (s : Slot) :
    Protocol.vote_time E s = Protocol.proposal_time E s + E.Δ ∧
      Protocol.support_cutoff E s = Protocol.proposal_time E s + 2 * E.Δ ∧
      Protocol.view_freeze E s = Protocol.proposal_time E s + 3 * E.Δ ∧
      Protocol.proposal_time E (s + 1) = Protocol.proposal_time E s + 4 * E.Δ ∧
      Protocol.vote_time E (s + 1) = Protocol.proposal_time E s + 5 * E.Δ ∧
      Protocol.confirmation_time E s = Protocol.proposal_time E s + 6 * E.Δ := by
  have hv : ∀ s' : Slot, Protocol.vote_time E s' = Protocol.proposal_time E s' + E.Δ :=
    fun s' => by rw [← slotStart_add_delta_eq_vote_time, slotStart_eq_proposal_time]
  have h4 := proposal_time_succ_l55 E s
  refine ⟨hv s, ?_, (proposal_time_add_three_delta_eq_view_freeze E s).symm, h4, ?_,
    (proposal_time_add_six_delta E s).symm⟩
  · rw [← slotStart_add_two_delta_eq_support_cutoff, slotStart_eq_proposal_time]
  · rw [hv, h4]
    ring

end SlotInstants


end DecoupledConsensusModel.Sts
