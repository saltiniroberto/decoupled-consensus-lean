import Proofs.Claims.Spec2Claims.Claim13beRoute3_86d
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_opening
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmationReadFrom
import Proofs.Claims.Spec2Claims.Claim13bSGCompatible
import Proofs.Claims.Spec2Claims.Claim13bModel_round_of
import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot
import Proofs.Claims.Spec2Claims.Claim13bModel_support_cutoff
import Proofs.Claims.Spec2Claims.Claim13bModel_vote_time
import Proofs.Claims.Spec2Claims.Claim13bModel_view_freeze
import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
import Proofs.Claims.Spec2Claims.Claim13bModel_toHealing
import Proofs.Claims.Spec2Claims.Claim13bModel_voter_filtered_block_tree
import Proofs.Claims.Spec2Claims.Claim13bModel_domain
import Proofs.Claims.Spec2Claims.Claim13bModel_voter_processed_block_tree
import Proofs.Claims.Spec2Claims.Claim13bModel_anchor
import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot_mk
import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot_inclRelay
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq

/-!
# Slots within a round

A round's first interior slot is before the next opening slot, and every slot lies between its
round's opening slot and the next one.
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

section FirstInteriorHead

/-- `opening_slot r + 1 < opening_slot (r + 1)`. -/
theorem firstInterior_lt_nextOpening_l86e (S : Setup V) (r : Round) :
    S.hc.opening_slot r + 1 < S.hc.opening_slot (r + 1) := by
  rw [opening_slot_succ_mk]
  exact Nat.add_lt_add_left (Nat.lt_of_succ_le S.hc.R_ge_two) _

end FirstInteriorHead

section SGBlockBound

/-- `opening_slot (round_of s) ≤ s < opening_slot (round_of s + 1)`. -/
theorem slot_round_bounds_l86e (S : Setup V) (s : Slot) :
    S.hc.opening_slot (S.hc.round_of s) ≤ s ∧
      s < S.hc.opening_slot (S.hc.round_of s + 1) := by
  refine ⟨opening_slot_le_of_le_round_of_inclRelay S.hc (le_refl _), ?_⟩
  by_contra hns
  have h := le_round_of_of_opening_slot_le_inclRelay S.hc (Nat.le_of_not_lt hns)
  exact absurd h (Nat.not_succ_le_self _)

end SGBlockBound

end DecoupledConsensusModel.Sts
