import Proofs.Claims.Spec2Claims.Claim13beRoute3_56
import Proofs.Vocabulary.Protocol.Grades.GSTZeroSelectionSafety
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_compatible
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmationReadFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_incl
import Proofs.Claims.Spec2Claims.Claim13bModel_toHealing
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeContract_inclG1
import Proofs.Claims.Spec2Claims.Claim13bModel_get_head_in_tree_with_layer
import Proofs.Claims.Spec2Claims.Claim13bModel_get_head_with
import Proofs.Claims.Spec2Claims.Claim13bModel_voter_filtered_block_tree
import Proofs.Claims.Spec2Claims.Claim13bModel_get_filtered_block_tree_from
import Proofs.Claims.Spec2Claims.Claim13bModel_get_fg_root
import Proofs.Claims.Spec2Claims.Claim13bModel_get_filtered_block_tree
import Proofs.Claims.Spec2Claims.Claim13bModel_voter_processed_block_tree
import Proofs.Claims.Spec2Claims.Claim13bModel_goldfish_fork_choice
import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot

/-!
# Opening slots of a positive round

The opening slot of a positive round, and the slot before it, are positive.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

section Helpers

/-- If `0 < q`, then `0 < opening_slot q`. -/
theorem openingSlot_pos_l58 (S : Setup V) {q : Round} (hq : 0 < q) :
    0 < S.hc.opening_slot q :=
  opening_slot_pos_of_round_pos S.hc hq

/-- If `0 < q`, then `0 < opening_slot q − 1`. -/
theorem openingSlot_pred_pos_l58 (S : Setup V) {q : Round} (hq : 0 < q) :
    0 < S.hc.opening_slot q - 1 := by
  rw [opening_slot_closed]
  have hR : 2 ≤ S.hc.R := S.hc.R_ge_two
  have hqOne : 1 ≤ q := Nat.succ_le_iff.mpr hq
  have hopenTwo : 2 ≤ q * S.hc.R := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul hqOne hR
  exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_sub_of_add_le hopenTwo)

end Helpers

end DecoupledConsensusModel.Sts
