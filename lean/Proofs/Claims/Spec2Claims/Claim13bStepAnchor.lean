import Proofs.Claims.Spec2Claims.Claim13bInvariantActive
import Proofs.Claims.Spec2Claims.Claim13bModel_derive_named
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAttestation_erase
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_attestations
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_parent
import Proofs.Claims.Spec2Claims.Claim13bModel_author
import Proofs.Claims.Spec2Claims.Claim13bModel_matchesEntry
import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
import Proofs.Claims.Spec2Claims.Claim13bModel_Env_q
import Proofs.Claims.Spec2Claims.Claim13bModel_actionStoreAt
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedStore_initial_stamp
import Proofs.Vocabulary.ModelProperties.NamedReceipt_processed
import Proofs.Vocabulary.ModelProperties.NamedDuties_update_confirmation_with
import Proofs.Vocabulary.ModelProperties.Store_toHealing
import Proofs.Vocabulary.ModelProperties.confirmationReadFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_early_mk

/-!
# Round openings are monotone

A later round opens at a later instant.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- For `r ≤ r'`, round `r` opens at or before round `r'`. -/
theorem opening_mono (S : Setup V) {r r' : Round} (h : r ≤ r') :
    Protocol.opening S.E S.hc r ≤ Protocol.opening S.E S.hc r' := by
  rw [opening_eq_slotStart S r, opening_eq_slotStart S r']
  exact slotStart_mono S (opening_slot_le_of_le_round_of_inclRelay S.hc
    (h.trans (le_round_of_of_opening_slot_le_inclRelay S.hc (le_refl _))))

end DecoupledConsensusModel.Sts
