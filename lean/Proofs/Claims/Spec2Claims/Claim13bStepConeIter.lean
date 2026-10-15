import Proofs.Claims.Spec2Claims.Claim13bStepSG
import Proofs.Claims.Spec2Claims.Claim13bStepCone
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmation_time
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG1
import Proofs.Claims.Spec2Claims.Claim13bModel_update_confirmation_with_phase

/-!
# Round openings after round zero

Every round after round `0` opens at a slot after slot `0`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every round after round `0` opens at a slot after slot `0`. -/
theorem opening_slot_pos (S : Setup V) {r : Round} (hr : 0 < r) :
    0 < S.hc.opening_slot r :=
  opening_slot_pos_of_round_pos_inclRelay S.hc hr

end DecoupledConsensusModel.Sts
