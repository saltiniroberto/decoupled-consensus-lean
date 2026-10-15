import Model.Sts.Spec2Claims.ClaimConfirmedIncludedAfterHealing
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedWake
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time_inclG1
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedStrongRoundSettle

/-!
# The phase end is positive

If `tGAT + tHeal ≤ tE`, `S.E.t_GST ≤ tGAT` and `0 < tHeal`, then `0 < tE`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If `tGAT + tHeal ≤ tE`, `S.E.t_GST ≤ tGAT` and `0 < tHeal`, then `0 < tE`. -/
theorem pos_of_phase (S : Setup V) {tGAT tHeal tE : Int} (hlen : tGAT + tHeal ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT) (hpos : 0 < tHeal) : 0 < tE := by
  have h0 := S.E.t_GST_nonneg
  linarith

end DecoupledConsensusModel.Sts
