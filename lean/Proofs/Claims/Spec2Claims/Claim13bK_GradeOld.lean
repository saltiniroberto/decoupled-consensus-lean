import Proofs.Claims.Spec2Claims.Claim13bStepPairwise
import Proofs.Claims.Spec2Claims.Claim13bKit
import Proofs.Claims.Spec2Claims.Claim13bStepFin
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAttestation_erase
import Proofs.Claims.Spec2Claims.Claim13bModel_rawView
import Proofs.Claims.Spec2Claims.Claim13bModel_a

/-!
# Consecutive action instants

Round `r + 1`'s action instant is `4 * S.hc.R * S.E.Δ` after round `r`'s.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Round `r + 1`'s action instant is `4 * S.hc.R * S.E.Δ` after round `r`'s. -/
theorem action_succ_eq_add_rounds (S : Setup V) (r : Round) :
    S.a (r + 1) = S.a r + 4 * (S.hc.R : Int) * S.E.Δ := by
  unfold Setup.a
  rw [healA_succ_round]
  ring

end DecoupledConsensusModel.Sts
