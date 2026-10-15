import Proofs.Claims.Spec2Claims.Claim13bModel_deepest_clear
import Proofs.Claims.Spec2Claims.Claim13bModel_floor_on_stable_incl
import Proofs.Claims.Spec2Claims.Claim13bModel_update_confirmation_with_incl
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeBool_cs
import Proofs.Claims.Spec2Claims.Claim13bModel_frameStableRoot_cs
import Proofs.Claims.Spec2Claims.Claim13bK_StableRecord
import Proofs.Claims.Spec2Claims.Claim13bK_ProposalVotesWalk
import Proofs.Claims.Spec2Claims.ClaimAsyncK_GstShift

/-!
# Slot arithmetic at the hand-over

One fact over `Nat` on slots `R` apart.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

section AtHandover

open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If `a ≤ o₁ + 1`, `o₂ = o₁ + R`, `3 ≤ R` and `o₂ ≤ o`, then `a + 2 ≤ o`. -/
theorem slot_gap_add_two (a o₁ o₂ o R : Nat) (h1 : a ≤ o₁ + 1) (h2 : o₂ = o₁ + R) (hR : 3 ≤ R)
    (h3 : o₂ ≤ o) : a + 2 ≤ o := by
  omega

end AtHandover

end DecoupledConsensusModel.Sts
