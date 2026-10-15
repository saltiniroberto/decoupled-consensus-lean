import Proofs.Claims.Spec2Claims.ClaimAsyncK_HandoverRootsUpTo
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq

/-!
# Slot arithmetic

One fact over `Nat` on slots `R` apart.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Over `Nat`, if `a = b + R` and `3 ≤ R`, then `a − 2 = b + (R − 2)`. -/
theorem nat_sub_two_l9 (a b R : Nat) (h : a = b + R) (hR : 3 ≤ R) : a - 2 = b + (R - 2) := by
  omega

end DecoupledConsensusModel.Sts
