import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedRecordReadersUpTo
import Proofs.Claims.Spec2Claims.ClaimAsyncK_HandoverCovers
import Proofs.Claims.Spec2Claims.ClaimAsyncK_Defs
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_compatible

/-!
# Slot and round arithmetic

Facts over `Nat` on slots `R` apart, and on the round whose slots contain a given slot.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
variable {V : Type} [DecidableEq V] [Fintype V]

open Framework.StsMultisetLog

/-- Over `Nat`, if `a = b + R` and `3 ≤ R`, then `a + 1 − 2 = b + (R − 1)`. -/
theorem nat_add_one_sub_two_l9 (a b R : Nat) (h : a = b + R) (hR : 3 ≤ R) :
    a + 1 - 2 = b + (R - 1) := by omega

/-- Over `Nat`, if `a = b + R`, `c ≤ b` and `3 ≤ R`, then `c + 2 ≤ a + 1`. -/
theorem nat_add_two_le_l9 (a b c R : Nat) (h : a = b + R) (h0 : c ≤ b) (hR : 3 ≤ R) :
    c + 2 ≤ a + 1 := by omega

/-- Over `Nat`, if `3 ≤ R`, `ρ R ≤ (r + 1) R + 1` and `(r + 1) R + 1 ≤ (ρ + 1) R`, then `ρ = r + 1`. -/
theorem nat_eq_succ_of_mul_bounds_l9 (r ρ R : Nat) (hR : 3 ≤ R) (h0 : ρ * R ≤ (r + 1) * R + 1)
    (h1 : (r + 1) * R + 1 ≤ (ρ + 1) * R) : ρ = r + 1 := by
  rcases Nat.lt_trichotomy ρ (r + 1) with h | h | h
  · have := Nat.mul_le_mul_right R (show ρ + 1 ≤ r + 1 by omega)
    omega
  · exact h
  · have := Nat.mul_le_mul_right R (show r + 2 ≤ ρ by omega)
    have h2 : (r + 2) * R = (r + 1) * R + R := by ring
    omega

end DecoupledConsensusModel.Sts
