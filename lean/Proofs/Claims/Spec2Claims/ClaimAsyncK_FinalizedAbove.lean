import Proofs.Claims.Spec2Claims.Claim13beRoute3_97
import Model.Sts.Spec2Claims.ClaimStableThroughAsyncPeriod
import Proofs.Claims.Spec2Claims.Claim13bModel_author
import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot
import Proofs.Claims.Spec2Claims.Claim13bModel_slotStart
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmation_time

/-!
# Round and height arithmetic for three successive windows

Facts over `Nat` on the rounds of the windows `q₀`, `c₁` and `c₂` before `W`, and one fact on
heights.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Round arithmetic -/

section Arithmetic

/-- Round arithmetic before the first window: if `d + 2 ≤ w` and `w + (3g + m) ≤ W`, then `w ≠ 0`
    and `w + g ≤ W + 1`. -/
theorem nat_switch_fa (d w W g m : Nat) (h1 : d + 2 ≤ w) (h2 : w + (3 * g + m) ≤ W) :
    w ≠ 0 ∧ w + g ≤ W + 1 := by
  omega

/-- Round arithmetic for the window `q₀`: if `d + 2 ≤ w`, `w + (3g + m) ≤ W`, `w + 1 ≤ q₀` and
    `q₀ + 2 ≤ w + g`, then `3 ≤ g`, `d + 2 ≤ q₀`, `q₀ ≤ W` and `q₀ + g ≤ W + 1`. -/
theorem nat_firstWindow_fa (d w W q₀ g m : Nat) (h1 : d + 2 ≤ w) (h2 : w + (3 * g + m) ≤ W)
    (h3 : w + 1 ≤ q₀) (h4 : q₀ + 2 ≤ w + g) :
    3 ≤ g ∧ d + 2 ≤ q₀ ∧ q₀ ≤ W ∧ q₀ + g ≤ W + 1 := by
  omega

/-- Round arithmetic for the window `c₁`: if `w + (3g + m) ≤ W`, `w + 1 ≤ q₀`, `q₀ + 2 ≤ w + g`,
    `q₀ + 1 ≤ c₁` and `c₁ + 2 ≤ q₀ + g`, then `w + 2 ≤ c₁`, `q₀ ≤ c₁ − 1` and `c₁ + m + g ≤ W + 2`. -/
theorem nat_secondWindow_fa (w W q₀ c₁ g m : Nat) (h2 : w + (3 * g + m) ≤ W) (h3 : w + 1 ≤ q₀)
    (h4 : q₀ + 2 ≤ w + g) (h5 : q₀ + 1 ≤ c₁) (h6 : c₁ + 2 ≤ q₀ + g) :
    w + 2 ≤ c₁ ∧ q₀ ≤ c₁ - 1 ∧ c₁ + m + g ≤ W + 2 := by
  omega

/-- Round arithmetic for the window `c₂`: if `d + 2 ≤ w`, `w + (3g + m) ≤ W`, `w + 1 ≤ q₀`,
    `q₀ + 2 ≤ w + g`, `q₀ + 1 ≤ c₁`, `c₁ + 2 ≤ q₀ + g`, `c₁ ≤ c₂` and `c₂ + 3 ≤ c₁ + m + g`, then
    `d + 2 ≤ c₂`, `w + 2 ≤ c₂`, `c₂ + 1 ≤ W` and
    `c₂ + (3g + m − 6 + 1) ≤ w + (2g + m + 3) + (3g + m) + (3g + m − 6 + 1)`. -/
theorem nat_thirdWindow_fa (d w W q₀ c₁ c₂ g m : Nat) (h1 : d + 2 ≤ w)
    (h2 : w + (3 * g + m) ≤ W) (h3 : w + 1 ≤ q₀) (h4 : q₀ + 2 ≤ w + g) (h5 : q₀ + 1 ≤ c₁)
    (h6 : c₁ + 2 ≤ q₀ + g) (h7 : c₁ ≤ c₂) (h8 : c₂ + 3 ≤ c₁ + m + g) :
    d + 2 ≤ c₂ ∧ w + 2 ≤ c₂ ∧ c₂ + 1 ≤ W ∧
      c₂ + (3 * g + m - 6 + 1) ≤ w + (2 * g + m + 3) + (3 * g + m) + (3 * g + m - 6 + 1) := by
  omega

/-- If `a ≤ b + 1`, `b ≤ c`, `c < d` and `d < e` over `Nat`, then `a < e`. -/
theorem nat_heights_fa (a b c d e : Nat) (h1 : a ≤ b + 1) (h2 : b ≤ c) (h3 : c < d) (h4 : d < e) :
    a < e := by
  omega

end Arithmetic

end DecoupledConsensusModel.Sts
