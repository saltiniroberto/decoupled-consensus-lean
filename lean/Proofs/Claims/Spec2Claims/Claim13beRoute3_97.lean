import Proofs.Claims.Spec2Claims.Claim13beRoute3_95
import Proofs.Claims.Spec2Claims.Claim13beRoute3_96

/-!
# Round arithmetic for three successive windows

Facts over `Nat` on the rounds of three successive windows, each placing a window's rounds inside
the rounds up to `W`.
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

/-- Round arithmetic for the first window: if `d + 2 ≤ w ≤ r₀ ≤ rs`, `rs + (3g + m − 5) ≤ W` and
    `2 ≤ m`, then `d ≤ rs − 1 ≤ W`, `rs + 1 − 2 = rs − 1` over `Int`, and `g − 1 ≤ 3g + m − 5` over
    `Int`. -/
theorem nat_firstSharp_f7 (d w r₀ rs g m W : Nat) (h1 : d + 2 ≤ w) (h2 : w ≤ r₀) (h3 : r₀ ≤ rs)
    (hW : rs + (3 * g + m - 5) ≤ W) (hm : 2 ≤ m) :
    d ≤ rs - 1 ∧ rs - 1 ≤ W ∧ ((rs - 1 : Nat) : Int) = ((rs + 1 : Nat) : Int) - 2 ∧
      (g : Int) - 1 ≤ ((3 * g + m - 5 : Nat) : Int) := by
  omega

/-- Round arithmetic for the second window: if `d + 2 ≤ w ≤ r₀ ≤ rs`, `rs + (3g + m − 5) ≤ W`,
    `2 ≤ m`, `rs + 1 + 1 ≤ c₁` and `c₁ + 2 ≤ rs + 1 + g`, then `3 ≤ g`, `r₀ + 2 ≤ c₁`,
    `rs + 2 ≤ c₁`, `rs + 1 ≤ W` and `c₁ + m + g ≤ W + 2`. -/
theorem nat_secondSharp_f7 (d w r₀ rs g m W c₁ : Nat) (h1 : d + 2 ≤ w) (h2 : w ≤ r₀)
    (h3 : r₀ ≤ rs) (hW : rs + (3 * g + m - 5) ≤ W) (hm : 2 ≤ m) (hlo : rs + 1 + 1 ≤ c₁)
    (hhi : c₁ + 2 ≤ rs + 1 + g) :
    3 ≤ g ∧ r₀ + 2 ≤ c₁ ∧ rs + 2 ≤ c₁ ∧ rs + 1 ≤ W ∧ c₁ + m + g ≤ W + 2 := by
  omega

/-- Round arithmetic for the window after a timeout: if `d + 2 ≤ w ≤ r₀`, `2 ≤ m`, `3 ≤ g`,
    `r₀ + 2 ≤ c₁` and `c₁ + m + g ≤ W + 2`, then `r₀ ≤ c₁`, `c₁ + 1 ≤ W`, `d + 2 ≤ c₁ + m − 1`,
    `c₁ + m − 1 + g ≤ W + 1`, and every `c₂` with `c₁ + m − 1 + 1 ≤ c₂` and
    `c₂ + 2 ≤ c₁ + m − 1 + g` has `c₁ + m ≤ c₂`, `c₂ ≤ c₁ + m + g`, `c₂ + 1 ≤ W` and
    `c₂ + 3 ≤ c₁ + m + g`. -/
theorem nat_afterTimeoutSharp_f7 (d w r₀ c₁ g m W : Nat) (h1 : d + 2 ≤ w) (h2 : w ≤ r₀)
    (hm : 2 ≤ m) (hg : 3 ≤ g) (hc : r₀ + 2 ≤ c₁) (hW : c₁ + m + g ≤ W + 2) :
    r₀ ≤ c₁ ∧ c₁ + 1 ≤ W ∧ d + 2 ≤ c₁ + m - 1 ∧ c₁ + m - 1 + g ≤ W + 1 ∧
      ∀ c₂ : Nat, c₁ + m - 1 + 1 ≤ c₂ → c₂ + 2 ≤ c₁ + m - 1 + g →
        c₁ + m ≤ c₂ ∧ c₂ ≤ c₁ + m + g ∧ c₂ + 1 ≤ W ∧ c₂ + 3 ≤ c₁ + m + g := by
  refine ⟨by omega, by omega, by omega, by omega, fun c₂ hlo hhi => ⟨by omega, by omega,
    by omega, by omega⟩⟩

/-- If `2 ≤ m` and `3 ≤ g`, then `c₁ + 3 ≤ c₁ + m + g`. -/
theorem nat_clearSharp_f7 (c₁ g m : Nat) (hm : 2 ≤ m) (hg : 3 ≤ g) : c₁ + 3 ≤ c₁ + m + g := by
  omega

/-- Round arithmetic for the third window: if `d + 2 ≤ w ≤ r₀`, `rs + (3g + m − 5) ≤ W`, `2 ≤ m`,
    `3 ≤ g`, `r₀ + 2 ≤ c₁`, `c₁ + 2 ≤ rs + 1 + g`, `c₁ ≤ c₂` and `c₂ + 3 ≤ c₁ + m + g`, then
    `d + 2 ≤ c₂`, `c₂ + g ≤ W + 1`, `r₀ ≤ c₂`, and every `c₃` with `c₂ + 1 ≤ c₃` and
    `c₃ + 2 ≤ c₂ + g` has `c₃ + 1 ≤ W`, `c₃ ≤ rs + (3g + m − 6)` and `d + 2 ≤ c₃`. -/
theorem nat_thirdSharp_f7 (d w r₀ rs g m W c₁ c₂ : Nat) (h1 : d + 2 ≤ w) (h2 : w ≤ r₀)
    (hW : rs + (3 * g + m - 5) ≤ W) (hm : 2 ≤ m) (hg : 3 ≤ g) (hc₁lo : r₀ + 2 ≤ c₁)
    (hc₁ : c₁ + 2 ≤ rs + 1 + g) (hc₁₂ : c₁ ≤ c₂) (hc₂ : c₂ + 3 ≤ c₁ + m + g) :
    d + 2 ≤ c₂ ∧ c₂ + g ≤ W + 1 ∧ r₀ ≤ c₂ ∧
      ∀ c₃ : Nat, c₂ + 1 ≤ c₃ → c₃ + 2 ≤ c₂ + g →
        c₃ + 1 ≤ W ∧ c₃ ≤ rs + (3 * g + m - 6) ∧ d + 2 ≤ c₃ := by
  refine ⟨by omega, by omega, by omega, fun c₃ hlo hhi => ⟨by omega, by omega, by omega⟩⟩

end Arithmetic

section SecondWindow

/-- An index into an sts execution is always valid, so `get_elem_tactic` is answered by
    `True.intro`. -/
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

end SecondWindow

section Assembly

/-- An index into an sts execution is always valid, so `get_elem_tactic` is answered by
    `True.intro`. -/
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

end Assembly

end DecoupledConsensusModel.Sts
