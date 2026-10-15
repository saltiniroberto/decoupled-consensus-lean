import Proofs.Claims.Spec2Claims.Claim13beRoute3_94
import Proofs.Claims.Spec2Claims.Claim13bK_FinalityStepWindow

/-!
# Round and slot arithmetic for three windows

The round and slot inequalities over `Nat` that place three windows of rounds before the round `W`.
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

section Arithmetic

/-- If `d' ≤ w ≤ r₀` and `r₀ + 2 ≤ c`, then `d' + 1 ≤ c`. -/
theorem nat_anchorRound_f2d (d' w r₀ c : Nat) (h1 : d' ≤ w) (h2 : w ≤ r₀) (h3 : r₀ + 2 ≤ c) :
    d' + 1 ≤ c := by
  omega

/-- If `s < (rs + 1)·R`, `(rs + 1)·R ≤ W·R` and `rs + 1 ≤ W`, then `s ≤ W·R + 2` and `W ≠ 0`. -/
theorem nat_slotBound_f2d (s R rs W : Nat) (hslt : s < (rs + 1) * R)
    (h2 : (rs + 1) * R ≤ W * R) (h3 : rs + 1 ≤ W) : s ≤ W * R + 2 ∧ W ≠ 0 := by
  omega

/-- If `d + 2 ≤ w ≤ r₀ ≤ c₂`, `c₂ + 1 ≤ c₃` and `c₃ + 1 ≤ W`, then the listed bounds on `c₂`, `c₃`
    and `W` hold. -/
theorem nat_thirdParent_f2d (d w r₀ c₂ c₃ W : Nat) (h1 : d + 2 ≤ w) (h2 : w ≤ r₀) (h3 : r₀ ≤ c₂)
    (h4 : c₂ + 1 ≤ c₃) (h5 : c₃ + 1 ≤ W) :
    d + 1 ≤ c₂ ∧ d + 2 ≤ c₃ ∧ w ≤ c₃ - 1 ∧ 1 ≤ c₃ ∧ c₂ ≤ c₃ - 1 ∧ c₂ + 1 ≤ W ∧ c₂ ≤ W ∧
      W ≠ 0 := by
  omega

end Arithmetic

section SecondWindow

/-- Every index into an sts execution is valid, so `get_elem_tactic` is answered by `True.intro`. -/
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

end SecondWindow

section ThirdWindow

/-- Every index into an sts execution is valid, so `get_elem_tactic` is answered by `True.intro`. -/
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

end ThirdWindow

section Assembly

/-- Every index into an sts execution is valid, so `get_elem_tactic` is answered by `True.intro`. -/
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

end Assembly

end DecoupledConsensusModel.Sts
