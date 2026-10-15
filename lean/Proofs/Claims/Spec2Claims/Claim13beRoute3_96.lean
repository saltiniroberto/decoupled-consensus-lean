import Proofs.Claims.Spec2Claims.Claim13beRoute3_85f

/-!
# Round arithmetic for the strong-opening recurrence

The inequalities over `Nat` used to read the recurrence of strong openings at its sharp spacing.
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

/-- If not `c + 2 ≤ a + g`, then `a + g + 1 ≤ c + 2`. -/
theorem nat_sharpUpper_f7 (a g c : Nat) (h : ¬ c + 2 ≤ a + g) : a + g + 1 ≤ c + 2 := by
  omega

/-- If `1 ≤ j ≤ 2` and `1 ≤ c`, then `c − 2 ≤ c − j` and `c − j + 1 ≤ c`, with `c − j` taken over
    `Nat` and cast to `Int`. -/
theorem nat_prevOpenings_f7 (c j : Nat) (hj1 : 1 ≤ j) (hj2 : j ≤ 2) (hc : 1 ≤ c) :
    (c : Int) - 2 ≤ ((c - j : Nat) : Int) ∧ ((c - j : Nat) : Int) + 1 ≤ (c : Int) := by
  omega

/-- If `d + 2 ≤ a` and `a + g ≤ w + 1`, then `d ≤ a − 2`, `a − 2 + g ≤ w`, `d ≤ a − 1`,
    `a − 1 + g ≤ w`, and the casts of `a − 2` and `a − 1` are the integer differences. -/
theorem nat_sharpRounds_f7 (d a g w : Nat) (ha : d + 2 ≤ a) (hag : a + g ≤ w + 1) :
    d ≤ a - 2 ∧ a - 2 + g ≤ w ∧ d ≤ a - 1 ∧ a - 1 + g ≤ w ∧
      ((a - 2 : Nat) : Int) = (a : Int) - 2 ∧ ((a - 1 : Nat) : Int) = (a : Int) - 1 := by
  omega

end DecoupledConsensusModel.Sts
