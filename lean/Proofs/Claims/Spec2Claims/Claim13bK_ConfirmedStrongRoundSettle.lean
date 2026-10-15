import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedAgree
import Proofs.Claims.Spec2Claims.Claim13bK_JointBase
import Proofs.Claims.Spec2Claims.Claim13beRoute3_85f
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedSettleEarlier
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq

/-!
# Round arithmetic over `Nat`

Four arithmetic facts over `Nat` used for round and slot bounds.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

variable {V : Type} [DecidableEq V] [Fintype V]

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Over `Nat`, `a + 2 ≤ b`, `b + 1 ≤ d` and `d ≤ c − 2` give `a + 3 ≤ c`. -/
theorem nat_add_three_le_c7 {a b d c : Nat} (h1 : a + 2 ≤ b) (h2 : b + 1 ≤ d) (h3 : d ≤ c - 2) :
    a + 3 ≤ c := by omega

/-- Over `Nat`, `a + 3 ≤ r` gives `1 ≤ r − 1` and `r − 1 + 1 = r`. -/
theorem nat_sub_one_c7 {a r : Nat} (h : a + 3 ≤ r) : 1 ≤ r - 1 ∧ r - 1 + 1 = r := by omega

/-- Over `Nat`, `a < b`, `b ≤ c` and `c ≤ a` are contradictory. -/
theorem nat_lt_le_le_absurd_c7 {a b c : Nat} (h1 : a < b) (h2 : b ≤ c) (h3 : c ≤ a) : False := by
  omega

/-- Over `Nat`, `b ≤ s + 1`, `a + R ≤ b`, `s ≤ a` and `3 ≤ R` are contradictory. -/
theorem nat_round_hi_absurd_c7 {a b s R : Nat} (h1 : b ≤ s + 1) (h2 : a + R ≤ b) (h3 : s ≤ a)
    (hR : 3 ≤ R) : False := by omega

end DecoupledConsensusModel.Sts
