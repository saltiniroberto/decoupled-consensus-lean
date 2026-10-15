import Model.Vocabulary.Protocol.Grades
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.HealConfig.opening_slot`

Lemmas that unfold a round's opening slot.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.HealConfig.opening_slot

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

/-- The opening slot of round `r` is `r * R`. -/
theorem opening_slot_closed (hc : Protocol.HealConfig) (r : Round) :
    hc.opening_slot r = r * hc.R := rfl

/-- If `r ≤ r'`, the opening slot of round `r` is at most that of round `r'`. -/
theorem opening_slot_le_of_le (hc : Protocol.HealConfig) {r r' : Round} (h : r ≤ r') :
    hc.opening_slot r ≤ hc.opening_slot r' :=
  Nat.mul_le_mul_right _ h

/-- The opening slot of round `r + 1` is the opening slot of round `r` plus `R`. -/
theorem opening_slot_succ (hc : Protocol.HealConfig) (r : Round) :
    hc.opening_slot (r + 1) = hc.opening_slot r + hc.R :=
  Nat.succ_mul r hc.R

/-- If the round `r` is positive, its opening slot is positive. -/
theorem opening_slot_pos_of_round_pos (hc : Protocol.HealConfig) {r : Round} (h : 0 < r) :
    0 < hc.opening_slot r :=
  Nat.mul_pos h (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hc.R_ge_three)

/-- The opening slot of round `r + k` is the opening slot of round `r` plus `k * R`. -/
theorem opening_slot_add (hc : Protocol.HealConfig) (r k : Round) :
    hc.opening_slot (r + k) = hc.opening_slot r + k * hc.R :=
  Nat.add_mul r k hc.R

end DecoupledConsensusModel.Sts
