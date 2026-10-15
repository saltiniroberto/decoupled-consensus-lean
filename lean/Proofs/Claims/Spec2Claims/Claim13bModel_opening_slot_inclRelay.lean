module
public import Model.Vocabulary.Protocol.Grades
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.HealConfig.opening_slot` against `round_of`, as a module file

The opening slot of a round compared with the round of a slot.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.HealConfig.opening_slot
  DecoupledConsensusModel.Protocol.HealConfig.round_of

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

/-- If the round `r` is positive, its opening slot is positive. -/
theorem opening_slot_pos_of_round_pos_inclRelay (hc : Protocol.HealConfig) {r : Round}
    (h : 0 < r) : 0 < hc.opening_slot r := by
  unfold Protocol.HealConfig.opening_slot
  exact Nat.mul_pos h (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hc.R_ge_three)

/-- If the opening slot of round `r` is at most slot `s`, then `r` is at most the round of `s`. -/
theorem le_round_of_of_opening_slot_le_inclRelay (hc : Protocol.HealConfig) {r : Round}
    {s : Slot} (h : hc.opening_slot r ≤ s) : r ≤ hc.round_of s := by
  unfold Protocol.HealConfig.opening_slot at h
  unfold Protocol.HealConfig.round_of
  have hR : 0 < hc.R := lt_of_lt_of_le (by decide) hc.R_ge_three
  exact (Nat.le_div_iff_mul_le hR).mpr h

/-- If `r` is at most the round of slot `s`, then the opening slot of `r` is at most `s`. -/
theorem opening_slot_le_of_le_round_of_inclRelay (hc : Protocol.HealConfig) {r : Round}
    {s : Slot} (h : r ≤ hc.round_of s) : hc.opening_slot r ≤ s := by
  unfold Protocol.HealConfig.opening_slot
  unfold Protocol.HealConfig.round_of at h
  have hR : 0 < hc.R := lt_of_lt_of_le (by decide) hc.R_ge_three
  exact (Nat.le_div_iff_mul_le hR).mp h

end DecoupledConsensusModel.Sts
