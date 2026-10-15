import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot

/-!
# Facts about `Protocol.HealConfig.round_of`

Lemmas that unfold the round of a slot, against the opening slot of a round.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.HealConfig.round_of

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

/-- The opening slot of the round of `s` is at most `s`. -/
theorem opening_slot_round_of_le_slot (hc : Protocol.HealConfig) (s : Slot) :
    hc.opening_slot (hc.round_of s) ≤ s := by
  rw [opening_slot_closed]
  unfold Protocol.HealConfig.round_of
  exact Nat.div_mul_le_self s hc.R

/-- `s` is strictly less than the opening slot of the round after the round of `s`. -/
theorem lt_opening_slot_round_of_succ (hc : Protocol.HealConfig) (s : Slot) :
    s < hc.opening_slot (hc.round_of s + 1) := by
  rw [opening_slot_closed]
  unfold Protocol.HealConfig.round_of
  have hR : 0 < hc.R := lt_of_lt_of_le (by decide) hc.R_ge_three
  rw [Nat.succ_mul]
  exact Nat.lt_div_mul_add hR

/-- If the opening slot of round `r` is at most slot `s`, then `r` is at most the round of `s`. -/
theorem le_round_of_of_opening_slot_le (hc : Protocol.HealConfig) {r : Round} {s : Slot}
    (h : hc.opening_slot r ≤ s) : r ≤ hc.round_of s := by
  rw [opening_slot_closed] at h
  unfold Protocol.HealConfig.round_of
  have hR : 0 < hc.R := lt_of_lt_of_le (by decide) hc.R_ge_three
  exact (Nat.le_div_iff_mul_le hR).mpr h

/-- If `s ≤ s'`, the round of `s` is at most the round of `s'`. -/
theorem round_of_mono (hc : Protocol.HealConfig) {s s' : Slot} (h : s ≤ s') :
    hc.round_of s ≤ hc.round_of s' := by
  unfold Protocol.HealConfig.round_of
  exact Nat.div_le_div_right h

/-- If `r` is at most the round of slot `s`, then the opening slot of `r` is at most `s`. -/
theorem opening_slot_le_of_le_round_of (hc : Protocol.HealConfig) {r : Round} {s : Slot}
    (h : r ≤ hc.round_of s) : hc.opening_slot r ≤ s := by
  rw [opening_slot_closed]
  unfold Protocol.HealConfig.round_of at h
  have hR : 0 < hc.R := lt_of_lt_of_le (by decide) hc.R_ge_three
  exact (Nat.le_div_iff_mul_le hR).mp h

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

/-- If `j < R`, the slot `j` places after round `ρ`'s opening slot is in round `ρ`. -/
theorem round_of_opening_slot_add (hc : Protocol.HealConfig) (ρ : Round) {j : Nat}
    (hj : j < hc.R) : hc.round_of (hc.opening_slot ρ + j) = ρ := by
  rw [opening_slot_closed]
  unfold Protocol.HealConfig.round_of
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < hc.R), Nat.div_eq_of_lt hj,
    Nat.zero_add]

end DecoupledConsensusModel.Sts
