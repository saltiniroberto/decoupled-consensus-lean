import Proofs.Claims.Spec2Claims.Claim13beRoute3_85d
import Proofs.Claims.Spec2Claims.Claim13beRoute3_85c
import Proofs.Vocabulary.ModelProperties.NamedBlock_parent
import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot
import Proofs.Claims.Spec2Claims.Claim13bModel_vote_time
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmation_time
import Proofs.Claims.Spec2Claims.Claim13bModel_matchesEntry
import Proofs.Claims.Spec2Claims.Claim13bModel_Env_q
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmationReadFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock
import Proofs.Claims.Spec2Claims.Claim13bModel_inWindow
import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot_mk
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time
import Proofs.Claims.Spec2Claims.Claim13bModel_slotStart

/-!
# Round and slot arithmetic for the switch round's windows

Inequalities over `Nat` between rounds, slots, `K` and the timeout delay, used to place two windows
of rounds before the switch round.
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

variable {V : Type} [DecidableEq V] [Fintype V]


section WindowExec

open Framework.StsMultisetLog

/-- If `1 ≤ c`, then `c = (c − 1) + 1`. -/
theorem nat_succ_pred_l85f (c : Nat) (h : 1 ≤ c) : c = (c - 1) + 1 := by omega

/-- If `d + 4 ≤ c`, then `d + 2 ≤ c`, `d + 3 ≤ c`, `1 ≤ c`, `d + 3 ≤ c − 1` and `c − 1 − 1 = c − 2`. -/
theorem nat_window_rounds_l85f (d c : Nat) (h : d + 4 ≤ c) :
    d + 2 ≤ c ∧ d + 3 ≤ c ∧ 1 ≤ c ∧ d + 3 ≤ c - 1 ∧ c - 1 - 1 = c - 2 := by omega

/-- If `d + 3 ≤ c`, then `d + 2 ≤ c − 1`. -/
theorem nat_prev_round_l85f (d c : Nat) (h : d + 3 ≤ c) : d + 2 ≤ c - 1 := by omega

/-- If `p + 1 ≤ o + 2`, `o = o' + R`, `3 ≤ R` and `2R ≤ tD`, then `p + 1 ≤ o' + tD`. -/
theorem nat_slot_budget_l85f (p o o' R tD : Nat) (h1 : p + 1 ≤ o + 2) (h2 : o = o' + R)
    (h3 : 3 ≤ R) (h4 : 2 * R ≤ tD) : p + 1 ≤ o' + tD := by omega

end WindowExec


section Climb

open Framework.StsMultisetLog

/-- If `d + 2 ≤ c`, then `1 ≤ c` and `d ≤ c − 1`. -/
theorem nat_later_round_l85f (d c : Nat) (h : d + 2 ≤ c) : 1 ≤ c ∧ d ≤ c - 1 := by omega

/-- If `c₁ + m ≤ c₂` and `2 ≤ m`, then `c₁ + 1 ≤ c₂ − 1`. -/
theorem nat_gap_rounds_l85f (c₁ c₂ m : Nat) (h : c₁ + m ≤ c₂) (hm : 2 ≤ m) :
    c₁ + 1 ≤ c₂ - 1 := by omega

/-- If `R ∣ tD` and `c₁ + tD / R ≤ c₂`, then `c₁·R + tD ≤ c₂·R`. -/
theorem nat_window_far_l85f (c₁ c₂ R tD : Nat) (hdvd : R ∣ tD) (hlo : c₁ + tD / R ≤ c₂) :
    c₁ * R + tD ≤ c₂ * R := by
  obtain ⟨d, rfl⟩ := hdvd
  rcases Nat.eq_zero_or_pos R with h0 | hpos
  · subst h0; simp
  · rw [Nat.mul_div_cancel_left d hpos] at hlo
    calc c₁ * R + R * d = (c₁ + d) * R := by ring
      _ ≤ c₂ * R := Nat.mul_le_mul_right _ hlo

/-- If `R ∣ tD`, `2R ≤ tD`, `g + 2 ≤ K` and `c₂ ≤ c₁ + tD / R + g`, then
    `c₁·R + 1 + (K − 1)·tD ≤ c₂·R` is impossible. -/
theorem nat_climb_far_l85f (c₁ c₂ R tD K g : Nat) (hdvd : R ∣ tD) (h2 : 2 * R ≤ tD)
    (hK : g + 2 ≤ K) (hhi : c₂ ≤ c₁ + tD / R + g)
    (hsp : c₁ * R + 1 + (K - 1) * tD ≤ c₂ * R) : False := by
  obtain ⟨d, rfl⟩ := hdvd
  rcases Nat.eq_zero_or_pos R with h0 | hpos
  · subst h0; simp at hsp
  · rw [Nat.mul_div_cancel_left d hpos] at hhi
    have h3 : c₂ * R ≤ (c₁ + d + g) * R := Nat.mul_le_mul_right _ hhi
    have hd2 : 2 ≤ d := Nat.le_of_mul_le_mul_left (by rw [Nat.mul_comm]; exact h2) hpos
    have hK1 : g + 1 ≤ K - 1 := by omega
    have h4 : (g + 1) * (R * d) ≤ (K - 1) * (R * d) := Nat.mul_le_mul_right _ hK1
    have h5 : g * R * 2 ≤ g * R * d := Nat.mul_le_mul_left _ hd2
    nlinarith

/-- If `K ∣ a`, `K ∣ b` and `a < b`, then `a + K ≤ b`. -/
theorem nat_dvd_step_l85f (K a b : Nat) (ha : K ∣ a) (hb : K ∣ b) (hab : a < b) : a + K ≤ b := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  have hij : i < j := Nat.lt_of_mul_lt_mul_left hab
  calc K * i + K = K * (i + 1) := by ring
    _ ≤ K * j := Nat.mul_le_mul_left _ hij

/-- If `K ∣ a` and `1 ≤ j < K`, then `K` does not divide `a + j`. -/
theorem nat_not_dvd_add_l85f (K a j : Nat) (ha : K ∣ a) (hj1 : 1 ≤ j) (hjK : j < K) :
    ¬ K ∣ a + j := fun h => by
  have hj := (Nat.dvd_add_right ha).mp h
  exact absurd (Nat.le_of_dvd (by omega) hj) (by omega)

/-- `o₂ < e + tD`, `e ≤ o₁` and `o₁ + tD ≤ o₂` cannot all hold. -/
theorem nat_plateau_far_l85f (o₁ o₂ e tD : Nat) (h1 : o₂ < e + tD) (h2 : e ≤ o₁)
    (h3 : o₁ + tD ≤ o₂) : False := by omega

/-- If `g + 2 ≤ K`, then `1 ≤ K`. -/
theorem nat_one_le_of_l85f (g K : Nat) (h : g + 2 ≤ K) : 1 ≤ K := by omega

end Climb


section Assembly

open Framework.StsMultisetLog

/-- If `d + g + 1 + 3 ≤ c₁`, `c₁ + m ≤ c₂` and `c₂ + 1 ≤ w`, then the listed lower bounds on `c₁`,
    `c₂`, `c₁ − 1` and `c₂ − 1` and upper bounds by `w` hold. -/
theorem nat_assembly_rounds_l85f (d g c₁ c₂ m w : Nat) (h1 : d + g + 1 + 3 ≤ c₁)
    (h2 : c₁ + m ≤ c₂) (h3 : c₂ + 1 ≤ w) :
    d + 4 ≤ c₁ ∧ d + 4 ≤ c₂ ∧ d + 2 ≤ c₁ ∧ c₁ ≤ c₂ ∧
    d + g + 1 + 1 ≤ c₁ ∧ d + g + 1 + 1 ≤ c₂ ∧ d + g + 1 + 1 ≤ c₁ - 1 ∧ d + g + 1 + 1 ≤ c₂ - 1 ∧
    d + 3 ≤ c₁ ∧ d + 3 ≤ c₂ ∧ d + 3 ≤ c₁ - 1 ∧ d + 3 ≤ c₂ - 1 ∧
    c₁ + 1 ≤ w ∧ c₁ - 1 + 1 ≤ w ∧ c₂ - 1 + 1 ≤ w ∧
    c₁ - 1 - 1 = c₁ - 2 ∧ c₂ - 1 - 1 = c₂ - 2 := by omega

end Assembly

end DecoupledConsensusModel.Sts
