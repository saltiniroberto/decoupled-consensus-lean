import Spec.NodeState
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Schedule arithmetic

Facts about the spec's round schedule over `C : Config`: the round `roundAt C t` of a time, the
window starts, the openings of consecutive rounds, and how the round changes over one delay.
-/

set_option autoImplicit false

namespace SpecRecord.NoRaise

open Spec

/-- `omega` after unfolding `Time` to `Int` in every hypothesis and in the goal. -/
macro "time_omega" : tactic =>
  `(tactic| ((try simp only [Spec.Time] at *) <;> omega))

variable (C : Config)

/-- The round of the slot of the time `t`. -/
abbrev roundAt (t : Time) : Round := C.round_of (C.slotOf t)

/-- Round `ρ`'s grade-1 window start is `C.opening ρ − 5 * C.Δ`. -/
theorem grade1_window_start_eq (ρ : Round) :
    grade1_window_start C ρ = C.opening ρ - 5 * C.Δ := by
  simp only [grade1_window_start, Config.early, Protocol.Phase.earlyOffset]
  simp only [reduceCtorEq, if_false, if_true]
  ring

/-- Round `ρ`'s grade-2 window start is `C.opening ρ − 6 * C.Δ`. -/
theorem grade2_window_start_eq (ρ : Round) :
    grade2_window_start C ρ = C.opening ρ - 6 * C.Δ := by
  simp only [grade2_window_start, Config.early, Protocol.Phase.earlyOffset]
  simp only [reduceCtorEq, if_false]
  ring

/-- Round `ρ + 1` opens `4 * C.Δ * C.R` after round `ρ`. -/
theorem opening_succ (ρ : Round) :
    C.opening (ρ + 1) = C.opening ρ + 4 * C.Δ * C.R := by
  simp only [Config.opening, Config.proposal_time]
  push_cast
  ring

/-- A round lasts at least `12 * C.Δ`. -/
theorem roundLength_ge : 12 * C.Δ ≤ 4 * C.Δ * C.R := by
  have h3 : (3 : Int) ≤ C.R := by exact_mod_cast C.R_ge_three
  have hΔ : (0 : Int) < C.Δ := C.Δ_pos
  nlinarith

/-- Every opening is a multiple of `C.Δ`. -/
theorem opening_dvd (ρ : Round) : C.Δ ∣ C.opening ρ := by
  simp only [Config.opening, Config.proposal_time]
  exact ⟨4 * ((ρ * C.R : Nat) : Int), by ring⟩

/-- Openings increase with the round. -/
theorem opening_mono {ρ ρ' : Round} (h : ρ ≤ ρ') : C.opening ρ ≤ C.opening ρ' := by
  simp only [Config.opening, Config.proposal_time]
  have hΔ : (0 : Int) < C.Δ := C.Δ_pos
  have : ((ρ * C.R : Nat) : Int) ≤ ((ρ' * C.R : Nat) : Int) := by
    exact_mod_cast Nat.mul_le_mul_right _ h
  exact Int.mul_le_mul_of_nonneg_left this (by time_omega)

/-- A time `t ≥ 0` is at or after the opening of its round and before the opening of the next round. -/
theorem opening_le_self {t : Time} (ht : 0 ≤ t) :
    C.opening (roundAt C t) ≤ t ∧ t < C.opening (roundAt C t + 1) := by
  have hΔ : (0 : Int) < C.Δ := C.Δ_pos
  have hR : 0 < C.R := by have := C.R_ge_three; time_omega
  set s := C.slotOf t with hs
  have hsI : (s : Int) = t / (4 * C.Δ) := by
    rw [hs, Config.slotOf, Int.fdiv_eq_ediv_of_nonneg _ (by time_omega), Int.toNat_of_nonneg]
    exact Int.ediv_nonneg ht (by time_omega)
  have h1 : 4 * C.Δ * (s : Int) ≤ t := by
    rw [hsI, Int.mul_comm]; exact Int.ediv_mul_le t (by time_omega)
  have h2 : t < 4 * C.Δ * ((s : Int) + 1) := by
    rw [hsI, Int.mul_comm]; exact Int.lt_ediv_add_one_mul_self t (by time_omega)
  have h3 : C.round_of s * C.R ≤ s := Nat.div_mul_le_self s C.R
  have h4 : s < (C.round_of s + 1) * C.R := by
    simp only [Config.round_of]
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.lt_div_mul_add hR
  simp only [roundAt, Config.opening, Config.proposal_time]
  rw [← hs]
  constructor
  · have : ((C.round_of s * C.R : Nat) : Int) ≤ (s : Int) := by exact_mod_cast h3
    exact Int.le_trans (Int.mul_le_mul_of_nonneg_left this (by time_omega)) h1
  · have : (s : Int) + 1 ≤ (((C.round_of s + 1) * C.R : Nat) : Int) := by exact_mod_cast h4
    exact Int.lt_of_lt_of_le h2 (Int.mul_le_mul_of_nonneg_left this (by time_omega))

/-- The round of a time `t ≥ 0` is the only round `ρ` with `C.opening ρ ≤ t < C.opening (ρ + 1)`. -/
theorem round_eq_of_bounds {t : Time} {ρ : Round} (ht : 0 ≤ t) (h1 : C.opening ρ ≤ t)
    (h2 : t < C.opening (ρ + 1)) : roundAt C t = ρ := by
  obtain ⟨h3, h4⟩ := opening_le_self C ht
  rcases Nat.lt_trichotomy (roundAt C t) ρ with h | h | h
  · have h5 : (C.opening (roundAt C t + 1) : Int) ≤ C.opening ρ :=
      opening_mono C (Nat.succ_le_of_lt h)
    time_omega
  · exact h
  · have h5 : (C.opening (ρ + 1) : Int) ≤ C.opening (roundAt C t) :=
      opening_mono C (Nat.succ_le_of_lt h)
    time_omega

/-- Two multiples of `C.Δ` less than `C.Δ` apart are equal: if `t − Δ < Y ≤ t`, then `t = Y`. -/
theorem eq_of_dvd_of_window {t Y : Time} (hY : C.Δ ∣ Y) (ht : C.Δ ∣ t) (h1 : t - C.Δ < Y)
    (h2 : Y ≤ t) : t = Y := by
  have hd : C.Δ ∣ (t : Int) - Y := Int.dvd_sub ht hY
  have := Int.eq_zero_of_dvd_of_nonneg_of_lt (by time_omega) (by time_omega) hd
  time_omega

/-- For a multiple `t` of `C.Δ` with `t − Δ ≥ 0`, the round at `t` is the round at `t − Δ`, or it is
    the next round and `t` is its opening. -/
theorem round_step {t : Time} (h0 : 0 ≤ t - C.Δ) (hm : C.Δ ∣ t) :
    roundAt C t = roundAt C (t - C.Δ) ∨
      (roundAt C t = roundAt C (t - C.Δ) + 1 ∧ t = C.opening (roundAt C t)) := by
  have hΔ : (0 : Int) < C.Δ := C.Δ_pos
  obtain ⟨h1, h2⟩ := opening_le_self C h0
  by_cases hlt : (t : Int) < C.opening (roundAt C (t - C.Δ) + 1)
  · exact Or.inl (round_eq_of_bounds C (by time_omega) (by time_omega) hlt)
  · have heq : t = C.opening (roundAt C (t - C.Δ) + 1) :=
      eq_of_dvd_of_window C (opening_dvd C _) hm h2 (by time_omega)
    have hL : (12 : Int) * C.Δ ≤ 4 * C.Δ * C.R := roundLength_ge C
    have hr : roundAt C t = roundAt C (t - C.Δ) + 1 := by
      refine round_eq_of_bounds C (by time_omega) heq.ge ?_
      rw [opening_succ C (roundAt C (t - C.Δ) + 1)]
      time_omega
    exact Or.inr ⟨hr, by rw [hr]; exact heq⟩

/-- For a time `t` with `t − 1 ≥ 0`, the round at `t` is the round at `t − 1`, or it is the next
    round and `t` is its opening. -/
theorem round_step_one {t : Time} (h0 : 0 ≤ t - 1) :
    roundAt C t = roundAt C (t - 1) ∨
      (roundAt C t = roundAt C (t - 1) + 1 ∧ t = C.opening (roundAt C t)) := by
  have hΔ : (0 : Int) < C.Δ := C.Δ_pos
  obtain ⟨h1, h2⟩ := opening_le_self C h0
  by_cases hlt : (t : Int) < C.opening (roundAt C (t - 1) + 1)
  · exact Or.inl (round_eq_of_bounds C (by time_omega) (by time_omega) hlt)
  · have heq : t = C.opening (roundAt C (t - 1) + 1) := by time_omega
    have hL : (12 : Int) * C.Δ ≤ 4 * C.Δ * C.R := roundLength_ge C
    have hr : roundAt C t = roundAt C (t - 1) + 1 := by
      refine round_eq_of_bounds C (by time_omega) heq.ge ?_
      rw [opening_succ C (roundAt C (t - 1) + 1)]
      time_omega
    exact Or.inr ⟨hr, by rw [hr]; exact heq⟩

end SpecRecord.NoRaise
