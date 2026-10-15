module
public import Model.Vocabulary.Execution.Setup
import Proofs.Vocabulary.ModelVocabulary.Healing.Schedule
import Mathlib.Order.Interval.Finset.Box

@[expose] public section

/-!
# The action time names its own round

Slot arithmetic placing round `r`'s action time `a_r` in a slot of round `r`.
-/


namespace DecoupledConsensusModel.Proofs.HealingLemmas.ActionRound

open Protocol (HealConfig)
open Execution (Setup)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A time inside slot `s`'s own window names slot `s`. -/
theorem slotOfTime_add (Δ : Time) (hΔ : 0 < Δ) (s : Slot) (r : Time)
    (hr0 : 0 ≤ r) (hr : r < 4 * Δ) : slotOfTime Δ (4 * Δ * (s : Time) + r) = s := by
  have hne : (4 : Time) * Δ ≠ 0 := by
    have h : ∀ d : Int, 0 < d → (4 : Int) * d ≠ 0 := by intro d hd; omega
    exact h Δ hΔ
  unfold slotOfTime
  have hrw : 4 * Δ * (s : Time) + r = r + (s : Time) * (4 * Δ) := by ring
  rw [hrw, Int.add_mul_fdiv_right _ _ hne, Int.fdiv_eq_zero_of_lt hr0 hr, zero_add]
  simp

/-- The slot-`s` confirmation time falls in slot `s + 1`. -/
theorem slotOf_confirmation_time (E : Env V) (s : Slot) :
    E.slotOf (Protocol.confirmation_time E s) = s + 1 := by
  have h : ∀ d : Int, 0 < d → (0 : Int) ≤ 2 * d ∧ 2 * d < 4 * d := by intro d hd; omega
  obtain ⟨h0, h1⟩ := h E.Δ E.Δ_pos
  have hrw : Protocol.confirmation_time E s
      = 4 * E.Δ * ((s + 1 : Slot) : Time) + 2 * E.Δ := by
    unfold Protocol.confirmation_time Env.t slotStart
    push_cast
    ring
  rw [Env.slotOf, hrw]
  exact slotOfTime_add E.Δ E.Δ_pos (s + 1) (2 * E.Δ) h0 h1

/-- `round(rR + 1) = r`: the slot after round `r`'s opening slot is in round `r`. -/
theorem round_of_opening_succ (hc : HealConfig) (r : Round) :
    hc.round_of (hc.opening_slot r + 1) = r := by
  have key : ∀ R n : Nat, 2 ≤ R → (n * R + 1) / R = n := by
    intro R n hR
    have hR0 : 0 < R := by omega
    have hcomm : n * R + 1 = 1 + R * n := by ring
    rw [hcomm, Nat.add_mul_div_left _ _ hR0, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  simp only [Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
  exact key hc.R r hc.R_ge_two

end DecoupledConsensusModel.Proofs.HealingLemmas.ActionRound

end
