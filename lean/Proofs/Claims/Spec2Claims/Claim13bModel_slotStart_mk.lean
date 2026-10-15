module
public import Model.Vocabulary.Execution.Setup
public import Proofs.Claims.ModelIrreducible
public import Proofs.Claims.Spec2Claims.Claim13bModel_Env_slotOf_s3
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Facts about `slotStart` at a `Setup`

A slot's start instant, read at the delay of a `Setup` and against `Env.slotOf`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.slotStart

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The start of slot `s`, `4 * S.E.Δ * s`, is a multiple of `S.E.Δ`. -/
theorem slotStart_emod_delta (S : Setup V) (s : Slot) :
    slotStart S.E.Δ s % S.E.Δ = 0 := by
  have hrw : slotStart S.E.Δ s = S.E.Δ * (4 * (s : Int)) := by
    show 4 * S.E.Δ * (s : Int) = _
    ring
  rw [hrw]
  exact Int.mul_emod_right _ _

/-- If `0 < s`, slot `s` starts strictly after `0`. -/
theorem slotStart_pos (S : Setup V) {s : Slot} (hs : 0 < s) :
    0 < slotStart S.E.Δ s := by
  have hsi : (0 : Int) < (s : Int) := by exact_mod_cast hs
  show (0 : Int) < 4 * S.E.Δ * (s : Int)
  exact Int.mul_pos (Int.mul_pos (by decide) S.E.Δ_pos) hsi

/-- If `s_0 ≤ s_1`, slot `s_0` starts no later than slot `s_1`. -/
theorem slotStart_mono (S : Setup V) {s_0 s_1 : Slot} (h : s_0 ≤ s_1) :
    slotStart S.E.Δ s_0 ≤ slotStart S.E.Δ s_1 := by
  have hsi : ((s_0 : Nat) : Int) ≤ ((s_1 : Nat) : Int) := by exact_mod_cast h
  show 4 * S.E.Δ * (s_0 : Int) ≤ 4 * S.E.Δ * (s_1 : Int)
  exact Int.mul_le_mul_of_nonneg_left hsi
    (le_of_lt (Int.mul_pos (by decide) S.E.Δ_pos))

/-- If `0 ≤ t` and `t` is strictly less than the start of slot `s`, then the slot of `t` is strictly
    less than `s`. -/
theorem slotOf_lt_of_lt_slotStart (S : Setup V) {t : Int} {s : Slot}
    (ht : 0 ≤ t) (h : t < slotStart S.E.Δ s) : S.E.slotOf t < s := by
  have hpos : (0 : Int) < 4 * S.E.Δ := Int.mul_pos (by decide) S.E.Δ_pos
  have hdm : 4 * S.E.Δ * (t / (4 * S.E.Δ)) + t % (4 * S.E.Δ) = t :=
    Int.mul_ediv_add_emod t (4 * S.E.Δ)
  have hmod : 0 ≤ t % (4 * S.E.Δ) := Int.emod_nonneg t (ne_of_gt hpos)
  have hnn : 0 ≤ t / (4 * S.E.Δ) := Int.ediv_nonneg ht (le_of_lt hpos)
  have hss : t < 4 * S.E.Δ * (s : Int) := h
  have hd : t / (4 * S.E.Δ) < (s : Int) := by
    by_contra hcon
    have hle : (s : Int) ≤ t / (4 * S.E.Δ) := not_lt.mp hcon
    have hmul : 4 * S.E.Δ * (s : Int) ≤ 4 * S.E.Δ * (t / (4 * S.E.Δ)) :=
      Int.mul_le_mul_of_nonneg_left hle (le_of_lt hpos)
    linarith
  rw [slotOf_eq_ediv S t]
  exact (Int.toNat_lt hnn).mpr hd

/-- If `0 ≤ t` and `s` is at most the slot of `t`, then slot `s` starts no later than `t`. -/
theorem slotStart_le_of_le_slotOf (S : Setup V) {t : Int} {s : Slot}
    (ht : 0 ≤ t) (h : s ≤ S.E.slotOf t) : slotStart S.E.Δ s ≤ t := by
  have hpos : (0 : Int) < 4 * S.E.Δ := Int.mul_pos (by decide) S.E.Δ_pos
  have hdm : 4 * S.E.Δ * (t / (4 * S.E.Δ)) + t % (4 * S.E.Δ) = t :=
    Int.mul_ediv_add_emod t (4 * S.E.Δ)
  have hmod : 0 ≤ t % (4 * S.E.Δ) := Int.emod_nonneg t (ne_of_gt hpos)
  have hnn : 0 ≤ t / (4 * S.E.Δ) := Int.ediv_nonneg ht (le_of_lt hpos)
  rw [slotOf_eq_ediv S t] at h
  have hle : (s : Int) ≤ t / (4 * S.E.Δ) := (Int.le_toNat hnn).mp h
  have hmul : 4 * S.E.Δ * (s : Int) ≤ 4 * S.E.Δ * (t / (4 * S.E.Δ)) :=
    Int.mul_le_mul_of_nonneg_left hle (le_of_lt hpos)
  show 4 * S.E.Δ * (s : Int) ≤ t
  linarith

/-- If `0 ≤ Δ`, every slot starts at or after time zero. -/
theorem slotStart_nonneg {Δ : Int} (hΔ : 0 ≤ Δ) (s : Slot) : 0 ≤ slotStart Δ s := by
  unfold slotStart
  have hs : (0 : Int) ≤ ((s : Nat) : Int) := Int.natCast_nonneg _
  exact Int.mul_nonneg (Int.mul_nonneg (by decide) hΔ) hs

end DecoupledConsensusModel.Sts
