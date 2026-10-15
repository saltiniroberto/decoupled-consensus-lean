module
public import Model.Vocabulary.Objects.Time
public import Proofs.Claims.ModelIrreducible
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Facts about `slotStart`

Lemmas that unfold a slot's start instant.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.slotStart

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

/-- Slot `s` starts at `4Δs`. -/
theorem slotStart_closed (Δ : Int) (s : Slot) : slotStart Δ s = 4 * Δ * (s : Int) := rfl

/-- Slot `s + 1` starts `4Δ` after slot `s` starts. -/
theorem slotStart_succ (Δ : Int) (s : Slot) : slotStart Δ (s + 1) = slotStart Δ s + 4 * Δ := by
  unfold slotStart
  push_cast
  ring

/-- Slot `s + n` starts `4Δn` after slot `s` starts. -/
theorem slotStart_add (Δ : Int) (s n : Slot) :
    slotStart Δ (s + n) = slotStart Δ s + 4 * Δ * (n : Int) := by
  unfold slotStart
  push_cast
  ring

/-- If `0 ≤ Δ` and `s ≤ s'`, slot `s` starts no later than slot `s'`. -/
theorem slotStart_le_slotStart {Δ : Int} (hΔ : 0 ≤ Δ) {s s' : Slot} (h : s ≤ s') :
    slotStart Δ s ≤ slotStart Δ s' := by
  unfold slotStart
  have hs : ((s : Nat) : Int) ≤ ((s' : Nat) : Int) := by exact_mod_cast h
  exact Int.mul_le_mul_of_nonneg_left hs (by omega)

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

end DecoupledConsensusModel.Sts
