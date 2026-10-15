import Model.Vocabulary.Objects.Parameters
import Proofs.Claims.ModelIrreducible
import Proofs.Claims.Spec2Claims.Claim13bModel_slotStart
import Mathlib.Tactic.Linarith

/-!
# The slot of an instant

For an instant `t ≥ 0`, the slot after the slot `E.slotOf t` starts strictly after `t` and at most
`4Δ` after it.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Env.slotOf
  DecoupledConsensusModel.slotOfTime

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- For `t ≥ 0`, the slot after the slot of `t` starts strictly after `t` and at most `4Δ` after
    `t`. -/
theorem slotStart_slotOf_succ_bounds (E : Env V) {t : Int} (ht : 0 ≤ t) :
    t < slotStart E.Δ (E.slotOf t + 1) ∧ slotStart E.Δ (E.slotOf t + 1) ≤ t + 4 * E.Δ := by
  have hpos : (0 : Int) < 4 * E.Δ := Int.mul_pos (by decide) E.Δ_pos
  have hdm : 4 * E.Δ * (t / (4 * E.Δ)) + t % (4 * E.Δ) = t :=
    Int.mul_ediv_add_emod t (4 * E.Δ)
  have hmod : 0 ≤ t % (4 * E.Δ) := Int.emod_nonneg t (ne_of_gt hpos)
  have hmodlt : t % (4 * E.Δ) < 4 * E.Δ := Int.emod_lt_of_pos t hpos
  have hnn : 0 ≤ t / (4 * E.Δ) := Int.ediv_nonneg ht (le_of_lt hpos)
  have hc : (((t / (4 * E.Δ)).toNat : Nat) : Int) = t / (4 * E.Δ) :=
    Int.toNat_of_nonneg hnn
  have hq : E.slotOf t = (t / (4 * E.Δ)).toNat := by
    simp only [Env.slotOf, slotOfTime]
    rw [Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt hpos)]
  rw [hq]
  have hss : slotStart E.Δ ((t / (4 * E.Δ)).toNat + 1)
      = 4 * E.Δ * (t / (4 * E.Δ)) + 4 * E.Δ := by
    rw [slotStart_succ, slotStart_closed, hc]
  rw [hss]
  constructor <;> linarith

end DecoupledConsensusModel.Sts
