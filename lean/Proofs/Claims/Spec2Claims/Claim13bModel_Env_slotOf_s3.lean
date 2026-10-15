module
public import Model.Vocabulary.Execution.Setup
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# The slot of an instant, as a quotient

The slot of an instant is monotone in the instant, and is the integer quotient of the instant by
`4Δ`, clamped at `0`.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Env.slotOf
  DecoupledConsensusModel.slotOfTime

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A later instant falls in a slot at or after an earlier instant's slot. -/
theorem slotOf_mono_sts (S : Setup V) {t_0 t_1 : Int} (h : t_0 ≤ t_1) :
    S.E.slotOf t_0 ≤ S.E.slotOf t_1 := by
  have hpos : (0 : Int) < 4 * S.E.Δ := Int.mul_pos (by decide) S.E.Δ_pos
  simp only [Env.slotOf, slotOfTime]
  rw [Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt hpos),
    Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt hpos)]
  exact Int.toNat_le_toNat (Int.ediv_le_ediv hpos h)

/-- The slot of `t` is the integer quotient of `t` by `4 * S.E.Δ`, clamped at `0`. -/
theorem slotOf_eq_ediv (S : Setup V) (t : Int) :
    S.E.slotOf t = (t / (4 * S.E.Δ)).toNat := by
  have hpos : (0 : Int) < 4 * S.E.Δ := Int.mul_pos (by decide) S.E.Δ_pos
  simp only [Env.slotOf, slotOfTime]
  rw [Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt hpos)]

end DecoupledConsensusModel.Sts
