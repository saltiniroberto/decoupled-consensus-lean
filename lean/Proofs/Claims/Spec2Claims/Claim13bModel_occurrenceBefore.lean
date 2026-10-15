import Model.Vocabulary.Objects.Time
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `occurrenceBefore`

Lemmas that unfold the test that an occurrence, a stamp or the absent occurrence `none`, is strictly
before a cutoff.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.occurrenceBefore

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

/-- The absent occurrence `none` is strictly before no cutoff `Γ`. -/
theorem occurrenceBefore_none (Γ : Time) : occurrenceBefore none Γ = false := by
  unfold occurrenceBefore
  rfl

/-- The occurrence `some u` is strictly before the cutoff `Γ` exactly when `u < Γ`. -/
theorem occurrenceBefore_some_iff (u : Stamp) (Γ : Time) :
    occurrenceBefore (some u) Γ = true ↔ u < (Γ : Stamp) := by
  unfold occurrenceBefore
  exact decide_eq_true_iff

end DecoupledConsensusModel.Sts
