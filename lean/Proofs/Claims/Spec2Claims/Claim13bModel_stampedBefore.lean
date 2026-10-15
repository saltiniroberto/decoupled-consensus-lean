module
public import Model.Vocabulary.Objects.Time
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `stampedBefore`

Lemmas that unfold the test that an object's timestamp is strictly before a cutoff.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.stampedBefore

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {α : Type}

/-- If the timestamp map `ts` gives `a` the stamp `σ` and `σ < t`, then `a` is stamped before `t`. -/
theorem stampedBefore_of_lt {ts : TimestampMap α} {t : Time} {a : α} {σ : Stamp}
    (h : ts a = some σ) (hlt : σ < (t : Stamp)) : stampedBefore ts t a = true := by
  unfold stampedBefore
  rw [h]
  exact decide_eq_true hlt

/-- If `a` is stamped before `t` under the timestamp map `ts`, then `ts` gives `a` some stamp `σ`
    with `σ < t`. -/
theorem exists_stamp_of_stampedBefore {ts : TimestampMap α} {t : Time} {a : α}
    (h : stampedBefore ts t a = true) : ∃ σ : Stamp, ts a = some σ ∧ σ < (t : Stamp) := by
  unfold stampedBefore at h
  cases hc : ts a with
  | none => rw [hc] at h; exact absurd h Bool.false_ne_true
  | some σ => rw [hc] at h; exact ⟨σ, rfl, of_decide_eq_true h⟩

end DecoupledConsensusModel.Sts
