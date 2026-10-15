module
public import Model.Vocabulary.Objects.Time

@[expose] public section

/-!
# Cutoff tests on occurrences

Facts about the cutoff test `occurrenceBefore` on stamps and occurrences, and its negation
`occurrenceAtLeast`.
-/


namespace DecoupledConsensusModel

variable {α : Type}

/-- The stamp cutoff test `stampedBefore` is the occurrence cutoff test applied to the stamp. -/
theorem stampedBefore_eq_occurrenceBefore (ts : TimestampMap α) (Γ : Time) (x : α) :
    stampedBefore ts Γ x = occurrenceBefore (ts x) Γ := rfl

/-- `e_v ≥ Γ`, the negation of the cutoff test; the occurrence `+∞` (none) satisfies it. -/
def occurrenceAtLeast (x : Occurrence) (Γ : Time) : Bool :=
  !occurrenceBefore x Γ

/-- An occurrence before `Γ` is before every later cutoff `Γ'`. -/
theorem occurrenceBefore_mono {x : Occurrence} {Γ Γ' : Time} (h : Γ ≤ Γ')
    (hx : occurrenceBefore x Γ = true) : occurrenceBefore x Γ' = true := by
  cases hs : x with
  | none => rw [hs] at hx; exact absurd hx (by simp [occurrenceBefore])
  | some u =>
    rw [hs] at hx
    simp only [occurrenceBefore, decide_eq_true_eq] at hx ⊢
    exact lt_of_lt_of_le hx (by exact_mod_cast h)

/-- If the maximum of two occurrences is before `Γ`, so is the first. -/
theorem occurrenceBefore_of_max_left {x y : Occurrence} {Γ : Time}
    (h : occurrenceBefore (occurrenceMax x y) Γ = true) :
    occurrenceBefore x Γ = true := by
  cases hx : x with
  | none => rw [hx] at h; exact absurd h (by simp [occurrenceMax, occurrenceBefore])
  | some a =>
    cases hy : y with
    | none => rw [hx, hy] at h; exact absurd h (by simp [occurrenceMax, occurrenceBefore])
    | some b =>
      rw [hx, hy] at h
      simp only [occurrenceMax, occurrenceBefore, decide_eq_true_eq] at h ⊢
      exact lt_of_le_of_lt (le_max_left a b) h

/-- If both occurrences are before `Γ`, so is their maximum. -/
theorem occurrenceBefore_max {x y : Occurrence} {Γ : Time}
    (hx : occurrenceBefore x Γ = true) (hy : occurrenceBefore y Γ = true) :
    occurrenceBefore (occurrenceMax x y) Γ = true := by
  cases hxe : x with
  | none => rw [hxe] at hx; exact absurd hx (by simp [occurrenceBefore])
  | some a =>
    cases hye : y with
    | none => rw [hye] at hy; exact absurd hy (by simp [occurrenceBefore])
    | some b =>
      rw [hxe] at hx; rw [hye] at hy
      simp only [occurrenceMax, occurrenceBefore, decide_eq_true_eq] at hx hy ⊢
      exact max_lt hx hy

end DecoupledConsensusModel

end
