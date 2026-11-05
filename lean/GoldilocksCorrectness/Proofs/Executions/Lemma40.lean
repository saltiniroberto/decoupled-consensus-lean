module
public import GoldilocksCorrectness.Proofs.Executions.LockSteps

@[expose] public section

/-!
# Lemma 40: where a saved confirmation comes from

The proof of `lem40_saved_confirmation_provenance`, stated in
`GoldilocksCorrectness/Statements/Executions/LockProvenanceStatements.lean`.

The route: a validator's saved confirmation of slot `s'` is `none` in the initial AC state, and the
only step that changes it is the validator's tick at the support cutoff of slot `s' + 1`, running
the confirmation update of slot `s' + 1` with the duty test passing (`step_saved_changed`). So the
invariant `SavedTraced` holds at every step, by induction on the step: a saved confirmation
`some C'` of slot `s'` at the step `i` was written by that tick, before `i`, and has been `some C'`
at every step since. Read at the step before `t`, it is the lemma.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ supportCutoff_eq)

open GoldilocksCorrectness.Proofs.Routines (acState_initial_eq initial_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `SavedTraced x v s' C' i`: if the validator `v`'s saved confirmation of slot `s'` at the step
`i` of `x` is `some C'`, then the step `stepBefore x c`, `c` the support cutoff of slot `s' + 1`,
comes before `i`; `v`'s tick at `c` starts from a state whose `awakeSince` is some time at most the
duty window's start of slot `s' + 1`; the confirmation update of slot `s' + 1` on `v`'s state before
`c`, its expired lock entries removed, answers some `A'` saving `C'` as the confirmation of slot
`s'`; and at every step after `stepBefore x c` up to `i`, `v`'s saved confirmation of slot `s'` is
`some C'`.

The variables:
- `x`: the execution; `v`: the validator; `s'`: the slot of the confirmation; `C'`: the block;
  `i`: the step.

Read aloud: a saved confirmation of slot `s'` at the step `i` was saved by `v`'s update of slot
`s' + 1` and has been kept since. -/
def SavedTraced {S : Setup V} {Sched : Schedule V} (x : AtomicExec (protocol S) Sched) (v : V)
    (s' : ℕ) (C' : Block V) (i : ℕ) : Prop :=
  (x[i][v].st).A.saved_confirmation s' = some C' →
    stepBefore x (supportCutoff S (s' + 1)) < i ∧
    (∃ τ : Time, (tickInputState x (stepBefore x (supportCutoff S (s' + 1)))
      (supportCutoff S (s' + 1)) v).awakeSince = some τ ∧ τ ≤ duty_window_start S.C (s' + 1)) ∧
    (∃ A' : ACState V,
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s' + 1)) v).A
          ((supportCutoff S (s' + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s' + 1)) v).S)
        ((supportCutoff S (s' + 1) : ℕ) : Int) (s' + 1) = .ok A' ∧
      A'.saved_confirmation s' = some C') ∧
    ∀ i' : ℕ, stepBefore x (supportCutoff S (s' + 1)) < i' → i' ≤ i →
      (x[i'][v].st).A.saved_confirmation s' = some C'

/-- `SavedTraced` holds at every step: by induction on the step, from the initial AC state, which
saves no confirmation, through `step_saved_changed`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `v`: the validator; `s'`: the slot of
  the confirmation; `C'`: the block; `i`: the step. -/
theorem savedTraced (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched) (v : V)
    (s' : ℕ) (C' : Block V) (i : ℕ) : SavedTraced x v s' C' i := by
  induction i with
  | zero =>
      intro h
      rw [getElem_zero_st, initial_eq, acState_initial_eq] at h
      cases h
  | succ i ih =>
      intro h
      by_cases hc : (x[i + 1][v].st).A.saved_confirmation s' = (x[i][v].st).A.saved_confirmation s'
      · -- the step keeps the field
        obtain ⟨h1, h2, h3, h4⟩ := ih (hc ▸ h)
        refine ⟨by omega, h2, h3, fun i' hi₁ hi₂ => ?_⟩
        rcases Nat.lt_or_eq_of_le hi₂ with hlt | heq
        · exact h4 i' hi₁ (by omega)
        · rw [heq]
          exact h
      · -- the step is the tick at the support cutoff of slot `s' + 1`
        obtain ⟨hl, -, hτ, A'', hA'', hsv⟩ := step_saved_changed x i v s' hc
        have hsb : stepBefore x (supportCutoff S (s' + 1)) = i := stepBefore_eq_of_lbl x hl
        refine ⟨by omega, by rw [hsb]; exact hτ, ⟨A'', ?_, (congrFun hsv s').symm.trans h⟩,
          fun i' hi₁ hi₂ => ?_⟩
        · unfold stateBefore
          rw [hsb]
          exact hA''
        · have : i' = i + 1 := by omega
          rw [this]
          exact h

/-- **Lemma 40, where a saved confirmation comes from.** The proof; the audited statement is in
`Statements/Executions/LockProvenanceStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator;
- `s'`: the slot of the confirmation; `C'`: the block saved. -/
theorem lem40_saved_confirmation_provenance (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) (s' : ℕ) (C' : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hSaved : (stateBefore x t v).A.saved_confirmation s' = some C') :
    supportCutoff S (s' + 1) < t ∧
      (∃ τ : Time, (tickInputState x (stepBefore x (supportCutoff S (s' + 1)))
        (supportCutoff S (s' + 1)) v).awakeSince = some τ ∧ τ ≤ duty_window_start S.C (s' + 1)) ∧
      (∃ A' : ACState V,
        update_confirmation S.C S.P
          (expireLocks (stateBefore x (supportCutoff S (s' + 1)) v).A
            ((supportCutoff S (s' + 1) : ℕ) : Int))
          (fg_to_ac (stateBefore x (supportCutoff S (s' + 1)) v).S)
          ((supportCutoff S (s' + 1) : ℕ) : Int) (s' + 1) = .ok A' ∧
        A'.saved_confirmation s' = some C') ∧
      ∀ t' : ℕ, supportCutoff S (s' + 1) < t' → t' ≤ t →
        (stateBefore x t' v).A.saved_confirmation s' = some C' := by
  obtain ⟨h1, h2, h3, h4⟩ := savedTraced S Sched x v s' C' (stepBefore x t) hSaved
  -- the tick at the support cutoff `c` of slot `s' + 1` ends at `c`
  have hΔ := one_le_Δ S
  have hc1 : 1 ≤ supportCutoff S (s' + 1) := by
    rw [supportCutoff_eq]
    omega
  have hc := (stepBefore_spec x hDiv hc1).2.2
  refine ⟨?_, h2, h3, fun t' ht₁ ht₂ => ?_⟩
  · have := (lt_stepBefore_iff x hDiv).1 h1
    omega
  · have hlt : stepBefore x (supportCutoff S (s' + 1)) < stepBefore x t' :=
      (lt_stepBefore_iff x hDiv).2 (by omega)
    exact h4 (stepBefore x t') hlt (stepBefore_mono x hDiv ht₂)

end GoldilocksCorrectness.Proofs.Executions
