module
public import GoldilocksCorrectness.Proofs.Executions.Lemma39
public import GoldilocksCorrectness.Proofs.Executions.Lemma41
public import GoldilocksCorrectness.Proofs.Executions.ConfirmationSteps
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.Blocks

@[expose] public section

/-!
# Lemma 33: slot-by-slot compatible saved confirmations make a slow lock compatible

The proof of `lem33_slow_lock_compatible_of_slotwise_confirmations`, stated in
`GoldilocksCorrectness/Statements/Executions/HealingStatements.lean`, and three facts it reads.


## What is proved

- `saved_confirmation_kept`: a saved confirmation of slot `s` present on a validator's node state
  before `t`, with the support cutoff of slot `s + 1` before `t`, is kept at every later time: only
  the tick at that support cutoff writes it (`step_saved_changed`);
- `saved_eq_update_of_entry`: when a validator holds, just after the support cutoff of slot
  `s + 1`, a lock entry with the deadline of a lock of slot `s`, its tick at that cutoff ran the
  confirmation update, and its saved confirmations just after are that update's answer's;
- `lock_entry_saved_confirmation`: every lock entry `e` of a validator's node state before `t` is a
  lock of a slot `s` whose update ran before `t`, and the state before `t` has a saved confirmation
  of slot `s` that is `e`'s block or a descendant of it.

## The route of Lemma 33

Write `c` for the support cutoff of slot `s + 1` and `T := c + 1`. `lock_entry_saved_confirmation`
on `e_w` gives its slot `s'`, with `s' ≤ s` (its update ran before `T`), and `w`'s saved
confirmation `C_w` of slot `s'` on the state before `T`, `e_w`'s block an ancestor of it or
equal; Lemma 41 with `e_w` live at `T` gives `s' ≥ s + 1 − k`. When `s' = s`, the same fact on
`e_v` gives `v`'s saved confirmation `C_v` of slot `s` (the deadline names the slot,
`lockDeadline_injective`). When `s' < s`, the deadlines differ, so the slow test passed, and
Lemma 37 gives `v`'s saved confirmation of slot `s'` on the state before `c`, extending `e_v`'s
block, kept to `T`. In both cases the hypothesis on the saved confirmations at slot `s'`, the slot
`e_w`'s deadline names, makes the two saved confirmations compatible, and two ancestors-or-equal of
compatible blocks are compatible.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (lockDeadline_injective one_le_Δ slotStart_eq
  slot_eq_of_mem supportCutoff_cast supportCutoff_eq supportCutoff_lt_of_lt voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_both)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans compatible_iff
  compatible_of_ancestorEq_compatible voteTime_ne_cutoff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

variable {S : Setup V} {Sched : Schedule V}

/-- A saved confirmation of slot `s` present on `v`'s node state before `t`, when the support
cutoff of slot `s + 1` is before `t`, is present with the same block on `v`'s node state before
every later time `t'`: a step that changes it is the tick at that support cutoff
(`step_saved_changed`), which comes before `t`.

The variables:
- `x`: the execution; `v`: the validator; `s`: the slot of the confirmation; `C'`: the block;
  `t`, `t'`: the two times.

Read aloud: once the update of slot `s + 1` is past, the saved confirmation of slot `s` stays. -/
theorem saved_confirmation_kept (x : AtomicExec (protocol S) Sched)
    (hDiv : TimeDiverges x.toTrace) (v : V) (s : ℕ) (C' : Block V) {t t' : ℕ}
    -- the support cutoff of slot `s + 1` is before `t`
    (hc : supportCutoff S (s + 1) < t)
    -- `t'` is `t` or later
    (htt' : t ≤ t')
    -- `v`'s node state before `t` has `C'` saved as the confirmation of slot `s`
    (hSaved : (stateBefore x t v).A.saved_confirmation s = some C') :
    (stateBefore x t' v).A.saved_confirmation s = some C' := by
  have hrel := rel_stateBefore_of_step x hDiv
    (fun n n' => n'.A.saved_confirmation s = n.A.saved_confirmation s)
    (fun _ => rfl) (fun _ _ _ h h' => h'.trans h) htt' v (fun i hi _ => by
      by_contra hne
      obtain ⟨hl, -⟩ := step_saved_changed x i v s hne
      have h1 := (time_of_lbl_tickAllAwake x hl).2
      have h2 : i < stepBefore x t := (lt_stepBefore_iff x hDiv).2 (by omega)
      omega)
  exact hrel.trans hSaved

/-- When `v`'s node state just after the support cutoff of slot `s + 1` holds a lock entry with
the deadline of a lock of slot `s`, `v`'s tick at that cutoff ran the confirmation update of slot
`s + 1`, and `v`'s saved confirmations just after are those of the update's answer `A'` on `v`'s
state before the cutoff, its expired entries removed.

Why: the tick at the cutoff `c` does one of three things (`step_cases_lock_saved`). It cannot keep
a subset of the entries: the entry would then be held before `c`, and Lemma 39 would place the
update that added it, the one of slot `s + 1` since the deadline names the slot, strictly before
`c`. It cannot revoke: `c` is not a vote time. So it ran the update, on the state before `c`,
whose answer is `A'`; the deliveries at the time `c` keep the saved confirmations
(`stateBefore_succ_keepsConfirmation`).

The variables:
- `x`: the execution; `v`: the validator; `s`: the slot of the lock; `e`: the lock entry;
  `A'`: the update's answer.

Read aloud: a lock of slot `s` held just after the update of slot `s + 1` means that update ran,
and the saved confirmations just after are its answer's. -/
theorem saved_eq_update_of_entry (x : AtomicExec (protocol S) Sched)
    (hDiv : TimeDiverges x.toTrace) (v : V) (s : ℕ) (e : LockEntry V) (A' : ACState V)
    -- `v` holds `e` just after the support cutoff of slot `s + 1`
    (he : e ∈ (stateBefore x (supportCutoff S (s + 1) + 1) v).A.lock_entries)
    -- `e` has the deadline of a lock of slot `s`
    (hd : e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    -- the update of slot `s + 1` on `v`'s state before the cutoff answers `A'`
    (hA' : update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A') :
    (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation =
      A'.saved_confirmation := by
  have hΔ := one_le_Δ S
  have hc1 : 1 ≤ supportCutoff S (s + 1) := by
    rw [supportCutoff_eq]
    omega
  obtain ⟨hl, -, hti'⟩ := stepBefore_spec x hDiv hc1
  have hK := stateBefore_succ_keepsConfirmation x hDiv v hti'
  have hslot : S.C.slot ((supportCutoff S (s + 1) : ℕ) : Int) = s + 1 := by
    have h1 : slotStart S (s + 1 + 1) = slotStart S (s + 1) + 4 * Δ S := by
      rw [slotStart_eq, slotStart_eq S (s + 1), Nat.mul_add, Nat.mul_one]
    have h2 := supportCutoff_eq S (s + 1)
    have h3 := voteTime_eq S (s + 1)
    exact slot_eq_of_mem S (by omega) (by omega)
  rw [hK.2.1]
  rcases step_cases_lock_saved x (stepBefore x (supportCutoff S (s + 1))) v with
      ⟨-, hsub⟩ | ⟨t, hl', -, ht, -⟩ | ⟨t, hl', -, -, -, A'', hA'', hsv, -⟩
  · -- the tick kept a subset of the entries: `e` was held before the cutoff, impossible
    exfalso
    have he' : e ∈ (stateBefore x (supportCutoff S (s + 1)) v).A.lock_entries := by
      have h1 : e ∈ (x[stepBefore x (supportCutoff S (s + 1)) + 1][v].st).A.lock_entries := by
        rw [← hK.1]
        exact he
      exact hsub h1
    obtain ⟨s', hd', hlt, -⟩ :=
      lem39_lock_entry_provenance S Sched x (supportCutoff S (s + 1)) v e hDiv he'
    have hb' : s' = s := lockDeadline_injective S (hd'.symm.trans hd)
    rw [hb'] at hlt
    exact lt_irrefl _ hlt
  · -- the tick revoked: the cutoff is not a vote time
    exfalso
    have htc : t = supportCutoff S (s + 1) := by
      have h := hl.symm.trans hl'
      injection h with h
      exact h.symm
    subst htc
    exact voteTime_ne_cutoff ht (by rw [hslot, supportCutoff_cast])
  · -- the tick ran the update, whose answer is `A'`
    have htc : t = supportCutoff S (s + 1) := by
      have h := hl.symm.trans hl'
      injection h with h
      exact h.symm
    subst htc
    rw [hslot] at hA''
    have hAA : A'' = A' := by
      have h : (Except.ok A'' : DRE (ACState V)) = Except.ok A' := hA''.symm.trans hA'
      injection h
    rw [hsv, hAA]

/-- Every lock entry `e` of `v`'s node state before `t` is a lock of a slot `s` whose update ran
before `t`: the deadline of `e` is `S.C.t_ (s + S.C.k) + 5 · S.C.Δ`, the support cutoff of slot
`s + 1` is before `t`, and `v`'s node state before `t` has a saved confirmation of slot `s` that
is `e`'s block or a descendant of it.

Why: Lemma 39 gives the update of slot `s + 1` that added an entry `e₀` with `e`'s deadline on a
block that its answer saves as the confirmation of slot `s` or an ancestor of it, and entries with
that deadline at every time since, between `e`'s block and `e₀`'s; the one just after the cutoff
makes the saved confirmations then the answer's (`saved_eq_update_of_entry`), kept to `t`
(`saved_confirmation_kept`).

The variables:
- `x`: the execution; `t`: the time; `v`: the validator; `e`: the lock entry.

Read aloud: a lock entry is on its slot's saved confirmation or an ancestor of it. -/
theorem lock_entry_saved_confirmation (x : AtomicExec (protocol S) Sched)
    (hDiv : TimeDiverges x.toTrace) (t : ℕ) (v : V) (e : LockEntry V)
    -- `e` is a lock entry of `v`'s node state before `t`
    (he : e ∈ (stateBefore x t v).A.lock_entries) :
    ∃ s : ℕ, e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ ∧ supportCutoff S (s + 1) < t ∧
      ∃ C' : Block V, (stateBefore x t v).A.saved_confirmation s = some C' ∧
        e.B.AncestorEq C' := by
  obtain ⟨s, hd, hlt, -, A', hA', e₀, -, -, -, -, ⟨C', hC', hBC⟩, -, htr⟩ :=
    lem39_lock_entry_provenance S Sched x t v e hDiv he
  obtain ⟨e₁, he₁, hd₁, -, -⟩ := htr (supportCutoff S (s + 1) + 1) (by omega) (by omega)
  have hsv := saved_eq_update_of_entry x hDiv v s e₁ A' he₁ (hd₁.trans hd) hA'
  have hs1 : (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some C' := by
    rw [hsv]
    exact hC'
  have hsT := saved_confirmation_kept x hDiv v s C' (t := supportCutoff S (s + 1) + 1) (t' := t)
    (by omega) (by omega) hs1
  obtain ⟨e₂, -, -, hB₁, hB₂⟩ := htr t hlt le_rfl
  exact ⟨s, hd, hlt, C', hsT, ancestorEq_trans hB₁ (ancestorEq_trans hB₂ hBC)⟩

/-- **Lemma 33, slot-by-slot compatible saved confirmations make a slow or same-slot lock
compatible.** The proof; the audited statement is in
`Statements/Executions/HealingStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot of `v`'s lock;
- `v`, `w`: the two validators; `e_v`, `e_w`: their lock entries. -/
theorem lem33_slow_lock_compatible_of_slotwise_confirmations (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (s : ℕ) (v w : V) (e_v e_w : LockEntry V)
    (hDiv : TimeDiverges x.toTrace)
    (hCompat : ∀ s' : ℕ, e_w.d = S.C.t_ (s' + S.C.k) + 5 * S.C.Δ → ∀ Cv Cw : Block V,
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s' = some Cv →
      (stateBefore x (supportCutoff S (s + 1) + 1) w).A.saved_confirmation s' = some Cw →
      Cv.compatible Cw = true)
    (he_v : e_v ∈ (stateBefore x (supportCutoff S (s + 1) + 1) v).A.lock_entries)
    (hd_v : e_v.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    (he_w : e_w ∈ (stateBefore x (supportCutoff S (s + 1) + 1) w).A.lock_entries)
    (hlive_w : ((supportCutoff S (s + 1) + 1 : ℕ) : Int) < e_w.d)
    (hSlowOrSame : slow_test S.C (stateBefore x (supportCutoff S (s + 1)) v).A
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S) s e_v.B = true ∨
      e_w.d = e_v.d) :
    e_v.B.compatible e_w.B = true := by
  have hΔ := one_le_Δ S
  -- the slot `s'` of `e_w`, and `w`'s saved confirmation of it
  obtain ⟨s', hd_w, hc_w, C_w, hC_w, hB_w⟩ :=
    lock_entry_saved_confirmation x hDiv _ w e_w he_w
  -- `s' ≤ s`: the update of slot `s' + 1` ran before `supportCutoff S (s + 1) + 1`
  have hle : s' ≤ s := by
    by_contra h
    have := supportCutoff_lt_of_lt S (show s + 1 < s' + 1 by omega)
    omega
  -- `s + 1 − k ≤ s'`: `e_w` is still live at `supportCutoff S (s + 1) + 1`
  have hlow : s + 1 - S.C.k ≤ s' := by
    by_cases hkb : S.C.k ≤ s + 1
    · refine GoldilocksCorrectness.Proofs.Executions.lem41_slot_of_live_entry S (s + 1 - S.C.k)
        s' (supportCutoff S (s + 1) + 1) e_w hd_w hlive_w ?_
      rw [Nat.sub_add_cancel hkb, supportCutoff_eq]
      omega
    · omega
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · -- `s' < s`: the two locks are of different slots, so `e_v` passed the slow test
    rcases hSlowOrSame with hSlow | hSame
    · obtain ⟨-, hj⟩ :=
        GoldilocksCorrectness.Statements.Routines.lem37_slow_test_saved_confirmations S.C _ _ s
          e_v.B hSlow
      obtain ⟨C', hCj, -, hBj⟩ := hj s' hlow hlt
      have hCj' := saved_confirmation_kept x hDiv v s' C'
        (supportCutoff_lt_of_lt S (show s' + 1 < s + 1 by omega)) (Nat.le_succ _) hCj
      exact compatible_of_ancestorEq_both hBj hB_w (hCompat s' hd_w C' C_w hCj' hC_w)
    · exfalso
      have : s' = s := lockDeadline_injective S (hd_w.symm.trans (hSame.trans hd_v))
      omega
  · -- `s' = s`: both locks are of slot `s`
    obtain ⟨s'', hd_v', -, C_v, hC_v, hB_v⟩ :=
      lock_entry_saved_confirmation x hDiv _ v e_v he_v
    have hbv : s'' = s := lockDeadline_injective S (hd_v'.symm.trans hd_v)
    rw [hbv] at hC_v
    rw [heq] at hC_w hd_w
    exact compatible_of_ancestorEq_both hB_v hB_w
      (hCompat s hd_w C_v C_w hC_v hC_w)

end GoldilocksCorrectness.Proofs.Executions
