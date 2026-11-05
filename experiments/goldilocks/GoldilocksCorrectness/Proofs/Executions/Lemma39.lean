module
public import GoldilocksCorrectness.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Statements.Routines.LockStatements
public import GoldilocksCorrectness.Proofs.Executions.LockSteps

@[expose] public section

/-!
# Lemma 39: where a lock entry comes from

The proof of `lem39_lock_entry_provenance`, stated in
`GoldilocksCorrectness/Statements/Executions/LockProvenanceStatements.lean`.

The route: a validator's lock entries are empty in the initial AC state, and a step does one of
three things to them (`step_cases_lock_saved`): it keeps a subset of them (a delivery, a failed
tick, a tick at neither duty time, a tick whose duty test fails, the deletion of the expired
entries); at the vote time, the revocation moves live entries to ancestors keeping their
deadlines (Lemma 38); at the support cutoff of slot `s + 1`, the confirmation update deletes none
and adds at most one entry, with the deadline of a lock of slot `s` and the block facts of
Lemma 35. So the invariant `LockTraced` holds of every entry at every step, by induction on the
step (`lockTraced_of_mem`): the entry was added by the update of the slot its deadline names, and
at every step since, some entry with its deadline sits on a block between it and the added one.
Read at the step before `t`, it is the lemma.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ supportCutoff_cast supportCutoff_eq)

open GoldilocksCorrectness.Proofs.Routines (revoke_locks_zero update_confirmation_zero)

open GoldilocksCorrectness.Proofs.Routines (acState_initial_eq initial_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `LockTraced x v i e`: the lock entry `e`, held by the validator `v` at the step `i` of `x`, was
added by `v`'s confirmation update of the slot `s` its deadline names. Write `c` for the support
cutoff of slot `s + 1`. The deadline of `e` is `S.C.t_ (s + S.C.k) + 5 · S.C.Δ`; the step
`stepBefore x c` comes before `i`; `v`'s tick at `c` starts from a state whose `awakeSince` is
some time at most the duty window's start of slot `s + 1`; the update of slot `s + 1` on `v`'s
state before `c`, its expired lock entries removed, answers some `A'` holding an entry `e₀` with
the deadline of `e`, on a block of the frame's tree other than the genesis block that is the saved
confirmation of slot `s` or an ancestor of it, a fast block of `A'` or passing the slow test; the
block of `e` is that block or an ancestor of it; and at every step after `stepBefore x c` up to
`i`, `v` holds an entry with the deadline of `e` whose block is the block of `e` or a descendant
of it, and the block of `e₀` or an ancestor of it.

The variables:
- `x`: the execution; `v`: the validator; `i`: the step; `e`: the lock entry.

Read aloud: `e` was added by `v`'s update of the slot its deadline names, and has been traced
since by entries between it and the added one. -/
def LockTraced {S : Setup V} {Sched : Schedule V} (x : AtomicExec (protocol S) Sched) (v : V)
    (i : ℕ) (e : LockEntry V) : Prop :=
  ∃ s : ℕ, e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ ∧
    stepBefore x (supportCutoff S (s + 1)) < i ∧
    (∃ τ : Time, (tickInputState x (stepBefore x (supportCutoff S (s + 1)))
      (supportCutoff S (s + 1)) v).awakeSince = some τ ∧ τ ≤ duty_window_start S.C (s + 1)) ∧
    ∃ A' : ACState V,
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A' ∧
      ∃ e₀ ∈ A'.lock_entries, e₀.d = e.d ∧
        e₀.B ∈ (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree ∧
        e₀.B ≠ Block.genesis ∧
        (∃ C' : Block V, A'.saved_confirmation s = some C' ∧ e₀.B.AncestorEq C') ∧
        (e₀.B ∈ A'.fast_blocks ∨
          slow_test S.C (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
            ((supportCutoff S (s + 1) : ℕ) : Int))
            (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S) s e₀.B = true) ∧
        e.B.AncestorEq e₀.B ∧
        ∀ i' : ℕ, stepBefore x (supportCutoff S (s + 1)) < i' → i' ≤ i →
          ∃ e' ∈ (x[i'][v].st).A.lock_entries, e'.d = e.d ∧ e.B.AncestorEq e'.B ∧
            e'.B.AncestorEq e₀.B

/-- A traced entry at the step `i` traces, at the step `i + 1`, every entry held then with its
deadline on its block or an ancestor of it: the same update added it.

The variables:
- `x`: the execution; `v`: the validator; `i`: the step; `e`: the entry at `i`; `e'`: the entry
  at `i + 1`. -/
theorem lockTraced_succ {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
    {v : V} {i : ℕ} {e e' : LockEntry V}
    -- `e` is traced at the step `i`
    (h : LockTraced x v i e)
    -- `e'` has the deadline of `e`
    (hd : e'.d = e.d)
    -- the block of `e'` is the block of `e` or an ancestor of it
    (hB : e'.B.AncestorEq e.B)
    -- `v` holds `e'` at the step `i + 1`
    (he' : e' ∈ (x[i + 1][v].st).A.lock_entries) :
    LockTraced x v (i + 1) e' := by
  obtain ⟨s, hdb, h1, h2, A', hA', e₀, he₀, hd₀, hT, hG, hC, hF, hB₀, h4⟩ := h
  refine ⟨s, hd.trans hdb, by omega, h2, A', hA', e₀, he₀, hd₀.trans hd.symm, hT, hG, hC, hF,
    ancestorEq_trans hB hB₀, fun i' hi₁ hi₂ => ?_⟩
  rcases Nat.lt_or_eq_of_le hi₂ with hlt | heq
  · obtain ⟨e'', he'', hd'', hB₁, hB₂⟩ := h4 i' hi₁ (by omega)
    exact ⟨e'', he'', hd''.trans hd.symm, ancestorEq_trans hB hB₁, hB₂⟩
  · rw [heq]
    exact ⟨e', he', rfl, ancestorEq_refl _, ancestorEq_trans hB hB₀⟩

omit [RootOrder] in
/-- A natural-number time that is the support cutoff of its slot `s + 1`, read as an integer, is
`supportCutoff S (s + 1)`.

The variables:
- `S`: the setup; `t`: the time; `s`: the slot before `t`'s slot. -/
theorem eq_supportCutoff_of_cast (S : Setup V) {t s : ℕ}
    -- `t` is the support cutoff of its slot
    (ht : (t : Int) = S.C.t_ (S.C.slot (t : Int)) + 2 * S.C.Δ)
    -- the slot of `t` is `s + 1`
    (hslot : S.C.slot (t : Int) = s + 1) :
    t = supportCutoff S (s + 1) := by
  have h1 := supportCutoff_cast S (s + 1)
  rw [hslot] at ht
  have : (t : Int) = ((supportCutoff S (s + 1) : ℕ) : Int) := by rw [h1]; exact ht
  exact_mod_cast this

/-- Every lock entry a validator holds at a step is traced there (`LockTraced`): by induction on
the step, from the initial AC state, which holds no entry, through `step_cases_lock_saved`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `v`: the validator; `i`: the step. -/
theorem lockTraced_of_mem (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (v : V) (i : ℕ) : ∀ e ∈ (x[i][v].st).A.lock_entries, LockTraced x v i e := by
  induction i with
  | zero =>
      intro e he
      rw [getElem_zero_st, initial_eq, acState_initial_eq] at he
      exact absurd he (Finset.notMem_empty e)
  | succ i ih =>
      intro e he
      rcases step_cases_lock_saved x i v with ⟨-, hsub⟩ | ⟨t, -, -, -, A', hA', -, hlk⟩ |
          ⟨t, hl, -, ht, hτ, A'', hA'', -, hlk⟩
      · -- the step keeps a subset of the entries
        exact lockTraced_succ (ih e (hsub he)) rfl (ancestorEq_refl _) he
      · -- the revocation moves live entries to ancestors
        rw [hlk] at he
        by_cases hs0 : S.C.slot (t : Int) = 0
        · rw [hs0, revoke_locks_zero] at hA'
          cases hA'
          have he₁ := (Finset.mem_filter.1 he).1
          refine lockTraced_succ (ih e he₁) rfl (ancestorEq_refl _) ?_
          rw [hlk]
          exact he
        · obtain ⟨e₁, he₁, -, hd, hB, -⟩ :=
            GoldilocksCorrectness.Statements.Routines.lem38_revoke_locks_entries_moved S.P _ A' _
              _ _ (Nat.one_le_iff_ne_zero.mpr hs0) hA' e he
          refine lockTraced_succ (ih e₁ (Finset.mem_filter.1 he₁).1) hd hB ?_
          rw [hlk]
          exact he
      · -- the confirmation update keeps every entry and adds at most one
        have he'' := he
        rw [hlk] at he
        by_cases hs0 : S.C.slot (t : Int) = 0
        · rw [hs0, update_confirmation_zero] at hA''
          cases hA''
          exact lockTraced_succ (ih e (Finset.mem_filter.1 he).1) rfl (ancestorEq_refl _) he''
        rcases (GoldilocksCorrectness.Statements.Routines.lem35_update_confirmation_lock_entries
            S.C S.P _ A'' _ _ _ hA'').2 e he with hold |
            ⟨hd, hT, hG, ⟨C', hC', hBC⟩, hF⟩
        · exact lockTraced_succ (ih e (Finset.mem_filter.1 hold).1) rfl (ancestorEq_refl _) he''
        -- a new entry: the update is the one of slot `s + 1`, `s` the slot before `t`'s
        obtain ⟨s, hb⟩ : ∃ s : ℕ, S.C.slot (t : Int) = s + 1 :=
          ⟨S.C.slot (t : Int) - 1, by
            have h0 : @Ne ℕ (S.C.slot (t : Int)) 0 := hs0
            show @Eq ℕ (S.C.slot (t : Int)) (S.C.slot (t : Int) - 1 + 1)
            omega⟩
        have htc := eq_supportCutoff_of_cast S ht hb
        subst htc
        have hsb : stepBefore x (supportCutoff S (s + 1)) = i := stepBefore_eq_of_lbl x hl
        rw [hb] at hA'' hτ hd hC' hF
        simp only [Nat.add_sub_cancel] at hd hC' hF
        refine ⟨s, hd, by omega, by rw [hsb]; exact hτ, A'', ?_, e, he, rfl, ?_, hG,
          ⟨C', hC', hBC⟩, ?_, ancestorEq_refl _, fun i' hi₁ hi₂ => ?_⟩
        · unfold stateBefore
          rw [hsb]
          exact hA''
        · unfold stateBefore
          rw [hsb]
          exact hT
        · unfold stateBefore
          rw [hsb]
          exact hF
        · have : i' = i + 1 := by omega
          rw [this]
          exact ⟨e, he'', rfl, ancestorEq_refl _, ancestorEq_refl _⟩

/-- **Lemma 39, where a lock entry comes from.** The proof; the audited statement is in
`Statements/Executions/LockProvenanceStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator;
- `e`: the lock entry. -/
theorem lem39_lock_entry_provenance (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) (e : LockEntry V)
    (hDiv : TimeDiverges x.toTrace)
    (he : e ∈ (stateBefore x t v).A.lock_entries) :
    ∃ s : ℕ, e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ ∧ supportCutoff S (s + 1) < t ∧
      (∃ τ : Time, (tickInputState x (stepBefore x (supportCutoff S (s + 1)))
        (supportCutoff S (s + 1)) v).awakeSince = some τ ∧ τ ≤ duty_window_start S.C (s + 1)) ∧
      ∃ A' : ACState V,
        update_confirmation S.C S.P
          (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
            ((supportCutoff S (s + 1) : ℕ) : Int))
          (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
          ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A' ∧
        ∃ e₀ ∈ A'.lock_entries, e₀.d = e.d ∧
          e₀.B ∈ (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree ∧
          e₀.B ≠ Block.genesis ∧
          (∃ C' : Block V, A'.saved_confirmation s = some C' ∧ e₀.B.AncestorEq C') ∧
          (e₀.B ∈ A'.fast_blocks ∨
            slow_test S.C (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
              ((supportCutoff S (s + 1) : ℕ) : Int))
              (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S) s e₀.B = true) ∧
          ∀ t' : ℕ, supportCutoff S (s + 1) < t' → t' ≤ t →
            ∃ e' ∈ (stateBefore x t' v).A.lock_entries, e'.d = e.d ∧ e.B.AncestorEq e'.B ∧
              e'.B.AncestorEq e₀.B := by
  obtain ⟨s, hd, h1, h2, A', hA', e₀, he₀, hd₀, hT, hG, hC, hF, -, h4⟩ :=
    lockTraced_of_mem S Sched x v (stepBefore x t) e he
  -- the tick at the support cutoff `c` of slot `s + 1` ends at `c`
  have hΔ := one_le_Δ S
  have hc1 : 1 ≤ supportCutoff S (s + 1) := by
    rw [supportCutoff_eq]
    omega
  have hc := (stepBefore_spec x hDiv hc1).2.2
  refine ⟨s, hd, ?_, h2, A', hA', e₀, he₀, hd₀, hT, hG, hC, hF, fun t' ht₁ ht₂ => ?_⟩
  · have := (lt_stepBefore_iff x hDiv).1 h1
    omega
  · have hlt : stepBefore x (supportCutoff S (s + 1)) < stepBefore x t' :=
      (lt_stepBefore_iff x hDiv).2 (by omega)
    exact h4 (stepBefore x t') hlt (stepBefore_mono x hDiv ht₂)

end GoldilocksCorrectness.Proofs.Executions
