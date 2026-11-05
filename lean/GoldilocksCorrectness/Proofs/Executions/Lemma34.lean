module
public import GoldilocksCorrectness.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma33

@[expose] public section

/-!
# Lemma 34: a fast lock against an older lock, through the revocation

The proof of `lem34_fast_lock_compatible_of_revocation`, stated in
`GoldilocksCorrectness/Statements/Executions/HealingStatements.lean`.

The route: write `t₃` for the vote time of slot `s + 1` and `c` for the support cutoff of slot
`s + 1`. Lemma 39 on `e_w` gives its slot `s'`, with `s' < s` since its deadline is before
`e_v`'s, so the update that added it ran at the support cutoff of slot `s' + 1`, before `t₃`; its
tracking clause at `t₃ + 1` gives an entry `e'` of `w`'s state before `t₃ + 1` with `e_w`'s
deadline, whose block is `e_w`'s block or a descendant of it. `w` is awake and honest at `t₃`, so
its tick then answered (`ticksSucceed_of_exec`); with the duty test passing, Lemma 13 gives the
revocation's answer `A'` with the tick's lock entries, which the deliveries at `t₃` keep
(`stateBefore_succ_keepsConfirmation`); so `e' ∈ A'.lock_entries`. `e'` is live at `t₃`: its
deadline is after `c + 1`, and its block is in the frame's tree (`revoke_locks_entry_mem_tree`). The
hypothesis on the revocation makes `e'`'s block compatible with `e_v`'s, and so is its ancestor
`e_w`'s block. -/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem supportCutoff_eq
  supportCutoff_lt_of_lt voteTime_cast voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (is_live_iff)

open GoldilocksCorrectness.Proofs.Routines (t_eq_mul)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (compatible_iff compatible_of_ancestorEq_compatible
  revoke_locks_entry_mem_tree)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 34, a fast lock against an older lock, through the revocation.** The proof; the
audited statement is in `Statements/Executions/HealingStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot of `e_v`'s lock;
- `w`: the validator whose revocation is read; `e_v`: a lock entry with the deadline of a lock of
  slot `s`; `e_w`: `w`'s older live lock entry. -/
theorem lem34_fast_lock_compatible_of_revocation (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (s : ℕ) (w : V) (e_v e_w : LockEntry V)
    (hDiv : TimeDiverges x.toTrace)
    (hd_v : e_v.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    (he_w : e_w ∈ (stateBefore x (supportCutoff S (s + 1) + 1) w).A.lock_entries)
    (hlive_w : ((supportCutoff S (s + 1) + 1 : ℕ) : Int) < e_w.d)
    (hOlder : e_w.d < e_v.d)
    (hw₃ : w ∈ Sched.awake (voteTime S (s + 1) : Int) ∧ w ∉ Sched.adv (voteTime S (s + 1) : Int))
    (hDuty : ∃ τ : Time, (tickInputState x (stepBefore x (voteTime S (s + 1)))
      (voteTime S (s + 1)) w).awakeSince = some τ ∧ τ ≤ duty_window_start S.C (s + 1))
    (hLocks : ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.compatible e_v.B = true) :
    e_v.B.compatible e_w.B = true := by
  have hΔ := one_le_Δ S
  -- the times
  have hss : slotStart S (s + 1 + 1) = slotStart S (s + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s + 1), Nat.mul_add, Nat.mul_one]
  have hss' : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S s, Nat.mul_add, Nat.mul_one]
  have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hv₂ : supportCutoff S (s + 1) = voteTime S (s + 1) + Δ S := supportCutoff_eq S (s + 1)
  have hcb : supportCutoff S s = voteTime S s + Δ S := supportCutoff_eq S s
  have hvb : voteTime S s = slotStart S s + Δ S := voteTime_eq S s
  have hslot₃ : S.C.slot ((voteTime S (s + 1) : ℕ) : Int) = s + 1 :=
    slot_eq_of_mem S (by omega) (by omega)
  -- the slot `s'` of `e_w`, before `s`
  obtain ⟨s', hd_w, -, -, A_w, -, e₀, -, -, -, -, -, -, htr⟩ :=
    lem39_lock_entry_provenance S Sched x _ w e_w hDiv he_w
  have hlt : s' < s := by
    by_contra h
    have hΔi : (0 : Int) < S.C.Δ := S.C.Δ_pos
    have h1 : @LT.lt Int _ (S.C.t_ (s' + S.C.k) + 5 * S.C.Δ) (S.C.t_ (s + S.C.k) + 5 * S.C.Δ) := by
      rw [← hd_w, ← hd_v]
      exact hOlder
    have h2 : (((s + S.C.k : ℕ) : Int)) ≤ (((s' + S.C.k : ℕ) : Int)) := by
      exact_mod_cast (show s + S.C.k ≤ s' + S.C.k by omega)
    have h3 : @LE.le Int _ (4 * S.C.Δ * (((s + S.C.k : ℕ) : Int)))
        (4 * S.C.Δ * (((s' + S.C.k : ℕ) : Int))) :=
      Int.mul_le_mul_of_nonneg_left h2 (by omega)
    have h4 : @LT.lt Int _ (4 * S.C.Δ * (((s' + S.C.k : ℕ) : Int)))
        (4 * S.C.Δ * (((s + S.C.k : ℕ) : Int))) := by
      have h1' := h1
      simp only [t_eq_mul] at h1'
      omega
    omega
  -- the update of slot `s' + 1` ran before the vote time of slot `s + 1`
  have hcw : supportCutoff S (s' + 1) ≤ supportCutoff S s := by
    rcases Nat.lt_or_eq_of_le (show s' + 1 ≤ s by omega) with h | h
    · exact le_of_lt (supportCutoff_lt_of_lt S h)
    · rw [h]
  -- an entry `e'` of `w`'s state before `t₃ + 1`, between `e_w`'s block and the added one
  obtain ⟨e', he', hd', hB', -⟩ := htr (voteTime S (s + 1) + 1) (by omega) (by omega)
  -- the tick at `t₃`
  obtain ⟨hl₃, -, hti₃'⟩ := stepBefore_spec x hDiv (by omega : 1 ≤ voteTime S (s + 1))
  obtain ⟨n₃, sent₃, hrun₃, hst₃⟩ := tick_step_outcome x hl₃ hw₃.1 hw₃.2
  have hA₃ : (tickInputState x (stepBefore x (voteTime S (s + 1))) (voteTime S (s + 1)) w).A =
      (stateBefore x (voteTime S (s + 1)) w).A := (tickInputState_frame x _ _ w).2.1
  have hS₃ : (tickInputState x (stepBefore x (voteTime S (s + 1))) (voteTime S (s + 1)) w).S =
      (stateBefore x (voteTime S (s + 1)) w).S := (tickInputState_frame x _ _ w).1
  obtain ⟨A', hRevoke, hlock₃⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem13_tick_revokes_locks S.C S.P S.X _ n₃ _ sent₃
      hrun₃ (by rw [hslot₃, voteTime_cast]) (by rw [hslot₃]; exact hDuty)
  rw [hslot₃, hA₃, hS₃] at hRevoke
  -- `e'` is an entry the revocation left
  have hK := stateBefore_succ_keepsConfirmation x hDiv w hti₃'
  have he'A : e' ∈ A'.lock_entries := by
    rw [← hlock₃, ← hst₃, ← hK.1]
    exact he'
  -- `e'` is live at `t₃`
  have hlive : is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
      ((voteTime S (s + 1) : ℕ) : Int) e' = true := by
    simp only [is_live_iff]
    refine ⟨?_, revoke_locks_entry_mem_tree (Nat.le_add_left 1 s) hRevoke e' he'A⟩
    have h1 : ((voteTime S (s + 1) : ℕ) : Int) < ((supportCutoff S (s + 1) + 1 : ℕ) : Int) :=
      Int.ofNat_lt.2 (by omega)
    rw [hd']
    exact lt_trans h1 hlive_w
  have hC : e'.B.compatible e_v.B = true := hLocks A' hRevoke e' he'A hlive
  have hC' : e_w.B.compatible e_v.B = true := compatible_of_ancestorEq_compatible hB' hC
  exact (compatible_iff _ _).2 ((compatible_iff _ _).1 hC').symm

end GoldilocksCorrectness.Proofs.Executions
