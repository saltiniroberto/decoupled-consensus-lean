module
public import GoldilocksCorrectness.Proofs.Executions.Lemma43

@[expose] public section

/-!
# Lemma 44: after `GST` plus `L`, every two live honest locks are compatible

The proof of `lem44_live_locks_compatible_from_GST_plus_L`, stated in
`GoldilocksCorrectness/Statements/Executions/HealingStatements.lean`.

The route: Lemma 39 gives each entry's slot `s'`, with the deadline
`S.C.t_ (s' + S.C.k) + 5 · S.C.Δ`; the entry is live at `t`, at or after the vote time of slot
`s₁ + S.C.k`, so `s₁ ≤ s'` (Lemma 41), which is the deadline bound of Lemma 43; then Lemma 43.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (t_le_of_le)

open GoldilocksCorrectness.Proofs.Routines (is_live_iff)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

variable {S : Setup V} {Sched : Schedule V}

/-- A lock entry of `v`'s node state before `t`, live at `t`, with `t` at or after the vote time
of slot `s₁ + S.C.k`, has a deadline at least that of a lock of slot `s₁`: it is a lock of a slot
`s'` (Lemma 39) with `s₁ ≤ s'` (Lemma 41).

The variables:
- `x`: the execution; `s₁`: the slot; `t`: the time; `v`: the validator; `e`: the lock entry.

Read aloud: a lock still live `S.C.k` slots after `s₁` was made at `s₁` or later. -/
theorem deadline_ge_of_live_after (x : AtomicExec (protocol S) Sched)
    (hDiv : TimeDiverges x.toTrace) (s₁ t : ℕ) (v : V) (e : LockEntry V)
    (ht : voteTime S (s₁ + S.C.k) ≤ t)
    (he : e ∈ (stateBefore x t v).A.lock_entries)
    (hlive : is_live (fg_to_ac (stateBefore x t v).S) (t : Int) e = true) :
    S.C.t_ (s₁ + S.C.k) + 5 * S.C.Δ ≤ e.d := by
  obtain ⟨s', hd, -⟩ :=
    GoldilocksCorrectness.Proofs.Executions.lem39_lock_entry_provenance S Sched x t v e hDiv he
  have hl : (t : Int) < e.d ∧ e.B ∈ (fg_to_ac (stateBefore x t v).S).tree := by
    exact (is_live_iff _ _ _).1 hlive
  have hb := GoldilocksCorrectness.Proofs.Executions.lem41_slot_of_live_entry S s₁ s' t e hd hl.1
    ht
  rw [hd]
  exact Int.add_le_add_right (t_le_of_le S (show s₁ + S.C.k ≤ s' + S.C.k by omega)) _

/-- **Lemma 44, after `GST` plus `L`, every two live honest locks are compatible.** The proof;
the audited statement is in `Statements/Executions/HealingStatements.lean`.

Roots name blocks until `t`: Lemma 43, which the proof calls, takes blocks as held up to `t`. -/
theorem lem44_live_locks_compatible_from_GST_plus_L (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST s₁ s t : ℕ) (v w : V) (e_v e_w : LockEntry V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x t)
    (hParent : ParentHeldAtDelivery S Sched x)
    (hGST : GST ≤ voteTime S s₁)
    (ht : voteTime S (s₁ + S.C.k) ≤ t)
    (hst : slotStart S s ≤ t)
    (hv : ∀ t' : ℕ, dutyWindowStart S s ≤ t' → t' ≤ t →
      v ∈ Sched.awake (t' : Int) ∧ v ∉ Sched.adv (t' : Int))
    (hw : ∀ t' : ℕ, dutyWindowStart S s ≤ t' → t' ≤ t →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    (he_v : e_v ∈ (stateBefore x t v).A.lock_entries)
    (hlive_v : is_live (fg_to_ac (stateBefore x t v).S) (t : Int) e_v = true)
    (he_w : e_w ∈ (stateBefore x t w).A.lock_entries)
    (hlive_w : is_live (fg_to_ac (stateBefore x t w).S) (t : Int) e_w = true)
    (hFwv : (stateBefore x t w).S.F.compatible e_v.B = true)
    (hFvw : (stateBefore x t v).S.F.compatible e_w.B = true) :
    e_v.B.compatible e_w.B = true :=
  GoldilocksCorrectness.Proofs.Executions.lem43_live_locks_after_GST_compatible S Sched x GST s₁ s
    t v w e_v e_w hDiv hMono hSync hCatch hRoots hParent hGST hst hv hw he_v hlive_v
    (deadline_ge_of_live_after x hDiv s₁ t v e_v ht he_v hlive_v) he_w hlive_w
    (deadline_ge_of_live_after x hDiv s₁ t w e_w ht he_w hlive_w) hFwv hFvw

end GoldilocksCorrectness.Proofs.Executions
