module
public import GoldilocksCorrectness.Proofs.Executions.Lemma39
public import GoldilocksCorrectness.Proofs.Executions.Lemma40
public import GoldilocksCorrectness.Proofs.Executions.Lemma41

@[expose] public section

/-!
# Where lock entries and saved confirmations come from

The audited statements about the provenance of a validator's lock entries and saved
confirmations over an execution, and the arithmetic of a live lock entry's slot: Lemma 39,
`lem39_lock_entry_provenance`, every lock entry was added by the holder's confirmation update of
the slot its deadline names; Lemma 40, `lem40_saved_confirmation_provenance`, every saved
confirmation was saved by the holder's update of the next slot and kept since; Lemma 41,
`lem41_slot_of_live_entry`, a lock entry still live `C.k` slots after a slot `s₀` is a lock of a
slot at least `s₀`. Each is proved in its own file under
`GoldilocksCorrectness/Proofs/Executions/`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (voteTime supportCutoff)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 39, where a lock entry comes from.** In an execution that reaches every time, every
lock entry `e` of `v`'s node state before `t` was added by `v`'s confirmation update of the slot
`s` its deadline names. Write `c` for the support cutoff of slot `s + 1`. The deadline of `e` is
`S.C.t_ (s + S.C.k) + 5 · S.C.Δ`, and `c` is before `t`; `v`'s tick at `c` starts from a state
whose `awakeSince` is some time at most the duty window's start of slot `s + 1`, so the duty test
passed; the confirmation update of slot `s + 1` on `v`'s state before `c`, its expired lock
entries removed, answers some `A'` holding an entry `e₀` with the deadline of `e`, on a block of
the frame's tree other than the genesis block that is the saved confirmation of slot `s` or an
ancestor of it, and that block is a fast block of `A'` or passes the slow test of the update;
and at every time `t'` after `c` up to `t`, `v`'s node state before `t'` holds an entry with the
deadline of `e` whose block is the block of `e` or a descendant of it, and the block of `e₀` or
an ancestor of it.

Why: the lock entries are empty initially; a step keeps a subset of them, or, at the vote time,
the revocation moves live entries to ancestors keeping their deadlines (Lemma 38), or, at the
support cutoff with the duty test passing, the confirmation update deletes none and adds at most
one entry, with the slot's deadline and the block facts of Lemma 35. Each entry is traced along
the steps by an invariant proved by induction on the step.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator;
- `e`: the lock entry; `s`: the slot of the lock; `A'`: the update's answer; `e₀`: the entry it
  added; `C'`: the saved confirmation of slot `s`.

Read aloud: every lock entry `v` holds before `t` was added by `v`'s update of the slot `s` its
deadline names, run at the support cutoff of slot `s + 1` with the duty test passing, on a
non-genesis block of `v`'s frame tree then that is the saved confirmation of slot `s` or an
ancestor of it, fast or passing the slow test; and at every time from then to `t`, `v` holds an
entry with that deadline whose block is the entry's block or a descendant of it, and the added
block or an ancestor of it. -/
theorem lem39_lock_entry_provenance (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) (e : LockEntry V)
    -- the execution reaches every time
    (hDiv : TimeDiverges x.toTrace)
    -- `e` is a lock entry of `v`'s node state before `t`
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
              e'.B.AncestorEq e₀.B :=
  GoldilocksCorrectness.Proofs.Executions.lem39_lock_entry_provenance S Sched x t v e hDiv he

/-- **Lemma 40, where a saved confirmation comes from.** In an execution that reaches every
time, a block `C'` saved as the confirmation of slot `s'` on `v`'s node state before `t` was saved
by `v`'s confirmation update of slot `s' + 1`. Write `c` for the support cutoff of slot `s' + 1`.
Then `c` is before `t`; `v`'s tick at `c` starts from a state whose `awakeSince` is some time at
most the duty window's start of slot `s' + 1`, so the duty test passed; the confirmation update of
slot `s' + 1` on `v`'s state before `c`, its expired lock entries removed, answers some `A'` that
saves `C'` as the confirmation of slot `s'`; and at every time `t'` after `c` up to `t`, `v`'s
node state before `t'` has `C'` saved as the confirmation of slot `s'`.

Why: the saved confirmation of slot `s'` is `none` initially, and the only step that changes it is
`v`'s tick at `c`, running the update of slot `s' + 1` with the duty test passing: a tick writes it
only through the update of the slot of its time, which writes the saved confirmation of the slot
before only; every time has one tick.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator;
- `s'`: the slot of the confirmation; `C'`: the block saved; `A'`: the update's answer.

Read aloud: a saved confirmation of slot `s'` on `v`'s state before `t` was saved by `v`'s update of
slot `s' + 1`, run at the support cutoff of slot `s' + 1` with the duty test passing, and the field
keeps that value from then to `t`. -/
theorem lem40_saved_confirmation_provenance (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) (s' : ℕ) (C' : Block V)
    -- the execution reaches every time
    (hDiv : TimeDiverges x.toTrace)
    -- `v`'s node state before `t` has `C'` saved as the confirmation of slot `s'`
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
        (stateBefore x t' v).A.saved_confirmation s' = some C' :=
  GoldilocksCorrectness.Proofs.Executions.lem40_saved_confirmation_provenance S Sched x t v s' C'
    hDiv hSaved

omit [RootOrder] in
/-- **Lemma 41, the slot of a live lock entry.** A lock entry `e` with the deadline of a lock of
slot `s`, `S.C.t_ (s + S.C.k) + 5 · S.C.Δ`, whose deadline is after a time `t` that is at or after
the vote time of slot `s₀ + S.C.k`, is a lock of a slot `s` at least `s₀`.

Why: the vote time of slot `s₀ + S.C.k` is `4 · S.C.Δ · (s₀ + S.C.k) + S.C.Δ` and the deadline is
`4 · S.C.Δ · (s + S.C.k) + 5 · S.C.Δ`; a time at or after the first and strictly before the second
gives `s₀ + S.C.k < s + S.C.k + 1`, since `S.C.Δ` is positive.

The variables:
- `S`: the setup; `s₀`: the slot whose vote time `S.C.k` slots later bounds `t`; `s`: the slot of
  the lock; `t`: the time; `e`: the lock entry.

Read aloud: an entry with the deadline of a slot-`s` lock, whose deadline is after a time `t` at or
after the vote time of slot `s₀ + C.k`, is of a slot `s ≥ s₀`. -/
theorem lem41_slot_of_live_entry (S : Setup V) (s₀ s t : ℕ) (e : LockEntry V)
    -- `e` has the deadline of a lock of slot `s`
    (hd : e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    -- the deadline of `e` is after `t`
    (hlive : (t : Int) < e.d)
    -- `t` is at or after the vote time of slot `s₀ + S.C.k`
    (ht : voteTime S (s₀ + S.C.k) ≤ t) :
    s₀ ≤ s :=
  GoldilocksCorrectness.Proofs.Executions.lem41_slot_of_live_entry S s₀ s t e hd hlive ht

end GoldilocksCorrectness.Statements.Executions
