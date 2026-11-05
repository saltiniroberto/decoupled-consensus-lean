module
public import GoldilocksCorrectness.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Proofs.Routines.TickFrame
public import GoldilocksCorrectness.Proofs.Routines.Schedule

@[expose] public section

/-! Three unnumbered facts the G1 assembly (`Lemma18.lean`) reads:

- `dutyWindowStart_succ_le_slotStart`: the duty window of slot `s + 1` starts no later than slot
  `s` (`S.C.k ≥ 2`);
- `stateBefore_lock_entries_subset`: from a configuration `x[j]` to `v`'s node state before `t`,
  when no tick of the times strictly between `x[j].time` and `t` is at the vote time or the
  support cutoff of its slot, `v` keeps a subset of its lock entries: such a tick only deletes
  entries (`tick_lock_entries_subset`), a failed tick keeps the state, and a delivery keeps them
  (`receive_keeps_confirmation`);
- `stateBefore_succ_keepsConfirmation`: from a configuration `x[j]` at the time `t` to `v`'s node
  state before `t + 1`, `v` keeps its lock entries, saved confirmations, fast blocks and record of
  the confirmed tip: no tick happens in between, and a delivery keeps them.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicAction AtomicExec Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (KeepsConfirmation tick_lock_entries_subset
  receive_keeps_confirmation)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

variable {S : Setup V} {Sched : Schedule V}

/-- From the configuration `x[j]` to `v`'s node state before `t`, `v` keeps a subset of its lock
entries, when no time strictly between `x[j].time` and `t` is the vote time or the support cutoff
of its slot: a tick at such a time deletes entries and adds none (`tick_lock_entries_subset`), a
failed tick keeps the state, and a delivery keeps the entries (`receive_keeps_confirmation`).

The variables:
- `x`: the execution; `v`: the validator; `j`: the step; `t`: the time.

Read aloud: between duty times, a validator's lock entries only shrink. -/
theorem stateBefore_lock_entries_subset (x : AtomicExec (protocol S) Sched)
    (hDiv : TimeDiverges x.toTrace) (v : V) {j t : ℕ} (ht : 1 ≤ t)
    -- the configuration `x[j]` is at a time before `t`
    (hj : x[j].time < t)
    -- no time strictly between is a duty time of its slot
    (hNoDuty : ∀ t'' : ℕ, x[j].time < t'' → t'' < t →
      (t'' : Int) ≠ S.C.t_ (S.C.slot t'') + S.C.Δ ∧
        (t'' : Int) ≠ S.C.t_ (S.C.slot t'') + 2 * S.C.Δ) :
    (stateBefore x t v).A.lock_entries ⊆ (x[j][v].st).A.lock_entries := by
  refine rel_getElem_stateBefore x hDiv (fun n n' => n'.A.lock_entries ⊆ n.A.lock_entries)
    (fun n => Finset.Subset.refl _) (fun _ _ _ h h' => Finset.Subset.trans h' h) ht hj v ?_
  intro i hji hi
  show (x[i + 1][v].st).A.lock_entries ⊆ (x[i][v].st).A.lock_entries
  rcases step_cases x i v with h | ⟨t'', n', sent, hl, -, hok, h⟩ | ⟨sm, -, -, -, h⟩
  · exact h ▸ Finset.Subset.refl _
  · obtain ⟨h1, h2⟩ := time_of_lbl_tickAllAwake x hl
    have hlt : x[i + 1].time < t := (lt_stepBefore_iff x hDiv).1 hi
    have hge : x[j].time ≤ x[i].time := time_mono x hji
    obtain ⟨hnv, hnc⟩ := hNoDuty t'' (by omega) (by omega)
    rw [h, ← (tickInputState_frame x i t'' v).2.1]
    exact tick_lock_entries_subset S.C S.P S.X _ n' _ sent hok hnv hnc
  · rw [h, (receive_keeps_confirmation S.C S.P S.X _ sm.msg).1]

/-- From the configuration `x[j]` at the time `t` to `v`'s node state before `t + 1`, `v` keeps
its lock entries, saved confirmations, fast blocks and record of the confirmed tip: every step in
between is at the time `t`, so none is a tick, and a delivery keeps the four fields
(`receive_keeps_confirmation`).

The variables:
- `x`: the execution; `v`: the validator; `j`: the step; `t`: its time.

Read aloud: nothing after the tick at `t` and before the next one changes a validator's locks or
confirmations. -/
theorem stateBefore_succ_keepsConfirmation (x : AtomicExec (protocol S) Sched)
    (hDiv : TimeDiverges x.toTrace) (v : V) {j t : ℕ}
    -- the configuration `x[j]` is at the time `t`
    (hj : x[j].time = t) :
    KeepsConfirmation (x[j][v].st).A (stateBefore x (t + 1) v).A := by
  refine rel_getElem_stateBefore x hDiv (fun n n' => KeepsConfirmation n.A n'.A)
    (fun n => Routines.KeepsConfirmation.refl _) (fun _ _ _ h h' => h.trans h')
    (Nat.succ_pos t) (by omega) v ?_
  intro i hji hi
  show KeepsConfirmation (x[i][v].st).A (x[i + 1][v].st).A
  have hlt : x[i + 1].time < t + 1 := (lt_stepBefore_iff x hDiv).1 hi
  have hge : x[j].time ≤ x[i].time := time_mono x hji
  rcases step_cases x i v with h | ⟨t'', -, -, hl, -, -, -⟩ | ⟨sm, -, -, -, h⟩
  · rw [h]
    exact Routines.KeepsConfirmation.refl _
  · obtain ⟨h1, h2⟩ := time_of_lbl_tickAllAwake x hl
    omega
  · rw [h]
    exact receive_keeps_confirmation S.C S.P S.X _ sm.msg

end GoldilocksCorrectness.Proofs.Executions
