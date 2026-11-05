module
public import GoldilocksCorrectness.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Proofs.Executions.ConfirmationSteps
public import GoldilocksCorrectness.Proofs.Executions.Lemma39
public import GoldilocksCorrectness.Proofs.Executions.Lemma41
public import GoldilocksCorrectness.Proofs.Routines.Schedule

@[expose] public section

/-!
# The tick at a support cutoff and the state after it

The proofs of the two kit facts `update_state_of_duty` and `update_state_of_lock_entry`, stated in
`GoldilocksCorrectness/Statements/Executions/HonestChainStatements.lean`: the node state right
after the support cutoff `c` of slot `s + 1` holds what the confirmation update of slot `s + 1`
answered on the state before `c`. The first reads it off the tick at `c`, which answers when the
validator is awake and honest; the second off a lock entry of slot `s` held later, which only that
update can have added.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (lockDeadline_injective supportCutoff_cast
  supportCutoff_slot)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (voteTime_ne_cutoff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- The tick-to-update link, the awake form. Write `c` for the support cutoff of slot `s + 1`.
When `v` is awake and honest at `c`, and its tick at `c` starts from a
record of awakeness since the duty window's start of slot `s + 1` or earlier, the update of slot
`s + 1` on `v`'s state before `c`, its expired entries removed, answers some `A''`, and `v`'s state
before `c + 1` has `A''`'s saved confirmations, fast blocks, lock entries and confirmed tip.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the cutoff's
  slot; `v`: the validator. -/
theorem update_state_of_duty (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (v : V)
    (hDiv : TimeDiverges x.toTrace)
    (hv : v ∈ Sched.awake (supportCutoff S (s + 1) : Int) ∧
      v ∉ Sched.adv (supportCutoff S (s + 1) : Int))
    (hAw : ∃ τ : Time, (tickInputState x (stepBefore x (supportCutoff S (s + 1)))
      (supportCutoff S (s + 1)) v).awakeSince = some τ ∧ τ ≤ duty_window_start S.C (s + 1)) :
    ∃ A'' : ACState V,
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A'' ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation =
        A''.saved_confirmation ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.fast_blocks = A''.fast_blocks ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.lock_entries = A''.lock_entries ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.latest_confirmed =
        A''.latest_confirmed := by
  obtain ⟨hslot₂, hc1⟩ := supportCutoff_slot S s
  obtain ⟨hl₂, -, hti₂'⟩ := stepBefore_spec x hDiv hc1
  obtain ⟨n₂, sent₂, hrun₂, hst₂⟩ := tick_step_outcome x hl₂ hv.1 hv.2
  have hA₂ : (tickInputState x (stepBefore x (supportCutoff S (s + 1))) (supportCutoff S (s + 1))
      v).A = (stateBefore x (supportCutoff S (s + 1)) v).A := (tickInputState_frame x _ _ v).2.1
  have hS₂ : (tickInputState x (stepBefore x (supportCutoff S (s + 1))) (supportCutoff S (s + 1))
      v).S = (stateBefore x (supportCutoff S (s + 1)) v).S := (tickInputState_frame x _ _ v).1
  obtain ⟨A'', hUpdate, hsave, hfast, hlocks, hlatest⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem15_tick_updates_confirmation S.C S.P S.X _ n₂ _
      sent₂ hrun₂ (by rw [hslot₂, supportCutoff_cast]) (by rw [hslot₂]; exact hAw)
  rw [hslot₂, hA₂, hS₂] at hUpdate
  have hkeep := stateBefore_succ_keepsConfirmation x hDiv v hti₂'
  rw [hst₂] at hkeep
  obtain ⟨k1, k2, k3, k4⟩ := hkeep
  exact ⟨A'', hUpdate, k2.trans hsave, k3.trans hfast, k1.trans hlocks, k4.trans hlatest⟩

/-- The tick-to-update link, the lock-entry form. Write `c` for the support cutoff of slot
`s + 1`. When `v` holds before `t` a lock entry with the deadline of a lock of slot `s`, and `c` is
before `t`, then `v` was awake and honest at `c`, its tick at `c` started from a record of
awakeness since the duty window's start of slot `s + 1` or earlier, the update of slot `s + 1` on
`v`'s state before `c`, its expired entries removed, answered some `A''`, and `v`'s state before
`c + 1` has `A''`'s saved confirmations and lock entries.

Why: the entry is traced (`lockTraced_of_mem`) to the update of the slot its deadline names,
which is `s`; right after the step `i₀ := stepBefore x c` some entry with that deadline is held,
and none is held at `i₀`, since an entry held there would be traced to an update before `i₀`. So
the step `i₀` changed the lock entries, and of the three cases of `step_cases_lock_saved` only the
update at the support cutoff can: the first keeps a subset, the second adds only entries moved
from held ones with their deadlines, at a vote time, and `i₀` is the tick at `c`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `s`: the slot of the
  lock; `v`: the validator; `e`: the lock entry. -/
theorem update_state_of_lock_entry (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t s : ℕ) (v : V) (e : LockEntry V)
    (hDiv : TimeDiverges x.toTrace)
    (he : e ∈ (stateBefore x t v).A.lock_entries)
    (hd : e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    (hts : supportCutoff S (s + 1) < t) :
    (v ∈ Sched.awake (supportCutoff S (s + 1) : Int) ∧
      v ∉ Sched.adv (supportCutoff S (s + 1) : Int)) ∧
    (∃ τ : Time, (tickInputState x (stepBefore x (supportCutoff S (s + 1)))
      (supportCutoff S (s + 1)) v).awakeSince = some τ ∧ τ ≤ duty_window_start S.C (s + 1)) ∧
    ∃ A'' : ACState V,
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A'' ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation =
        A''.saved_confirmation ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.lock_entries = A''.lock_entries := by
  -- the entry is traced to the update of slot `s + 1`
  obtain ⟨s₂, hd₂, h1, -, A₀, -, e₀, -, -, -, -, -, -, -, htr⟩ :=
    lockTraced_of_mem S Sched x v (stepBefore x t) e he
  have hs₂ : s₂ = s := lockDeadline_injective S (hd₂.symm.trans hd)
  subst hs₂
  -- right after the step `i₀` an entry with `e`'s deadline is held, and none at `i₀`
  obtain ⟨e', he', hd', -, -⟩ := htr (stepBefore x (supportCutoff S (s₂ + 1)) + 1) (by omega) h1
  have hnone : ∀ e'' ∈ (x[stepBefore x (supportCutoff S (s₂ + 1))][v].st).A.lock_entries,
      e''.d ≠ e.d := by
    intro e'' he'' hd''
    obtain ⟨s₃, hd₃, h3, -⟩ := lockTraced_of_mem S Sched x v _ e'' he''
    have hs₃ : s₃ = s₂ := lockDeadline_injective S (hd₃.symm.trans (hd''.trans hd₂))
    subst hs₃
    exact lt_irrefl _ h3
  obtain ⟨hslot, hc1⟩ := supportCutoff_slot S s₂
  obtain ⟨hl, -, hti'⟩ := stepBefore_spec x hDiv hc1
  have hcut : ((supportCutoff S (s₂ + 1) : ℕ) : Int) =
      S.C.t_ (S.C.slot (supportCutoff S (s₂ + 1) : Int)) + 2 * S.C.Δ := by
    rw [hslot, supportCutoff_cast]
  rcases step_cases_lock_saved x (stepBefore x (supportCutoff S (s₂ + 1))) v with
      ⟨-, hsub⟩ | ⟨t₂, hl₂, -, ht₂, -⟩ | ⟨t₃, hl₃, hmem, -, hτ, A'', hA'', hsv, hlk⟩
  · -- a step keeping a subset of the entries
    exact absurd hd' (hnone e' (hsub he'))
  · -- the revocation runs at a vote time, and the step is the tick at the support cutoff
    rw [hl] at hl₂
    injection hl₂ with h
    subst h
    exact absurd hcut (voteTime_ne_cutoff ht₂)
  · -- the update at the support cutoff
    rw [hl] at hl₃
    injection hl₃ with h
    subst h
    rw [hslot] at hτ hA''
    have hkeep := stateBefore_succ_keepsConfirmation x hDiv v hti'
    obtain ⟨k1, k2, -, -⟩ := hkeep
    exact ⟨Finset.mem_sdiff.1 hmem, hτ, A'', hA'', k2.trans hsv, k1.trans hlk⟩

end GoldilocksCorrectness.Proofs.Executions
