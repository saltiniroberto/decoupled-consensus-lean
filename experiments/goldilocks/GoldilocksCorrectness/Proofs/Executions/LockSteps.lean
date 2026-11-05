module
public import GoldilocksCorrectness.Proofs.Routines.Lemma15
public import GoldilocksCorrectness.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Proofs.Executions.Steps
public import GoldilocksCorrectness.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Proofs.Routines.Locks
public import GoldilocksCorrectness.Proofs.Routines.ACInterfaceTick
public import GoldilocksCorrectness.Proofs.Routines.NodeTick

@[expose] public section

/-!

## What is proved

- per routine: `revoke_locks_zero` and `update_confirmation_zero`, both answer their input at
  slot `0`; `revoke_locks_saved`, the revocation keeps the saved confirmations;
  `update_confirmation_saved_ne`, the update of slot `s` writes the saved confirmation of slot
  `s − 1` only;
- `awakeSince_of_record_awake`, the duty test reads a present `awakeSince` when the time it
  compares with is before the tick;
- per tick: `ac_on_tick_cases`, `tick_cases`, the three things a tick does to the two fields;
- per step: `step_cases_lock_saved`, the same over a step of an execution;
  `step_saved_changed`, a step that changes the saved confirmation of slot `j` is the tick at the
  support cutoff of slot `j + 1`.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (supportCutoff_cast)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.ite DREBPost.liftM
  DREBPost.pure DREPost DREPost.bind_any DREPost.dite DREPost.ite DREPost.pure)

open GoldilocksCorrectness.Proofs.Routines (revoke_locks_saved update_confirmation_saved_ne
  update_confirmation_zero)

open GoldilocksCorrectness.Proofs.Routines (tick_cases)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (KeepsConfirmation tick_ac_on_tick voteTime_ne_cutoff
  goldfish_vote_keepsConfirmation receive_keeps_confirmation)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The routines -/

section Routines

end Routines

/-! ## The tick -/

section Tick

variable [RootOrder]

end Tick

/-! ## The steps -/

section Steps

variable [RootOrder] {S : Setup V} {Sched : Schedule V}

/-- What a step does to a validator's saved confirmations and lock entries, in three cases: it
keeps the saved confirmations and keeps a subset of the lock entries; or it is the tick of every
awake validator at a time `t` at which the validator is awake and honest, `t` is the vote time of
its slot, and the step keeps the saved confirmations and leaves the lock entries of the
revocation of that slot on the validator's AC state with its expired entries removed; or it is
that tick at the support cutoff of its slot, the tick starts from a state whose `awakeSince` is
some time at most the duty window's start of that slot, and the step leaves the saved
confirmations and the lock entries of the confirmation update of that slot on the validator's AC
state with its expired entries removed.

The variables:
- `x`: the execution; `i`: the step; `v`: the validator.

Read aloud: only the validator's own revocation and confirmation update, at their times, write
its lock entries beyond deleting some, and only the update writes its saved confirmations. -/
theorem step_cases_lock_saved (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    ((x[i + 1][v].st).A.saved_confirmation = (x[i][v].st).A.saved_confirmation ∧
      (x[i + 1][v].st).A.lock_entries ⊆ (x[i][v].st).A.lock_entries) ∨
    (∃ t : ℕ, x.lbl i = AtomicAction.tickAllAwake t ∧
      v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int) ∧
      (t : Int) = S.C.t_ (S.C.slot t) + S.C.Δ ∧ ∃ A' : ACState V,
        revoke_locks S.P (expireLocks (x[i][v].st).A t) (fg_to_ac (x[i][v].st).S) t
          (S.C.slot t) = .ok A' ∧
        (x[i + 1][v].st).A.saved_confirmation = (x[i][v].st).A.saved_confirmation ∧
        (x[i + 1][v].st).A.lock_entries = A'.lock_entries) ∨
    (∃ t : ℕ, x.lbl i = AtomicAction.tickAllAwake t ∧
      v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int) ∧
      (t : Int) = S.C.t_ (S.C.slot t) + 2 * S.C.Δ ∧
      (∃ τ : Time, (tickInputState x i t v).awakeSince = some τ ∧
        τ ≤ duty_window_start S.C (S.C.slot t)) ∧
      ∃ A'' : ACState V,
        update_confirmation S.C S.P (expireLocks (x[i][v].st).A t) (fg_to_ac (x[i][v].st).S) t
          (S.C.slot t) = .ok A'' ∧
        (x[i + 1][v].st).A.saved_confirmation = A''.saved_confirmation ∧
        (x[i + 1][v].st).A.lock_entries = A''.lock_entries) := by
  rcases step_cases x i v with h | ⟨t, n', sent, hl, hmem, hok, h⟩ | ⟨sm, -, -, -, h⟩
  · rw [h]
    exact Or.inl ⟨rfl, subset_refl _⟩
  · obtain ⟨hS, hA, -⟩ := tickInputState_frame x i t v
    rw [h]
    rcases tick_cases S.C S.P S.X _ n' (t : Int) sent hok with
      h1 | ⟨h1, A', hA', h2, h3⟩ | ⟨h1, h2, A'', hA'', h3, h4⟩
    · rw [hA] at h1
      exact Or.inl h1
    · rw [hA, hS] at hA'
      rw [hA] at h2
      exact Or.inr (Or.inl ⟨t, hl, hmem, h1, A', hA', h2, h3⟩)
    · rw [hA, hS] at hA''
      exact Or.inr (Or.inr ⟨t, hl, hmem, h1, h2, A'', hA'', h3, h4⟩)
  · rw [h]
    obtain ⟨h1, h2, -, -⟩ := receive_keeps_confirmation S.C S.P S.X (x[i][v].st) sm.msg
    rw [h1, h2]
    exact Or.inl ⟨rfl, subset_refl _⟩

/-- A step that changes a validator's saved confirmation of slot `j` is the tick of every awake
validator at the support cutoff of slot `j + 1`, at which the validator is awake and honest; that
tick starts from a state whose `awakeSince` is some time at most the duty window's start of slot
`j + 1`, and the step leaves the saved confirmations of the confirmation update of slot `j + 1`
on the validator's state at the step, its expired lock entries removed.

The variables:
- `x`: the execution; `i`: the step; `v`: the validator; `j`: the slot of the confirmation.

Read aloud: only the validator's update of slot `j + 1`, at its time, writes its saved
confirmation of slot `j`. -/
theorem step_saved_changed (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) (j : ℕ)
    -- the step changes the saved confirmation of slot `j`
    (hne : (x[i + 1][v].st).A.saved_confirmation j ≠ (x[i][v].st).A.saved_confirmation j) :
    x.lbl i = AtomicAction.tickAllAwake (supportCutoff S (j + 1)) ∧
      v ∈ Sched.awake (supportCutoff S (j + 1) : Int) \ Sched.adv (supportCutoff S (j + 1) : Int) ∧
      (∃ τ : Time, (tickInputState x i (supportCutoff S (j + 1)) v).awakeSince = some τ ∧
        τ ≤ duty_window_start S.C (j + 1)) ∧
      ∃ A'' : ACState V,
        update_confirmation S.C S.P
          (expireLocks (x[i][v].st).A ((supportCutoff S (j + 1) : ℕ) : Int))
          (fg_to_ac (x[i][v].st).S) ((supportCutoff S (j + 1) : ℕ) : Int) (j + 1) = .ok A'' ∧
        (x[i + 1][v].st).A.saved_confirmation = A''.saved_confirmation := by
  rcases step_cases_lock_saved x i v with ⟨h, -⟩ | ⟨t, -, -, -, -, -, h, -⟩ |
      ⟨t, hl, hmem, ht, hτ, A'', hA'', h, -⟩
  · exact absurd (congrFun h j) hne
  · exact absurd (congrFun h j) hne
  -- the update of the slot of `t` changed slot `j`'s field, so that slot is `j + 1`
  have hframe := update_confirmation_saved_ne S.C S.P _ _ _ _ A'' hA''
  have hs0 : S.C.slot (t : Int) ≠ 0 := by
    intro h0
    rw [h0, update_confirmation_zero] at hA''
    cases hA''
    exact hne (by rw [h]; rfl)
  have hj : j = S.C.slot (t : Int) - 1 := by
    by_contra hj
    exact hne (by rw [h, hframe j hj]; rfl)
  have hslot : S.C.slot (t : Int) = j + 1 := by
    -- `omega` reads facts stated at `Slot`, an `abbrev` of `ℕ`, only once restated at `ℕ`
    have h0 : @Ne ℕ (S.C.slot (t : Int)) 0 := hs0
    have h1 : @Eq ℕ j (S.C.slot (t : Int) - 1) := hj
    show @Eq ℕ (S.C.slot (t : Int)) (j + 1)
    omega
  have htc : t = supportCutoff S (j + 1) := by
    have h1 := supportCutoff_cast S (j + 1)
    rw [hslot] at ht
    have : (t : Int) = ((supportCutoff S (j + 1) : ℕ) : Int) := by rw [h1]; exact ht
    exact_mod_cast this
  subst htc
  rw [hslot] at hA'' hτ
  exact ⟨hl, hmem, hτ, A'', hA'', h⟩

end Steps

end GoldilocksCorrectness.Proofs.Executions
