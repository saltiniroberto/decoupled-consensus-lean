module
public import GoldilocksCorrectness.Proofs.Executions.Clock
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.Wiring

@[expose] public section

/-! A node records in `awakeSince` the
time since which it has been awake: a wake sets it to `none` (`wake`, applied inside
`tickInputState` to a validator entering the awake set), the first tick after it writes the tick's
time (`record_awake`), and nothing else writes it. So a validator awake and honest at every time
from `t₀` to `t` starts its tick at `t` with `awakeSince` some time at most `t₀`, when its tick at
`t₀` succeeds.

## What is proved

- per routine: `propose_block_awakeSince`, `attest_awakeSince`, `tick_awakeSince`,
  `receive_awakeSince`, `record_awake_awakeSince_some`;
- per step: `tickInputState_awakeSince_le`, `step_keeps_awakeSince`;
- along an execution: `awakeSince_le_clock` (a stored `awakeSince` is at most the node's clock),
  `awakeSince_keep` (it is kept while the validator is awake at every tick), and the proofs of
  `lem16b_awakeSince_of_awake_throughout` and its corollary `awakeSince_le_dutyWindowStart_b`.

Lemma 16 and its corollary `awakeSince_le_dutyWindowStart`, stated without `hTicks`, could not be
proved from their hypotheses; The forms with
`hTicks`, `lem16b_awakeSince_of_awake_throughout` and `awakeSince_le_dutyWindowStart_b`, are kept
under their names (lemma numbers are append-only).


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (proposal_window_start_zero_le
  proposal_window_start_zero_le_duty)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.bind_any DREBPost.dite
  DREBPost.ite DREBPost.of_outcome DREBPost.pure)

open GoldilocksCorrectness.Proofs.Routines (SlotKeyed)

open GoldilocksCorrectness.Proofs.Routines (on_block_eq record_awake_awakeSince_none
  record_awake_awakeSince_some tick_awakeSince tick_step)

open GoldilocksCorrectness.Proofs.Routines (initial_eq wake_eq)

open GoldilocksCorrectness.Proofs.Routines (receive_awakeSince receive_step)

open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_eq_toNat)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicAction AtomicExec Schedule SignedMsg entrants)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## The routines -/

section Routines

end Routines

/-! ## The times -/

section Times

end Times

/-! ## The steps -/

section Steps

variable {S : Setup V} {Sched : Schedule V}

/-- The node state a tick starts from has `awakeSince` at most its clock, when the validator's
stored state does: a wake writes `none`, and otherwise the stored state is the input.

The variables:
- `x`: the execution; `i`: the step; `t`: the time of the tick; `v`: the validator. -/
theorem tickInputState_awakeSince_le (x : AtomicExec (protocol S) Sched) (i t : ℕ) (v : V)
    -- the stored `awakeSince`, when present, is at most the stored clock
    (h : ∀ τ : Time, (x[i][v].st).awakeSince = some τ → τ ≤ (x[i][v].st).t) (τ : Time)
    (hτ : (tickInputState x i t v).awakeSince = some τ) : τ ≤ (tickInputState x i t v).t := by
  unfold tickInputState at hτ ⊢
  split at hτ
  · simp [wake_eq] at hτ
  · rw [if_neg (by assumption)]
    exact h τ hτ

/-- A stored `awakeSince`, when present, is at most the node's clock, at every step: the initial
value is at most `0`, a tick at `t` writes `t` or keeps a value at most the old clock, and a
delivery keeps both.

The variables:
- `x`: the execution; `i`: the step; `v`: the validator; `τ`: the stored time.

Read aloud: a node never records that it has been awake since a time its clock has not reached. -/
theorem awakeSince_le_clock (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    ∀ τ : Time, (x[i][v].st).awakeSince = some τ → τ ≤ (x[i][v].st).t := by
  induction i with
  | zero =>
      intro τ hτ
      rw [getElem_zero_st, initial_eq] at hτ ⊢
      injection hτ with hτ
      rw [← hτ]
      exact proposal_window_start_zero_le S.C
  | succ i ih =>
      rcases step_cases x i v with h | ⟨t, n', sent, hl, -, hok, h⟩ | ⟨sm, -, -, -, h⟩
      · rw [h]
        exact ih
      · rw [h]
        have hk : SlotKeyed (tickInputState x i t v).A := by
          rw [(tickInputState_frame x i t v).2.1]
          exact slotKeyed_of_exec x i v
        have hin := tickInputState_awakeSince_le x i t v ih
        have hclock : ((tickInputState x i t v).t : Int) ≤ (t : Int) := by
          have h1 : ((x[i][v].clock : ℕ) : Int) ≤ ((x[i].time : ℕ) : Int) := by
            exact_mod_cast Framework.StsMultisetLog.atomic_clock_le_time x i v
          have h2 := (time_of_lbl_tickAllAwake x hl).1
          have h3 : ((x[i].time : ℕ) : Int) ≤ (t : Int) := by exact_mod_cast (by omega)
          exact le_trans (tickInputState_frame x i t v).2.2 (le_trans h1 h3)
        intro τ hτ
        have ht' := (DREBPost.of_outcome (tick_step S.C S.P S.X _ (t : Int) hk) hok).2.2.2
        rw [tick_awakeSince S.C S.P S.X _ n' (t : Int) sent hok] at hτ
        rw [ht']
        cases hn : (tickInputState x i t v).awakeSince with
        | none =>
            rw [record_awake_awakeSince_none hn] at hτ
            injection hτ with hτ
            rw [← hτ]
        | some τ₀ =>
            rw [record_awake_awakeSince_some hn] at hτ
            injection hτ with hτ
            rw [← hτ]
            exact le_trans (hin τ₀ hn) hclock
      · rw [h]
        intro τ hτ
        rw [receive_awakeSince] at hτ
        rw [(receive_step S.C S.P S.X _ sm.msg (slotKeyed_of_exec x i v)).2.2.2]
        exact ih τ hτ

/-- A step keeps a present `awakeSince` of `v` when, if it is a tick, `v` does not enter the awake
set at it: a delivery keeps `awakeSince`, and a tick from the stored state keeps a present value
(`record_awake`).

The variables:
- `x`: the execution; `i`: the step; `v`: the validator; `τ`: the stored time. -/
theorem step_keeps_awakeSince (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V)
    -- if the step is a tick at `t`, `v` is not entering the awake set at `t`
    (hne : ∀ t : ℕ, x.lbl i = AtomicAction.tickAllAwake t → v ∉ entrants Sched t)
    (τ : Time) (hτ : (x[i][v].st).awakeSince = some τ) :
    (x[i + 1][v].st).awakeSince = some τ := by
  rcases step_cases x i v with h | ⟨t, n', sent, hl, -, hok, h⟩ | ⟨sm, -, -, -, h⟩
  · rw [h]
    exact hτ
  · have hin : tickInputState x i t v = x[i][v].st := by
      unfold tickInputState
      rw [if_neg (hne t hl)]
    rw [h, tick_awakeSince S.C S.P S.X _ n' (t : Int) sent hok, hin]
    exact record_awake_awakeSince_some hτ
  · rw [h, receive_awakeSince]
    exact hτ

omit [Fintype V] [RootOrder] in
/-- A validator awake at `t'' − 1` does not enter the awake set at `t''`.

The variables:
- `t''`: the time, at least `1`; `v`: the validator. -/
theorem not_mem_entrants {t'' : ℕ} {v : V} (h1 : 1 ≤ t'')
    (h : v ∈ Sched.awake ((t'' - 1 : ℕ) : Int)) : v ∉ entrants Sched t'' := by
  intro hmem
  have hc : ((t'' - 1 : ℕ) : Int) = (t'' : Int) - 1 := by omega
  rw [hc] at h
  simp only [entrants, Finset.mem_sdiff] at hmem
  exact hmem.2 h

/-- From a configuration at a time `t₀` or later and before `t`, a validator awake at every time
from `t₀` to `t` keeps a present `awakeSince` up to its node state before `t`: no tick in between
is one at which it enters the awake set.

The variables:
- `x`: the execution; `t₀`, `t`: the two times; `v`: the validator; `j`: the configuration;
  `τ`: the stored time. -/
theorem awakeSince_keep (x : AtomicExec (protocol S) Sched) (hDiv : TimeDiverges x.toTrace)
    {t₀ t : ℕ} {v : V}
    -- `v` is awake at every time from `t₀` to `t`
    (hAwake : ∀ t' : ℕ, t₀ ≤ t' → t' ≤ t → v ∈ Sched.awake (t' : Int))
    {j : ℕ} (hj₁ : t₀ ≤ x[j].time) (hj₂ : x[j].time < t) (τ : Time)
    (hτ : (x[j][v].st).awakeSince = some τ) : (stateBefore x t v).awakeSince = some τ := by
  have ht : 1 ≤ t := by omega
  refine rel_getElem_stateBefore x hDiv
    (fun n n' => ∀ τ : Time, n.awakeSince = some τ → n'.awakeSince = some τ)
    (fun _ _ h => h) (fun _ _ _ h h' τ hτ => h' τ (h τ hτ)) ht hj₂ v ?_ τ hτ
  intro i hji hi
  refine step_keeps_awakeSince x i v (fun t'' hl => ?_)
  have h1 := (time_of_lbl_tickAllAwake x hl).1
  have h2 := (time_of_lbl_tickAllAwake x hl).2
  have h3 := (lt_stepBefore_iff x hDiv).1 hi
  have h4 := time_mono x hji
  exact not_mem_entrants (by omega) (hAwake (t'' - 1) (by omega) (by omega))

/-- A validator awake at every time from `t₀ < t` to `t` starts its tick at `t` from its stored
node state before `t`: it is awake at `t − 1`, so it does not enter the awake set at `t`.

The variables:
- `x`: the execution; `t₀`, `t`: the two times; `v`: the validator. -/
theorem tickInputState_stateBefore (x : AtomicExec (protocol S) Sched) {t₀ t : ℕ} {v : V}
    -- `v` is awake at every time from `t₀` to `t`
    (hAwake : ∀ t' : ℕ, t₀ ≤ t' → t' ≤ t → v ∈ Sched.awake (t' : Int)) (ht₀ : t₀ < t) :
    tickInputState x (stepBefore x t) t v = stateBefore x t v := by
  unfold tickInputState stateBefore
  rw [if_neg (not_mem_entrants (by omega) (hAwake (t - 1) (by omega) (by omega)))]

end Steps

/-! ## The wake rule -/

section WakeRule

variable {S : Setup V} {Sched : Schedule V}

/-- A validator awake at every time from `0` to `t > 0` starts its tick at `t` with the initial
`awakeSince`, `proposal_window_start S.C 0`: it never enters the awake set at a tick before `t`,
so every step keeps the initial value.

The variables:
- `x`: the execution; `t`: the time; `v`: the validator. -/
theorem awakeSince_of_awake_from_zero (x : AtomicExec (protocol S) Sched)
    (hDiv : TimeDiverges x.toTrace) {t : ℕ} {v : V} (ht : 0 < t)
    -- `v` is awake at every time from `0` to `t`
    (hAwake : ∀ t' : ℕ, 0 ≤ t' → t' ≤ t → v ∈ Sched.awake (t' : Int)) :
    (tickInputState x (stepBefore x t) t v).awakeSince =
      some (proposal_window_start S.C 0) := by
  rw [tickInputState_stateBefore x hAwake ht]
  have h0 : x[0].time = 0 := x.init.1
  refine awakeSince_keep x hDiv hAwake (j := 0) (by omega) (by omega) _ ?_
  rw [getElem_zero_st, initial_eq]

/-- A validator awake at every time from `t₀ ≥ 1` to `t > t₀` and honest at `t₀` starts its tick at
`t` with `awakeSince` some time at most `t₀`: the tick at `t₀` leaves
`t₀` (when it starts from an absent value, as after a wake) or a value at most its clock, which is
before `t₀`; no later tick before `t` is one at which `v` enters the awake set.

The variables:
- `x`: the execution; `t₀`, `t`: the two times; `v`: the validator. -/
theorem awakeSince_of_awake_from_tick (x : AtomicExec (protocol S) Sched)
    (hDiv : TimeDiverges x.toTrace) {t₀ t : ℕ} {v : V} (h1 : 1 ≤ t₀) (ht₀ : t₀ < t)
    -- `v` is awake at every time from `t₀` to `t`
    (hAwake : ∀ t' : ℕ, t₀ ≤ t' → t' ≤ t → v ∈ Sched.awake (t' : Int))
    -- `v` is outside the adversary set at `t₀`
    (hHonest₀ : v ∉ Sched.adv (t₀ : Int)) :
    ∃ τ : Time, (tickInputState x (stepBefore x t) t v).awakeSince = some τ ∧
      τ ≤ (t₀ : Int) := by
  obtain ⟨hl, hT1, hT2⟩ := stepBefore_spec x hDiv h1
  have hv : v ∈ Sched.awake (t₀ : Int) := hAwake t₀ le_rfl ht₀.le
  obtain ⟨n', sent, hres, hst⟩ := tick_step_outcome x hl hv hHonest₀
  have haw := tick_awakeSince S.C S.P S.X _ n' (t₀ : Int) sent hres
  obtain ⟨τ', hτ', hle⟩ : ∃ τ' : Time,
      (x[stepBefore x t₀ + 1][v].st).awakeSince = some τ' ∧ τ' ≤ (t₀ : Int) := by
    rw [hst, haw]
    cases hn : (tickInputState x (stepBefore x t₀) t₀ v).awakeSince with
    | none => exact ⟨t₀, record_awake_awakeSince_none hn, le_rfl⟩
    | some τ₀ =>
        refine ⟨τ₀, record_awake_awakeSince_some hn, ?_⟩
        have h := tickInputState_awakeSince_le x _ t₀ v (awakeSince_le_clock x _ v) τ₀ hn
        have hc : ((x[stepBefore x t₀][v].clock : ℕ) : Int) ≤
            ((x[stepBefore x t₀].time : ℕ) : Int) := by
          exact_mod_cast Framework.StsMultisetLog.atomic_clock_le_time x (stepBefore x t₀) v
        have h3 : ((x[stepBefore x t₀].time : ℕ) : Int) ≤ (t₀ : Int) := by
          exact_mod_cast (by omega)
        exact le_trans h (le_trans (tickInputState_frame x _ t₀ v).2.2 (le_trans hc h3))
  refine ⟨τ', ?_, hle⟩
  rw [tickInputState_stateBefore x hAwake ht₀]
  exact awakeSince_keep x hDiv hAwake (j := stepBefore x t₀ + 1) (by omega) (by omega) τ' hτ'

/-- **Lemma 16b, the wake rule from awakeness.** The proof; the
audited statement is in `Statements/Executions/WakeStatements.lean`. -/
theorem lem16b_awakeSince_of_awake_throughout (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t₀ t : ℕ) (v : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (ht₀ : t₀ < t)
    (hAwake : ∀ t' : ℕ, t₀ ≤ t' → t' ≤ t → v ∈ Sched.awake (t' : Int))
    (hHonest : v ∉ Sched.adv (t : Int)) :
    ∃ τ : Time, (tickInputState x (stepBefore x t) t v).awakeSince = some τ ∧
      τ ≤ (t₀ : Int) ∧ (t₀ = 0 → τ = proposal_window_start S.C 0) := by
  rcases Nat.eq_zero_or_pos t₀ with rfl | h1
  · exact ⟨_, awakeSince_of_awake_from_zero x hDiv ht₀ hAwake,
      by rw [Nat.cast_zero]; exact proposal_window_start_zero_le S.C, fun _ => rfl⟩
  · have hHonest₀ : v ∉ Sched.adv (t₀ : Int) := fun h =>
      hHonest (hMono _ _ (by exact_mod_cast ht₀.le) h)
    obtain ⟨τ, hτ, hle⟩ := awakeSince_of_awake_from_tick x hDiv h1 ht₀ hAwake hHonest₀
    exact ⟨τ, hτ, hle, fun h => absurd h (by omega)⟩

/-- **The wake rule passes the duty test.** The proof; the audited
statement is in `Statements/Executions/WakeStatements.lean`. -/
theorem awakeSince_le_dutyWindowStart_b (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s' t : ℕ) (v : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (ht : dutyWindowStart S s' < t)
    (hAwake : ∀ t' : ℕ, dutyWindowStart S s' ≤ t' → t' ≤ t → v ∈ Sched.awake (t' : Int))
    (hHonest : v ∉ Sched.adv (t : Int)) :
    ∃ τ : Time, (tickInputState x (stepBefore x t) t v).awakeSince = some τ ∧
      τ ≤ duty_window_start S.C s' := by
  obtain ⟨τ, hτ, hle, h0⟩ := lem16b_awakeSince_of_awake_throughout S Sched x
    (dutyWindowStart S s') t v hDiv hMono ht hAwake hHonest
  refine ⟨τ, hτ, ?_⟩
  by_cases hd : 0 ≤ duty_window_start S.C s'
  · have hc : ((dutyWindowStart S s' : ℕ) : Int) = duty_window_start S.C s' := by
      rw [dutyWindowStart_eq_toNat]; exact Int.toNat_of_nonneg hd
    rw [hc] at hle
    exact hle
  · have hz : dutyWindowStart S s' = 0 := by
      rw [dutyWindowStart_eq_toNat]; exact Int.toNat_eq_zero.mpr (not_le.mp hd).le
    rw [h0 hz]
    exact proposal_window_start_zero_le_duty S.C s'

/-- A tick input with a present `awakeSince` is the validator's stored state: a validator
entering the awake set starts from the woken state, whose `awakeSince` is absent.

The variables:
- `x`: the execution; `i`: the step; `t`: the time of the tick; `v`: the validator;
  `τ`: the stored time. -/
theorem tickInputState_eq_of_awakeSince_some (x : AtomicExec (protocol S) Sched) (i t : ℕ)
    (v : V) (τ : Time) (hτ : (tickInputState x i t v).awakeSince = some τ) :
    v ∉ entrants Sched t ∧ tickInputState x i t v = x[i][v].st := by
  unfold tickInputState at hτ ⊢
  split at hτ
  · simp [wake_eq] at hτ
  · rename_i hne
    exact ⟨hne, if_neg hne⟩

/-- **`awakeSince` is kept while the validator stays awake.** The proof; the audited statement is
in `Statements/Executions/WakeStatements.lean`. -/
theorem awakeSince_kept_of_awake_throughout (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t₀ t : ℕ) (v : V) (τ : Time)
    (hDiv : TimeDiverges x.toTrace)
    (ht : t₀ ≤ t)
    (hτ : (tickInputState x (stepBefore x t₀) t₀ v).awakeSince = some τ)
    (hAwake : ∀ t' : ℕ, t₀ ≤ t' → t' ≤ t → v ∈ Sched.awake (t' : Int)) :
    (tickInputState x (stepBefore x t) t v).awakeSince = some τ := by
  rcases Nat.eq_or_lt_of_le ht with rfl | hlt
  · exact hτ
  obtain ⟨hne, heq⟩ := tickInputState_eq_of_awakeSince_some x _ t₀ v τ hτ
  rw [heq] at hτ
  rw [tickInputState_stateBefore x hAwake hlt]
  rcases Nat.eq_zero_or_pos t₀ with rfl | h1
  · have h0 : x[0].time = 0 := x.init.1
    rw [stepBefore_zero] at hτ
    exact awakeSince_keep x hDiv hAwake (j := 0) (by omega) (by omega) τ hτ
  · obtain ⟨hl, -, hT2⟩ := stepBefore_spec x hDiv h1
    have hτ' : (x[stepBefore x t₀ + 1][v].st).awakeSince = some τ := by
      refine step_keeps_awakeSince x _ v (fun t'' hl' => ?_) τ hτ
      have h := hl.symm.trans hl'
      injection h with h
      rw [← h]
      exact hne
    exact awakeSince_keep x hDiv hAwake (j := stepBefore x t₀ + 1) (by omega) (by omega) τ hτ'

/-- A validator whose stored node state at a step has `awakeSince = some τ`, and that is awake and
outside the adversary set at that step's time, is awake at every time from `τ` to that time: a
validator asleep at a time from `τ` on would have entered the awake set later, and the wake would
have erased `awakeSince`, the first tick after it recording a time after the sleep.

The variables:
- `x`: the execution; `i`: the step; `v`: the validator; `τ`: the stored time.

Read aloud: a node that records it has been awake since `τ`, and is awake and honest now, has been
awake at every time since `τ`. -/
theorem awake_of_stored_awakeSince (x : AtomicExec (protocol S) Sched)
    (hMono : Sched.MonotoneCorruption) (i : ℕ) (v : V) :
    ∀ τ : Time, (x[i][v].st).awakeSince = some τ →
      v ∈ Sched.awake ((x[i].time : ℕ) : Int) → v ∉ Sched.adv ((x[i].time : ℕ) : Int) →
      ∀ t' : ℕ, τ ≤ (t' : Int) → t' ≤ x[i].time → v ∈ Sched.awake (t' : Int) := by
  induction i with
  | zero =>
      intro τ _ hv _ t' _ ht'
      have h0 : x[0].time = 0 := x.init.1
      have ht0 : t' = 0 := by omega
      rw [ht0]
      rw [h0] at hv
      exact hv
  | succ i ih =>
      intro τ hτ hv hh t' hτt' ht'
      cases hl : x.lbl i with
      | tickAllAwake t =>
          obtain ⟨hT1, hT2⟩ := time_of_lbl_tickAllAwake x hl
          rw [hT2] at hv hh
          replace ht' : t' ≤ t := le_of_le_of_eq ht' hT2
          have hmem : v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int) :=
            Finset.mem_sdiff.2 ⟨hv, hh⟩
          obtain ⟨n', sent, hok, hst⟩ := tick_step_outcome x hl hv hh
          rw [hst] at hτ
          -- the stored state's `awakeSince` after the tick: `some t`, or the input's
          have hcase : τ = (t : Int) ∨ (tickInputState x i t v).awakeSince = some τ := by
            rw [tick_awakeSince S.C S.P S.X _ n' (t : Int) sent hok] at hτ
            cases hn : (tickInputState x i t v).awakeSince with
            | none =>
                rw [record_awake_awakeSince_none hn] at hτ
                injection hτ with hτ
                exact Or.inl hτ.symm
            | some τ₀ =>
                rw [record_awake_awakeSince_some hn] at hτ
                exact Or.inr (hτ ▸ rfl)
          rcases hcase with hτt | hin
          · have h1 : ((t : ℕ) : Int) ≤ (t' : Int) := hτt ▸ hτt'
            have h2 : t ≤ t' := by exact_mod_cast h1
            have : t' = t := by omega
            rw [this]
            exact hv
          · obtain ⟨hne, heq⟩ := tickInputState_eq_of_awakeSince_some x i t v τ hin
            rw [heq] at hin
            rcases Nat.lt_or_ge t' t with hlt | hge
            · -- `v` is awake at `t − 1`, since it does not enter the awake set at `t`
              have hprev : v ∈ Sched.awake ((t : Int) - 1) := by
                by_contra hc
                exact hne (Finset.mem_sdiff.2 ⟨hmem, hc⟩)
              have hprev' : v ∈ Sched.awake ((x[i].time : ℕ) : Int) := by
                have : ((x[i].time : ℕ) : Int) = (t : Int) - 1 := by omega
                rw [this]
                exact hprev
              have hh' : v ∉ Sched.adv ((x[i].time : ℕ) : Int) := fun h =>
                hh (hMono _ _ (by omega) h)
              exact ih τ hin hprev' hh' t' hτt' (by omega)
            · have : t' = t := by omega
              rw [this]
              exact hv
      | deliver p m =>
          have hT : x[i + 1].time = x[i].time :=
            time_succ_of_not_tickAllAwake x (fun t h => by rw [hl] at h; cases h)
          rw [hT] at hv hh ht'
          have hkeep : (x[i + 1][v].st).awakeSince = (x[i][v].st).awakeSince := by
            rcases step_cases x i v with h | ⟨t, -, -, hl', -⟩ | ⟨sm, -, -, -, h⟩
            · rw [h]
            · rw [hl] at hl'
              cases hl'
            · rw [h, receive_awakeSince]
          rw [hkeep] at hτ
          exact ih τ hτ hv hh t' hτt' ht'
      | _ =>
          have hT : x[i + 1].time = x[i].time :=
            time_succ_of_not_tickAllAwake x (fun t h => by rw [hl] at h; cases h)
          rw [hT] at hv hh ht'
          have hkeep : (x[i + 1][v].st).awakeSince = (x[i][v].st).awakeSince := by
            rcases step_cases x i v with h | ⟨t, -, -, hl', -⟩ | ⟨sm, hl', -, -, -⟩
            · rw [h]
            · rw [hl] at hl'
              cases hl'
            · rw [hl] at hl'
              cases hl'
          rw [hkeep] at hτ
          exact ih τ hτ hv hh t' hτt' ht'

/-- A validator whose tick at `t ≥ 1` starts with `awakeSince = some τ`, and that is awake and
outside the adversary set at `t`, is awake at every time from `τ` to `t`: its tick input is its
stored state before `t`, it is awake at `t − 1` (it does not enter the awake set at `t`), and
`awake_of_stored_awakeSince` applies there.

The variables:
- `x`: the execution; `t`: the time of the tick; `v`: the validator; `τ`: the stored time.

Read aloud: a validator whose tick at `t` records it has been awake since `τ`, awake and honest at
`t`, has been awake at every time from `τ` to `t`. -/
theorem awake_of_tickInput_awakeSince (x : AtomicExec (protocol S) Sched)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption) {t : ℕ} {v : V}
    {τ : Time} (h1 : 1 ≤ t)
    (hτ : (tickInputState x (stepBefore x t) t v).awakeSince = some τ)
    (hv : v ∈ Sched.awake (t : Int)) (hh : v ∉ Sched.adv (t : Int)) :
    ∀ t' : ℕ, τ ≤ (t' : Int) → t' ≤ t → v ∈ Sched.awake (t' : Int) := by
  intro t' hτt' ht'
  obtain ⟨hne, heq⟩ := tickInputState_eq_of_awakeSince_some x _ t v τ hτ
  rw [heq] at hτ
  rcases Nat.lt_or_ge t' t with hlt | hge
  · obtain ⟨-, hT1, -⟩ := stepBefore_spec x hDiv h1
    have hprev : v ∈ Sched.awake ((t : Int) - 1) := by
      by_contra hc
      exact hne (Finset.mem_sdiff.2 ⟨Finset.mem_sdiff.2 ⟨hv, hh⟩, hc⟩)
    have hprev' : v ∈ Sched.awake ((x[stepBefore x t].time : ℕ) : Int) := by
      have : ((x[stepBefore x t].time : ℕ) : Int) = (t : Int) - 1 := by omega
      rw [this]
      exact hprev
    have hh' : v ∉ Sched.adv ((x[stepBefore x t].time : ℕ) : Int) := fun h =>
      hh (hMono _ _ (by omega) h)
    exact awake_of_stored_awakeSince x hMono _ v τ hτ hprev' hh' t' hτt' (by omega)
  · have : t' = t := by omega
    rw [this]
    exact hv

end WakeRule

end GoldilocksCorrectness.Proofs.Executions
