module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma12
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickUpdateState

@[expose] public section

/-!
# The per-tick kit, over a model

The theorems that read a validator counted active up to its own tick (`A.activeThroughoutToTick`,
the sets `updaterAt` and `honestActiveAt`) at that tick: the wake test it passes there, the facts of
its state before the support cutoff, its update, and the windows inside its duty window. Moved here
from `Lemma89f.lean` and `PhaseChain.lean` so that the proofs of Lemmas 78 and 32 can read them
; the theorems are unchanged.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)
open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution, and `x[i][v]` into a configuration, has the valid-index
-- predicate `fun _ _ => True`; this rule, local to the file, proves it at once
--. No statement and no proof term
-- changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **The wake test at a tick, for a validator counted up to that tick from a duty window's start.**
A validator in `A.activeThroughoutToTick x (duty_window_start S.C s) b`, the protocol's duty window
start of slot `s` before `b`, ticks to `b` from a node state awake since a time at most that start.

Why: `awakeSince_le_of_mem_activeThroughoutToTick`: the stored wake time is the initial one, at most
every duty window's start (`proposal_window_start_zero_le_duty`), or a time at most the window's
start.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `s`: the slot; `b`: the
  tick's value; `v`: the validator.

Read aloud: a validator active from the duty window's start up to its tick has passed the wake test at
that tick. -/
theorem tickInput_awakeSince_of_mem_activeThroughoutToTick (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V} (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {s b : ℕ} {v : V} (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) b)
    (hb : duty_window_start S.C s < b) :
    ∃ τ : Time, (x.tickInput v b).awakeSince = some τ ∧ τ ≤ duty_window_start S.C s := by
  obtain ⟨τ, hτ, h | h⟩ := (awakeSince_le_of_mem_activeThroughoutToTick M F) x R E hb hv
  · exact ⟨τ, hτ, h ▸ GoldilocksCorrectness.Proofs.Routines.proposal_window_start_zero_le_duty S.C s⟩
  · exact ⟨τ, hτ, h⟩

/-- **The cutoff's state facts, read off the tick.** `cutoff_state_facts_of_active` with `v`'s tick to
the support cutoff `c` of slot `s + 1` in place of `v` active after every step read as `c`: the tick
reads `v`'s state before `c` (no restart between, `no_restart_of_tickInput_awakeSince_some`), which is
awake for slot `s + 1`, satisfies the node invariant, has a clock at most `c`; and `c` is the support
cutoff of slot `s + 1` read as a time.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `hWS`: the trace is
  wake-shaped; `s`: the slot; `v`: the validator; `τ`: the wake time; `i`: the tick's step.

Read aloud: a validator that ticks to the support cutoff awake for its duty ticks from its state before
the cutoff, which the tick's facts can be applied to. -/
theorem cutoff_state_facts_of_tick (U : UniformSchedule M.toSlotLayout) {S : Setup V}
    {A : Activity V} (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
 (s : ℕ) (v : V) (τ : Time) {i : ℕ}
    (hl : x.lbl i = Event.tick v (M.supportCutoff S.C (s + 1)))
    (hτ : (x.tickInput v (M.supportCutoff S.C (s + 1))).awakeSince = some τ)
    (hτle : τ ≤ duty_window_start S.C (s + 1)) :
    GoldilocksCorrectness.Record.Statements.Routines.AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1) ∧
      M.nodeInv S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1))) ∧
      (x.tickInput v (M.supportCutoff S.C (s + 1))).t ≤
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) ∧
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) =
        S.C.t_ (S.C.slot ((M.supportCutoff S.C (s + 1) : ℕ) : Int)) + 2 * S.C.Δ ∧
      S.C.slot ((M.supportCutoff S.C (s + 1) : ℕ) : Int) = s + 1 := by
  -- the tick reads `v`'s state at its own step `i`; `v` is honest there (`tick_active`)
  have hti : x.tickInput v (M.supportCutoff S.C (s + 1)) = x.st i v := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hl]
  have hvi : v ∉ A.corrupted i := E.not_mem_corrupted_of_tick hl
  obtain ⟨hInv, -, hclk⟩ := (lem11_node_invariant M F S A x R E i v) hvi
  -- the slot of the cutoff, read by the spec's `S.C.slot`
  have hslotM := ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot M.toSlotLayout F.sched) S s).1
  have hslot : S.C.slot ((M.supportCutoff S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact hslotM
  refine ⟨⟨τ, hτ, hτle⟩, by rw [hti]; exact hInv, ?_, ?_, hslot⟩
  · rw [hti, hclk]
    exact_mod_cast E.clockValue_le_of_set hvi (Or.inl hl)
  · rw [hslot]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U) S (s + 1)

/-- The duty window of slot `s + 1` starts before its support cutoff.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `S`: the setup; `s`: the slot.

Read aloud: a slot's duty window starts before its support cutoff. -/
theorem dutyWindowStart_succ_lt_supportCutoff (U : UniformSchedule M.toSlotLayout) (S : Setup V) (s : ℕ) :
    M.dutyWindowStart S.C (s + 1) < M.supportCutoff S.C (s + 1) := by
  have hΔ := one_le_Δ S
  have hdw := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_le_slotStart M.toSlotLayout F.sched) S s
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hv := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  omega

/-- **An updater's update.** `update_of_saved_confirmation` for a validator of `updaterAt M S A x s`
: some outcome of its tick at the support cutoff of slot `s + 1`,
from its state before the cutoff awake for slot `s + 1`, saves the confirmation it holds right after.

Why: `update_state_of_tick` at the reader's tick, with the wake test of
`tickInput_awakeSince_of_mem_activeThroughoutToTick`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`, `hWS`: the setup, the activity, the execution, its facts; `s`: the slot;
  `v`: the updater; `C`: the confirmation.

Read aloud: an updater's saved confirmation is what its update at the cutoff saved. -/
theorem update_of_saved_confirmation_of_updater (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ) (v : V) (C : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (hSaved : (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C) :
    ∃ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) ∧
      GoldilocksCorrectness.Record.Statements.Routines.AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1) ∧
      M.savedConfirmation n' s = some C := by
  obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  obtain ⟨n'', sent, hrun, hA, hSv, -, -, -⟩ := (update_state_of_tick M F U) S A x R s v E hk'
    ((tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hv
      ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_lt_supportCutoff M.toSlotLayout
        F.sched U) S (s + 1)))
  refine ⟨n'', sent, hrun, hA, ?_⟩
  rw [hSv] at hSaved
  exact hSaved

/-- **The producer, on the window widened by the two clock bounds.** A validator active in every
configuration in force at some real time from `ΔClockAhead` before `a` to `ΔClockBehind` after `b`, `1 ≤ b`,
`a ≤ b`, ticks to `b` and is counted up to that tick from `a` (`A.activeThroughoutToTick x a b`).

Why: the window holds every step whose real time is in `[b − ΔClockAhead, b + ΔClockBehind]`, so `v` ticks to `b`
(`tick_of_active`). When `a ≤ 0`, every step up to that tick is at a time from `0` to `b + ΔClockBehind`, inside
the window: the reader's first case. When `1 ≤ a`, the window holds every step whose real time is in
`[a − ΔClockAhead, a + ΔClockBehind]`, so `v` ticks to `a` at a step `k`; `k` comes at or before the tick to `b`
(`clock_mono`, `tick_unique`), and every step from `k` to the tick to `b` is inside the window: the second case
with the value `a`. The split is over the integer `a` and is exhaustive; no clause of the statement names it.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `v`: the validator;
  `a`, `b`: the clock values that open the reader's window and end it.

Read aloud: a validator active from one clock bound before `a` to one clock bound after `b` ticks to `b`
and is counted active up to that tick from `a`. -/
theorem mem_activeThroughoutToTick_of_mem_activeThroughout {S : Setup V} {A : Activity V}
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {v : V} {a : ℤ} {b : ℕ} (h1 : 1 ≤ b) (hab : a ≤ b)
    (hv : v ∈ A.activeThroughout x ((a : ℝ) - ΔClockAhead) ((b : ℝ) + ΔClockBehind)) :
    v ∈ A.activeThroughoutToTick x a b := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hvi : ∀ i : ℕ, (a : ℝ) - ΔClockAhead ≤ x.time i → x.time i ≤ (b : ℝ) + ΔClockBehind →
      v ∈ A.active i := fun i h1' h2' =>
    Activity.mem_activeThroughout.1 hv i h2' (le_trans h1' (R.time_mono (Nat.le_succ i)))
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  obtain ⟨k', hk', -, hk'2⟩ := E.tick_of_active b h1 v (fun i hi1 hi2 => hvi i (by linarith) hi2)
  refine Activity.mem_activeThroughoutToTick.2 ⟨k', hk', ?_⟩
  rcases le_or_gt a 0 with ha0 | ha0
  · left
    intro i hi
    have ht0 := (time_nonneg M) x R i
    have ha0' : (a : ℝ) ≤ 0 := by exact_mod_cast ha0
    exact hvi i (by linarith) (le_trans (R.time_mono hi) hk'2)
  · right
    obtain ⟨c, rfl⟩ : ∃ c : ℕ, a = (c : ℤ) := ⟨a.toNat, (Int.toNat_of_nonneg ha0.le).symm⟩
    have hc1 : 1 ≤ c := by omega
    have hcb : c ≤ b := by exact_mod_cast hab
    have hcbR : (c : ℝ) ≤ (b : ℝ) := by exact_mod_cast hcb
    have hcast : (((c : ℤ) : ℝ)) = (c : ℝ) := Int.cast_natCast c
    obtain ⟨k, hk, hk1, -⟩ := E.tick_of_active c hc1 v (fun i hi1 hi2 =>
      hvi i (by rw [hcast]; exact hi1) (by linarith))
    have hkk' : k ≤ k' := by
      by_contra hlt
      have hlt' : k' < k := by omega
      have hkc : v ∉ A.corrupted k := Activity.not_mem_corrupted_of_mem_active (E.tick_active k v c hk).1
      have hbc : b ≤ c := E.clock_mono k' k v b c hlt' hkc (Or.inl hk') (Or.inl hk)
      have hbc' : b = c := le_antisymm hbc hcb
      subst hbc'
      have := E.tick_unique k k' v b hk hk'
      omega
    refine ⟨k, hkk', c, le_rfl, hk, fun i hi1 hi2 => hvi i ?_ (le_trans (R.time_mono hi2) hk'2)⟩
    rw [hcast]
    exact le_trans hk1 (R.time_mono hi1)

/-- The environment's window from the model's natural duty window start of slot `s` is the window from
the protocol's integer start `duty_window_start S.C s`: the two are equal when the latter is not
negative, and when it is negative the former is `0`, and every step is at a time at least `0`, so both
windows, each opened `d ≥ 0` earlier, count every configuration up to `b`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `R`: the run's facts; `s`: the slot; `d`: how much earlier both windows open; `b`: the window's end;
  `v`: the validator.

Read aloud: active through the duty window from the model's start is active through it from the
protocol's start. -/
theorem activeThroughout_duty_window_start (U : UniformSchedule M.toSlotLayout) {S : Setup V}
    {A : Activity V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {s : ℕ} {d b : ℝ} {v : V}
    (hd : 0 ≤ d) (hv : v ∈ A.activeThroughout x ((M.dutyWindowStart S.C s : ℝ) - d) b) :
    v ∈ A.activeThroughout x (((duty_window_start S.C s : ℤ) : ℝ) - d) b := by
  have he := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_eq_toNat
    M.toSlotLayout F.sched U) S s
  refine Activity.mem_activeThroughout_of_forall fun i h1 h2 => Activity.mem_activeThroughout.1 hv i h1 ?_
  rcases lt_or_ge (duty_window_start S.C s) 0 with hneg | hnn
  · rw [he, Int.toNat_eq_zero.2 hneg.le, Nat.cast_zero]
    have := (time_nonneg M) x R (i + 1)
    linarith
  · have hc : (((duty_window_start S.C s).toNat : ℕ) : ℝ) = ((duty_window_start S.C s : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnn
    rw [he, hc]
    exact h2

/-- The duty window of slot `s + 1` starts strictly after that of slot `s`, or both start at `0` (the
start is clamped at `0` in the first slots).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `S`: the setup; `s`: the slot.

Read aloud: consecutive duty windows start in increasing order, unless both start at `0`. -/
theorem dutyWindowStart_lt_succ_or_zero (U : UniformSchedule M.toSlotLayout) (S : Setup V) (s : ℕ) :
    M.dutyWindowStart S.C s < M.dutyWindowStart S.C (s + 1) ∨
      (M.dutyWindowStart S.C s = 0 ∧ M.dutyWindowStart S.C (s + 1) = 0) := by
  obtain ⟨-, -, -, hs1, hd, -, hΔ⟩ := (slot_times M F U) S s
  obtain ⟨-, -, -, -, hd', -, -⟩ := (slot_times M F U) S (s + 1)
  rcases hd with hd | ⟨hd, hd2⟩ <;> rcases hd' with hd' | ⟨hd', hd2'⟩ <;> omega

/-- **The window inside a duty window, from a validator counted up to its tick.** A validator in
`A.activeThroughoutToTick x (duty_window_start S.C s) e` is active through `[b − max (Δ S) Δs, b]` when
`voteTime S.C s ≤ b + 3Δ`, `max (Δ S) Δs ≤ b` and `b + ΔClockAhead < e`, with
`max (Δ S) Δs + 3Δ + ΔClockAhead + ΔClockBehind < 4Δk`: that window starts more than `ΔClockBehind` after
the protocol's duty window start `4 Δ s + Δ − 4 Δ k`, and ends more than `ΔClockAhead` before the tick's
value (`mem_activeThroughout_of_mem_activeThroughoutToTick`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `Δs`: the sync delay; `s`: the
  slot; `b`: the window's end; `e`: the tick's value; `v`: the validator.

Read aloud: a validator active up to its tick from its duty window's start is active through every
recovery window inside that duty window and before the tick. -/
theorem activeThroughout_of_dutyWindow_ofTick (U : UniformSchedule M.toSlotLayout) {S : Setup V}
    {A : Activity V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {s b e : ℕ} {v : V}
    (h : v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) e)
    (hb : M.voteTime S.C s ≤ b + 3 * Δ S) (hcb : max (Δ S) Δs ≤ b) (hbe : (b : ℝ) + ΔClockAhead < e) :
    v ∈ A.activeThroughout x (b - (max (Δ S) Δs)) b := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hd := duty_window_start_real S s
  have hvt := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hmc : ((max (Δ S) Δs : ℕ) : ℝ) = max ((Δ S : ℕ) : ℝ) (Δs : ℝ) := Nat.cast_max _ _
  have hsub : ((b - max (Δ S) Δs : ℕ) : ℝ) = (b : ℝ) - ((max (Δ S) Δs : ℕ) : ℝ) := Nat.cast_sub hcb
  have hbR : ((M.voteTime S.C s : ℕ) : ℝ) ≤ (b : ℝ) + 3 * Δ S := by exact_mod_cast hb
  have hvR : ((M.voteTime S.C s : ℕ) : ℝ) = 4 * Δ S * s + Δ S := by rw [hvt, hss]; push_cast; ring
  have h' := (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E h (a' := b - max (Δ S) Δs) (e := b)
    (by rw [hsub, hd]; linarith [hmc]) hbe
  rw [hsub] at h'
  first | exact h' | (rw [hmc] at h'; exact h')

/-- A validator active through the duty window of slot `s + 1` up to its support cutoff, the window widened
by the two clock bounds, ticks to that cutoff and is counted up to its tick:
`mem_activeThroughoutToTick_of_mem_activeThroughout` at that window, whose end is at least `1` and after its
start.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `s`: the slot; `v`: the
  validator.

Read aloud: a validator active from one clock bound before its duty window to one clock bound after the
support cutoff is active up to its tick there. -/
theorem activeThroughoutToTick_of_dutyWindow (U : UniformSchedule M.toSlotLayout) {S : Setup V}
    {A : Activity V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {s : ℕ} {v : V}
    (hv : v ∈ A.activeThroughout x ((M.dutyWindowStart S.C (s + 1) : ℝ) - ΔClockAhead)
      ((M.supportCutoff S.C (s + 1) : ℝ) + ΔClockBehind)) :
    v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)) :=
  (mem_activeThroughoutToTick_of_mem_activeThroughout M F) x R E
    ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot M.toSlotLayout F.sched) S s).2
    ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_lt_supportCutoff M.toSlotLayout
      F.sched U) S (s + 1)).le
    ((activeThroughout_duty_window_start M F U) R E.ahead_nonneg hv)

/-- **The reader holds up to a tick strictly inside it.** A validator in `A.activeThroughoutToTick x a b` ticks to
every clock value `c ≥ 1` whose tick window `[c − ΔClockAhead, c + ΔClockBehind]` lies after the latest real time
of a tick to a value at most `a` and before the earliest real time of its tick to `b`, and is in
`A.activeThroughoutToTick x a c`.

Why: every step whose real time is in that window comes before the tick to `b` (`tick_active` at `b`), and, in the
reader's second case, after the tick to the value `c' ≤ a` (`tick_active` at `c'`); so `v` is active after it, and
ticks to `c` (`tick_of_active`); the reader holds up to that earlier tick (`mem_activeThroughoutToTick_of_tick_le`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `v`: the validator;
  `a`, `b`: the reader's window; `c`: the clock value inside it.

Read aloud: a validator active from `a` up to its tick to `b` ticks to every value strictly inside, with the
two clock bounds' margins, and is active from `a` up to that tick. -/
theorem mem_activeThroughoutToTick_of_inside {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {v : V} {a : ℤ} {b c : ℕ} (hv : v ∈ A.activeThroughoutToTick x a b) (hc1 : 1 ≤ c)
    (ha : (a : ℝ) + ΔClockBehind < (c : ℝ) - ΔClockAhead)
    (hb : (c : ℝ) + ΔClockBehind < (b : ℝ) - ΔClockAhead) :
    v ∈ A.activeThroughoutToTick x a c := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨k', hk', hcase⟩ := Activity.mem_activeThroughoutToTick.1 hv
  have hk'b := (E.tick_active k' v b hk').2.1
  obtain ⟨k'', hk'', -, -⟩ := E.tick_of_active c hc1 v (fun i h1 h2 => by
    have hik' : i < k' := (lt_of_time_lt M) x R (by linarith)
    rcases hcase with h | ⟨k, -, c', hca, hk, h⟩
    · exact h i hik'.le
    · have hka := (E.tick_active k v c' hk).2.2
      have hca' : (c' : ℝ) ≤ (a : ℝ) := by exact_mod_cast hca
      refine h i ?_ hik'.le
      by_contra hlt
      have := R.time_mono (show i ≤ k by omega)
      linarith)
  have hcb : c ≤ b := by
    have : (c : ℝ) ≤ b := by linarith
    exact_mod_cast this
  exact (mem_activeThroughoutToTick_of_tick_le M F) R E hv hk'' hcb

/-- The protocol's duty window start of slot `s`, read as a real number, is the model's natural-number start
when the latter is positive (the latter is the former raised to `0` when negative).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `S`: the setup; `s`: the slot.

Read aloud: a positive duty window start is the same in the two readings. -/
theorem duty_window_start_real_of_pos (U : UniformSchedule M.toSlotLayout) (S : Setup V) (s : ℕ)
    (h : 0 < M.dutyWindowStart S.C s) :
    ((duty_window_start S.C s : ℤ) : ℝ) = ((M.dutyWindowStart S.C s : ℕ) : ℝ) := by
  have he := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_eq_toNat
    M.toSlotLayout F.sched U) S s
  rw [he] at h ⊢
  have hnn : 0 ≤ duty_window_start S.C s := by
    by_contra hneg
    rw [Int.toNat_eq_zero.2 (le_of_lt (not_le.1 hneg))] at h
    exact absurd h (lt_irrefl 0)
  exact_mod_cast (Int.toNat_of_nonneg hnn).symm

/-- At the support cutoff of slot `s + 1`, an outcome of `v`'s tick from the state its tick to that cutoff starts
from, awake for slot `s + 1`, is a node state the confirmation update of slot `s + 1` leaves (the field
`tick_supportCutoff_confirmation_of_core` of `F.tk2`, from the core of the node invariant, Lemma 11, which holds
for every validator). The tick-input form of `confirmationUpdated_of_cutoff_tick`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `s`: the slot; `v`: the validator; `n₀`, `sent`: the outcome.

Read aloud: the tick at the support cutoff runs the confirmation update, from an awake state. -/
theorem confirmationUpdated_of_cutoff_tickInput (U : UniformSchedule M.toSlotLayout) {S : Setup V}
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ) (v : V) (n₀ : M.N)
    (sent : List (NamedObject V))
    (hrun : .ok (n₀, sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int))
    (hAw : GoldilocksCorrectness.Record.Statements.Routines.AwakeFor M S.C
      (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1)) :
    GoldilocksCorrectness.Record.Statements.Routines.ConfirmationUpdated M S.C S.P (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n₀ := by
  have hInv : M.nodeInvCore S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1))) :=
    (lem11_node_invariantCore_of_run M F S x R (x.tickStep v (M.supportCutoff S.C (s + 1))) v).1
  have hsl : S.C.slot ((M.supportCutoff S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot M.toSlotLayout F.sched) S s).1
  have h := F.tk2.tick_supportCutoff_confirmation_of_core S.C S.P S.X _ _ n₀ sent hrun hInv
    (by rw [hsl]; exact (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout
      F.sched U) S (s + 1))
    (by rw [hsl]; exact hAw)
  rw [hsl] at h
  exact h

/-- The natural-number form of `hΔs`, with the clock bounds dropped.

The variables:
- `S`: the setup; `Δs`: the sync delay; `ΔClockAhead`, `ΔClockBehind`: the clock bounds.

Read aloud: the longer of a delay and the sync delay, plus three delays, is less than `k` slots. -/
theorem slot_bound_nat_of_hΔs (S : Setup V) {Δs : ℕ} {ΔClockAhead ΔClockBehind : ℝ}
    (hA : 0 ≤ ΔClockAhead) (hB : 0 ≤ ΔClockBehind)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) :
    max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
  have h' : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
    push_cast; linarith
  exact_mod_cast h'

/-- **The updater's reader gives Lemma 12's receiver window at slot `s`.** A validator counted active from the
duty window's start of slot `s + 1` up to its tick to the support cutoff of slot `s + 1` ticks to the support
cutoff of slot `s` at a step `kR` and is active at every step from the real time
`supportCutoff s − max (2 · Δ S) Δs` (the sync fact's read time of Lemma 12) up to `kR`: the receiver window of
`lem12_honest_vote_delivered_until_of_steps`.

Why: the tick to the support cutoff of slot `s` lies more than both clock bounds inside the reader's window
(`mem_activeThroughoutToTick_of_inside`, by `hΔs` and `hSkew`), and the reader's integer opening value is more than
`ΔClockBehind` before the read time (`tick_window_of_activeThroughoutToTick_int`); when the read time is cut at
`0`, the opening value is less than `−ΔClockBehind`. Landed from the forty-fifth re-check's probe theorem 2
.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `s`: the slot; `v`: the validator.

Read aloud: an updater of slot `s + 1` ticks to the support cutoff of slot `s` and is active at every step from
Lemma 12's read time up to that tick. -/
theorem updater_reader_gives_core_window (U : UniformSchedule M.toSlotLayout) {S : Setup V} {A : Activity V}
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) {s : ℕ} {v : V}
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1))) :
    ∃ kR : ℕ, x.lbl kR = Event.tick v (M.supportCutoff S.C s) ∧
      ∀ i : ℕ, ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time i → i ≤ kR →
        v ∈ A.active i := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨hvt, hct, -, hs1, hd, hk8, hΔ⟩ := (slot_times M F U) S s
  obtain ⟨-, hct', -, -, -, -, -⟩ := (slot_times M F U) S (s + 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hdw := duty_window_start_real S (s + 1)
  push_cast at hdw
  have hkm := slot_bound_nat_of_hΔs M F S hA0 hB0 hΔs
  have hm1 := le_max_left (Δ S) Δs
  have hm2 := le_max_right (Δ S) Δs
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hcR : ((M.supportCutoff S.C s : ℕ) : ℝ) = 4 * Δ S * s + 2 * Δ S := by
    rw [hct, hss]; push_cast; ring
  have hc1R : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = 4 * Δ S * s + 6 * Δ S := by
    rw [hct', hs1, hss]; push_cast; ring
  have hmaxR : ((max (Δ S) Δs : ℕ) : ℝ) = max ((Δ S : ℕ) : ℝ) (Δs : ℝ) := Nat.cast_max _ _
  have hΔsR : (Δs : ℝ) ≤ ((max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hm2
  have hΔ1R : ((Δ S : ℕ) : ℝ) ≤ ((max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hm1
  have hkmR : ((max (Δ S) Δs : ℕ) : ℝ) + 3 * Δ S < 4 * Δ S * S.C.k := by exact_mod_cast hkm
  -- the tick to the support cutoff of slot `s`, strictly inside the reader's window
  have hv' : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C s) :=
    (mem_activeThroughoutToTick_of_inside M F) R E hv (by omega)
      (by rw [hdw, hcR]; linarith) (by rw [hcR, hc1R]; linarith)
  -- active from the real time `t₀` up to that tick
  refine (tick_window_of_activeThroughoutToTick_int M) x R E hv' ?_
  rw [hdw]
  rcases le_or_gt (max (2 * Δ S) Δs) (M.supportCutoff S.C s) with hle | hlt
  · rw [Nat.cast_sub hle, Nat.cast_max, hcR]
    push_cast
    rcases le_or_gt (2 * (Δ S : ℝ)) (Δs : ℝ) with h2 | h2
    · rw [max_eq_right h2]; linarith
    · rw [max_eq_left h2.le]
      have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
      linarith
  · -- the read time is cut at `0`: the sync delay is longer than the support cutoff of slot `s`
    rw [Nat.sub_eq_zero_of_le hlt.le, Nat.cast_zero]
    have h2 : M.supportCutoff S.C s < Δs := by
      rcases max_choice (2 * Δ S) Δs with hm | hm <;> rw [hm] at hlt <;> omega
    have h2R : ((M.supportCutoff S.C s : ℕ) : ℝ) < Δs := by exact_mod_cast h2
    rw [hcR] at h2R
    linarith


/-- **An updater of slot `s' + 1` is a reader to its tick to the vote time of slot `s' + 1`, from the duty window's
start of slot `s' + 2`, under `hSkew`.** A validator of `updaterAt M S A x (s' + 1)` (it ticks to the support cutoff
of slot `s' + 2`, active up to that tick from the trace's start or from its own tick to a clock value at most the
protocol's duty window start of slot `s' + 2`) ticks to the vote time of slot `s' + 1` and is active at every step up
to that tick, from the trace's start or from its own tick to a clock value at most `M.dutyWindowStart S.C (s' + 2)`.

Why: the vote time of slot `s' + 1` lies more than both clock bounds inside the reader's window
(`mem_activeThroughoutToTick_of_inside`: `ΔClockAhead + ΔClockBehind < 4 Δ (k − 1)` and `< 5 Δ`, from `hSkew`), and
the protocol's integer duty window start is at most its natural-number form (`dutyWindowStart_eq_toNat`). Landed
from the forty-eighth re-check's probe theorem 3.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `A`: the activity; `x`: the execution; `R`: the run's facts; `E`: the environment's facts;
- `s'`: the slot; `v`: the validator.

Read aloud: a validator that ran the update of slot `s' + 1` awake up to its own tick also ticked to the vote time of
slot `s' + 1`, awake up to that tick from the same start. -/
theorem reader_from_updater_under_skew (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s' : ℕ) (v : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hHonUpd : v ∈ updaterAt M S A x (s' + 1)) :
    v ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (s' + 2) : ℕ) : ℤ) (M.voteTime S.C (s' + 1)) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨hv0, hc0, -, hs0, -, hk8, hΔ⟩ := (slot_times M F U) S s'
  obtain ⟨hv1, -, -, hs1, -, -, -⟩ := (slot_times M F U) S (s' + 1)
  obtain ⟨-, hc2, -, -, -, -, -⟩ := (slot_times M F U) S (s' + 1 + 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s'
  have hdw2 := duty_window_start_real S (s' + 1 + 1)
  push_cast at hdw2
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  have hv1R : ((M.voteTime S.C (s' + 1) : ℕ) : ℝ) = 4 * Δ S * s' + 5 * Δ S := by
    rw [hv1, hs0, hss]; push_cast; ring
  have hc2R : ((M.supportCutoff S.C (s' + 1 + 1) : ℕ) : ℝ) = 4 * Δ S * s' + 10 * Δ S := by
    rw [hc2, hs1, hs0, hss]; push_cast; ring
  have h1 : 1 ≤ M.voteTime S.C (s' + 1) := by omega
  have hin := (mem_activeThroughoutToTick_of_inside M F) R E hHonUpd h1
    (by rw [hdw2, hv1R]; linarith) (by rw [hv1R, hc2R]; linarith)
  refine Activity.mem_activeThroughoutToTick_of_le ?_ hin
  have e := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_eq_toNat M.toSlotLayout F.sched U) S (s' + 2)
  show duty_window_start S.C (s' + 2) ≤ ((M.dutyWindowStart S.C (s' + 2) : ℕ) : ℤ)
  rw [e]
  exact Int.self_le_toNat _


/-- **An updater of slot `s` is a reader to its tick to the vote time of slot `s + 1`, from the duty window's start of
slot `s + 2`, under `hSkew`.** A validator of `updaterAt M S A x s` (it ticks to the support cutoff of slot `s + 1`,
active up to that tick from the trace's start or from its own tick to a clock value at most the protocol's duty window
start of slot `s + 1`) ticks to the vote time of slot `s + 1` and is active at every step up to that tick, from the
trace's start or from its own tick to a clock value at most `M.dutyWindowStart S.C (s + 2)`.

Why: the vote time of slot `s + 1` lies more than both clock bounds inside the reader's window
(`mem_activeThroughoutToTick_of_inside`: `ΔClockAhead + ΔClockBehind < 4 Δ k` and `< Δ`, from `hSkew`), and the
protocol's integer duty window start of slot `s + 1` is at most that of slot `s + 2`, at most its natural-number form.
The reader `round_proposal_extends` hands the tick helper `live_locks_compatible_of_honestChainExtends_tick`
.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `A`: the activity; `x`: the execution; `R`: the run's facts; `E`: the environment's facts;
- `s`: the slot; `v`: the validator.

Read aloud: a validator that ran the update of slot `s` awake up to its own tick also ticked to the vote time of slot
`s + 1`, awake up to that tick. -/
theorem vote_reader_from_updater_under_skew (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ) (v : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hUpd : v ∈ updaterAt M S A x s) :
    v ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (s + 2) : ℕ) : ℤ) (M.voteTime S.C (s + 1)) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨hv0, hc0, -, hs0, -, hk8, hΔ⟩ := (slot_times M F U) S s
  obtain ⟨hv1, hc1, -, hs1, -, -, -⟩ := (slot_times M F U) S (s + 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hdw1 := duty_window_start_real S (s + 1)
  push_cast at hdw1
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  have hv1R : ((M.voteTime S.C (s + 1) : ℕ) : ℝ) = 4 * Δ S * s + 5 * Δ S := by
    rw [hv1, hs0, hss]; push_cast; ring
  have hc1R : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = 4 * Δ S * s + 6 * Δ S := by
    rw [hc1, hs0, hss]; push_cast; ring
  have h1 : 1 ≤ M.voteTime S.C (s + 1) := by omega
  have hin := (mem_activeThroughoutToTick_of_inside M F) R E hUpd h1
    (by rw [hdw1, hv1R]; linarith) (by rw [hv1R, hc1R]; linarith)
  refine Activity.mem_activeThroughoutToTick_of_le ?_ hin
  have e := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_eq_toNat M.toSlotLayout F.sched U) S (s + 2)
  rw [e]
  exact le_trans (GoldilocksCorrectness.Proofs.Routines.duty_window_start_mono S (Nat.le_succ (s + 1)))
    (Int.self_le_toNat _)

/-- **An updater of slot `s` is active at every step from Lemma 12's read time of slot `s + 1` up to its tick to the
support cutoff of slot `s + 1`.** A validator of `updaterAt M S A x s` ticks to `M.supportCutoff S.C (s + 1)` at a step
`kR` and is active at every step whose real time is at least `supportCutoff (s + 1) − max (2 · Δ S) Δs` up to `kR`.

Why: the reader's integer opening value, at most the protocol's duty window start of slot `s + 1`, is more than
`ΔClockBehind` before that read time (`hΔs`; when the read time is cut at `0`, the opening value is less than
`−ΔClockBehind`): `tick_window_of_activeThroughoutToTick_int`. The step form `proposal_parent_extends_majority_block`
reads of the proposer.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `s`: the slot; `v`: the validator.

Read aloud: an updater of slot `s` is active from Lemma 12's read time of slot `s + 1` up to its own tick to the
support cutoff of slot `s + 1`. -/
theorem updater_reader_gives_own_core_window (U : UniformSchedule M.toSlotLayout) {S : Setup V} {A : Activity V}
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) {s : ℕ} {v : V}
    (hUpd : v ∈ updaterAt M S A x s) :
    ∃ kR : ℕ, x.lbl kR = Event.tick v (M.supportCutoff S.C (s + 1)) ∧
      ∀ i : ℕ, ((M.supportCutoff S.C (s + 1) - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time i → i ≤ kR →
        v ∈ A.active i := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨hvt, hct, -, hs1, hd, hk8, hΔ⟩ := (slot_times M F U) S s
  obtain ⟨-, hct', -, -, -, -, -⟩ := (slot_times M F U) S (s + 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hdw := duty_window_start_real S (s + 1)
  push_cast at hdw
  have hkm := slot_bound_nat_of_hΔs M F S hA0 hB0 hΔs
  have hm1 := le_max_left (Δ S) Δs
  have hm2 := le_max_right (Δ S) Δs
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hc1R : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = 4 * Δ S * s + 6 * Δ S := by
    rw [hct', hs1, hss]; push_cast; ring
  have hkmR : ((max (Δ S) Δs : ℕ) : ℝ) + 3 * Δ S < 4 * Δ S * S.C.k := by exact_mod_cast hkm
  have hΔsR : (Δs : ℝ) ≤ ((max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hm2
  refine (tick_window_of_activeThroughoutToTick_int M) x R E hUpd ?_
  rw [hdw]
  rcases le_or_gt (max (2 * Δ S) Δs) (M.supportCutoff S.C (s + 1)) with hle | hlt
  · rw [Nat.cast_sub hle, Nat.cast_max, hc1R]
    push_cast
    rcases le_or_gt (2 * (Δ S : ℝ)) (Δs : ℝ) with h2 | h2
    · rw [max_eq_right h2]; linarith
    · rw [max_eq_left h2.le]
      have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
      linarith
  · rw [Nat.sub_eq_zero_of_le hlt.le, Nat.cast_zero]
    have h2 : M.supportCutoff S.C (s + 1) < Δs := by
      rcases max_choice (2 * Δ S) Δs with hm | hm <;> rw [hm] at hlt <;> omega
    have h2R : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) < Δs := by exact_mod_cast h2
    rw [hc1R] at h2R
    linarith

/-- **A real-time window from the duty window's start of slot `s' + 1` to its vote time gives Lemma 12's
receiver window and holder window at slot `s'`.** A validator active at every real time from
`M.dutyWindowStart S.C (s' + 1)` to `M.voteTime S.C (s' + 1)` ticks to the support cutoff of slot `s'` at a step
`kR` and is active at every step from the read time `t₀ := supportCutoff s' − max (2 · Δ S) Δs` up to `kR`, and
is active throughout `[t₀, t₀ + Δs]`.

Why: the duty window of slot `s' + 1` starts at or before `t₀` (`hΔs`), `t₀ + Δs` is at most the support cutoff of
slot `s'` (`hGST`), and the tick to that cutoff lies inside the window (`tick_of_active`, `hSkew`), every step up to
it at a real time at most the cutoff plus `ΔClockBehind`, before the vote time of slot `s' + 1`. Landed from the
forty-fifth re-check's probe theorem 3.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `GST`: the sync time; `s'`: the slot;
  `w`: the validator.

Read aloud: a validator active through the duty window of slot `s' + 1` up to its vote time ticks to the support
cutoff of slot `s'`, active from Lemma 12's read time up to that tick, and is active through the holder window. -/
theorem dutyWindow_gives_core_window_and_hold (U : UniformSchedule M.toSlotLayout) {S : Setup V} {A : Activity V}
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) {GST s' : ℕ} {w : V}
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s')
    (hHon : w ∈ A.activeThroughout x (M.dutyWindowStart S.C (s' + 1)) (M.voteTime S.C (s' + 1))) :
    (∃ kR : ℕ, x.lbl kR = Event.tick w (M.supportCutoff S.C s') ∧
      ∀ i : ℕ, ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time i → i ≤ kR →
        w ∈ A.active i) ∧
    w ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨hvt, hct, -, hs1, -, hk8, hΔ⟩ := (slot_times M F U) S s'
  obtain ⟨hvt', -, -, -, hd', -, -⟩ := (slot_times M F U) S (s' + 1)
  have hkm := slot_bound_nat_of_hΔs M F S hA0 hB0 hΔs
  have hm1 := le_max_left (Δ S) Δs
  have hm2 := le_max_right (Δ S) Δs
  -- the duty window of slot `s' + 1` starts at or before the read time `t₀`
  have hdt : M.dutyWindowStart S.C (s' + 1) ≤ M.supportCutoff S.C s' - max (2 * Δ S) Δs := by
    clear hvt hvt'
    rcases hd' with hd' | ⟨hd', -⟩
    · rcases le_or_gt (2 * Δ S) Δs with h2 | h2
      · rw [max_eq_right h2]
        rw [max_eq_right (le_trans (by omega) h2)] at hkm
        omega
      · rw [max_eq_left h2.le]
        omega
    · rw [hd']
      exact Nat.zero_le _
  have hdtR : ((M.dutyWindowStart S.C (s' + 1) : ℕ) : ℝ) ≤
      ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hdt
  -- the read time plus the sync delay is at most the support cutoff of slot `s'`
  have hte : M.supportCutoff S.C s' - max (2 * Δ S) Δs + Δs ≤ M.supportCutoff S.C s' := by
    rcases le_or_gt (2 * Δ S) Δs with h2 | h2
    · rw [max_eq_right h2]; omega
    · rw [max_eq_left h2.le]; omega
  have hteR : ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs ≤
      ((M.supportCutoff S.C s' : ℕ) : ℝ) := by exact_mod_cast hte
  have hcvR : ((M.supportCutoff S.C s' : ℕ) : ℝ) + 3 * Δ S = ((M.voteTime S.C (s' + 1) : ℕ) : ℝ) := by
    have : M.supportCutoff S.C s' + 3 * Δ S = M.voteTime S.C (s' + 1) := by omega
    exact_mod_cast this
  have hdcR : ((M.dutyWindowStart S.C (s' + 1) : ℕ) : ℝ) + 2 * Δ S ≤ ((M.supportCutoff S.C s' : ℕ) : ℝ) := by
    have : M.dutyWindowStart S.C (s' + 1) + 2 * Δ S ≤ M.supportCutoff S.C s' := by
      rcases hd' with hd' | ⟨hd', -⟩ <;> omega
    exact_mod_cast this
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hwin : ∀ i : ℕ, ((M.dutyWindowStart S.C (s' + 1) : ℕ) : ℝ) ≤ x.time i →
      x.time i ≤ ((M.voteTime S.C (s' + 1) : ℕ) : ℝ) → w ∈ A.active i := fun i h1 h2 =>
    Activity.mem_activeThroughout.1 hHon i h2 (le_trans h1 (R.time_mono (Nat.le_succ i)))
  refine ⟨?_, Activity.mem_activeThroughout_of_le hdtR (by linarith) hHon⟩
  -- the tick to the support cutoff of slot `s'`, inside the window
  obtain ⟨kR, hkR, -, hkR2⟩ := E.tick_of_active (M.supportCutoff S.C s') (by omega) w
    (fun i h1 h2 => hwin i (by linarith) (by linarith))
  refine ⟨kR, hkR, fun i hi hik => hwin i (le_trans hdtR hi) ?_⟩
  exact le_trans (R.time_mono hik) (by linarith)

/-- **A reader from the protocol's duty window start of slot `s' + 1` to the vote time of slot `s' + 1` gives Lemma 12's
receiver window at slot `s'`.** A validator that ticks to the vote time of slot `s' + 1`, active up to that tick from
the trace's start or from its own tick to a clock value at most `duty_window_start S.C (s' + 1)`, ticks to the support
cutoff of slot `s'` at a step `kR` and is active at every step from the read time
`t₀ := supportCutoff s' − max (2 · Δ S) Δs` up to `kR`. The reader form of `dutyWindow_gives_core_window_and_hold`'s
first conjunct.

Why: the tick to the cutoff lies strictly inside the reader (`mem_activeThroughoutToTick_of_inside`): the duty window's
start plus the behind bound is less than `t₀` (`hΔs`, `hSkew`), and the cutoff plus the behind bound is less than the
vote time of slot `s' + 1` minus the ahead bound. A step at a real time at least `t₀` comes after the reader's opening
tick, whose real time is at most the duty window's start plus the behind bound.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `GST`: the sync time; `s'`: the slot;
  `w`: the validator.

Read aloud: a validator active from its tick at most at the duty window's start of slot `s' + 1` up to its tick to that
slot's vote time ticks to the support cutoff of slot `s'`, active from Lemma 12's read time up to that tick. -/
theorem core_window_of_dutyWindow_reader (U : UniformSchedule M.toSlotLayout) {S : Setup V} {A : Activity V}
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) {GST s' : ℕ} {w : V}
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s')
    (hHon : w ∈ A.activeThroughoutToTick x (duty_window_start S.C (s' + 1)) (M.voteTime S.C (s' + 1))) :
    ∃ kR : ℕ, x.lbl kR = Event.tick w (M.supportCutoff S.C s') ∧
      ∀ i : ℕ, ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time i → i ≤ kR →
        w ∈ A.active i := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨-, hct, -, -, -, hk8, hΔ⟩ := (slot_times M F U) S s'
  obtain ⟨hvt', -, -, -, -, -, -⟩ := (slot_times M F U) S (s' + 1)
  obtain ⟨-, -, -, hs1, -, -, -⟩ := (slot_times M F U) S s'
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s'
  have hdw := duty_window_start_real S (s' + 1)
  push_cast at hdw
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  have hcR : ((M.supportCutoff S.C s' : ℕ) : ℝ) = 4 * Δ S * s' + 2 * Δ S := by
    rw [hct, hss]; push_cast; ring
  have hvR : ((M.voteTime S.C (s' + 1) : ℕ) : ℝ) = 4 * Δ S * s' + 5 * Δ S := by
    rw [hvt', hs1, hss]; push_cast; ring
  -- `t₀ = supportCutoff s' − max (2 · Δ S) Δs`, read in the reals: the cutoff is at least the maximum
  have hm2 : max (2 * Δ S) Δs ≤ M.supportCutoff S.C s' := by
    have := le_max_right (Δ S) Δs
    rcases max_choice (2 * Δ S) Δs with h | h <;> rw [h] <;> omega
  have ht₀ : ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) =
      ((M.supportCutoff S.C s' : ℕ) : ℝ) - ((max (2 * Δ S) Δs : ℕ) : ℝ) := by
    rw [Nat.cast_sub hm2]
  -- the arithmetic of `hΔs`: `3 · Δ S + max (2 · Δ S) Δs + ΔClockAhead + ΔClockBehind < 4 · Δ S · k`
  have hkey : 3 * (Δ S : ℝ) + ((max (2 * Δ S) Δs : ℕ) : ℝ) + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k := by
    have hmx : (Δs : ℝ) ≤ (max (Δ S) Δs : ℝ) := le_max_right _ _
    have hmx' : (Δ S : ℝ) ≤ (max (Δ S) Δs : ℝ) := le_max_left _ _
    rcases max_choice (2 * Δ S) Δs with h | h <;> rw [h] <;> push_cast <;> linarith
  have ha : ((duty_window_start S.C (s' + 1) : ℤ) : ℝ) + ΔClockBehind <
      ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) := by
    rw [ht₀, hdw, hcR]; linarith
  have hm2R : 2 * (Δ S : ℝ) ≤ ((max (2 * Δ S) Δs : ℕ) : ℝ) := by
    exact_mod_cast (le_max_left (2 * Δ S) Δs)
  have hin := (mem_activeThroughoutToTick_of_inside M F) R E hHon (c := M.supportCutoff S.C s')
    (by omega) (by rw [ht₀] at ha; linarith) (by rw [hvR, hcR]; linarith)
  obtain ⟨kR, hkR, hcase⟩ := Activity.mem_activeThroughoutToTick.1 hin
  refine ⟨kR, hkR, fun i hi hik => ?_⟩
  rcases hcase with h | ⟨k, -, c, hc, hk, hact⟩
  · exact h i hik
  · have hkt := (E.tick_active k w c hk).2.2
    have hcR' : ((c : ℤ) : ℝ) ≤ ((duty_window_start S.C (s' + 1) : ℤ) : ℝ) := by exact_mod_cast hc
    push_cast at hcR'
    exact hact i (le_of_lt ((lt_of_time_lt M) x R (by linarith))) hik


open Classical in
/-- **A validator outside the adversary set at every honest validator's tick to `b` is outside it at `v`'s tick to
`b`.** For `v` counted active up to its own tick to `b` (`A.activeThroughoutToTick x a b`), a validator `u` that is in
the adversary set at no step where a validator outside it ticks to `b` is outside the adversary set at the step of `v`'s tick to `b`.

Why: `v` is active, so outside the adversary set, at its own tick (`tick_active`). Landed from the forty-sixth re-check's
probe theorem 1.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `E`: the environment's facts; `a`, `b`: the reader's window; `u`: the voter; `v`: the
  receiver.

Read aloud: a voter that no honest validator's tick to `b` finds in the adversary set is honest at `v`'s tick to
`b`. -/
theorem not_mem_corrupted_tickStep_of_outside_at_honest_ticks {A : Activity V} (x : Trace V (NamedObject V) M.N)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {a : ℤ} {b : ℕ} {u v : V} (hv : v ∈ A.activeThroughoutToTick x a b)
    (hu : u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w b ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k)) :
    u ∉ A.corrupted (x.tickStep v b) := by
  obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  rw [(tickStep_eq_of_lbl M) x E hk']
  intro huk
  have hvk : v ∉ A.corrupted k' := (Activity.mem_active.1 (E.tick_active k' v b hk').1).2
  exact hu (Finset.mem_filter.2 ⟨Finset.mem_univ u, k', v, hk', hvk, huk⟩)

/--

Why: that window starts more than `ΔClockBehind` after the protocol's duty window start of slot `s + 1` (`hΔs`; when
`t₀` is cut at `0`, the start is less than `−ΔClockBehind`) and ends, at most at the support cutoff of slot `s`
(`hGST`), more than `ΔClockAhead` before the support cutoff of slot `s + 1` (`hSkew`):
`mem_activeThroughout_of_mem_activeThroughoutToTick`. Landed from the forty-sixth re-check's probe theorem 2
.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `GST`: the sync time; `s`: the slot;
  `u`: the validator.

Read aloud: an updater of slot `s` holds through the sync delay after Lemma 12's read time at slot `s`. -/
theorem holder_window_of_updater_reader (U : UniformSchedule M.toSlotLayout) {S : Setup V} {A : Activity V}
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) {GST s : ℕ} {u : V}
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hu : u ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1))) :
    u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨hvt, hct, -, hs1, hd, hk8, hΔ⟩ := (slot_times M F U) S s
  obtain ⟨-, hct', -, -, -, -, -⟩ := (slot_times M F U) S (s + 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hdw := duty_window_start_real S (s + 1)
  push_cast at hdw
  have hkm := slot_bound_nat_of_hΔs M F S hA0 hB0 hΔs
  have hm1 := le_max_left (Δ S) Δs
  have hm2 := le_max_right (Δ S) Δs
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hcR : ((M.supportCutoff S.C s : ℕ) : ℝ) = 4 * Δ S * s + 2 * Δ S := by
    rw [hct, hss]; push_cast; ring
  have hc1R : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = 4 * Δ S * s + 6 * Δ S := by
    rw [hct', hs1, hss]; push_cast; ring
  have hkmR : ((max (Δ S) Δs : ℕ) : ℝ) + 3 * Δ S < 4 * Δ S * S.C.k := by exact_mod_cast hkm
  have hΔsR : (Δs : ℝ) ≤ max ((Δ S : ℕ) : ℝ) (Δs : ℝ) := le_max_right _ _
  have hΔ1R : ((Δ S : ℕ) : ℝ) ≤ max ((Δ S : ℕ) : ℝ) (Δs : ℝ) := le_max_left _ _
  -- the read time plus the sync delay is at most the support cutoff of slot `s`
  have hte : M.supportCutoff S.C s - max (2 * Δ S) Δs + Δs ≤ M.supportCutoff S.C s := by
    rcases le_or_gt (2 * Δ S) Δs with h2 | h2
    · rw [max_eq_right h2]; omega
    · rw [max_eq_left h2.le]; omega
  have hteR : ((M.supportCutoff S.C s - max (2 * Δ S) Δs + Δs : ℕ) : ℝ) ≤
      ((M.supportCutoff S.C s : ℕ) : ℝ) := by exact_mod_cast hte
  have h := (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E hu
    (a' := M.supportCutoff S.C s - max (2 * Δ S) Δs) (e := M.supportCutoff S.C s - max (2 * Δ S) Δs + Δs)
    ?_ ?_
  · push_cast at h
    exact h
  · -- the duty window's start of slot `s + 1`, plus the clock-behind bound, is before the read time
    rw [hdw]
    rcases le_or_gt (max (2 * Δ S) Δs) (M.supportCutoff S.C s) with hle | hlt
    · rw [Nat.cast_sub hle, Nat.cast_max, hcR]
      push_cast
      rcases le_or_gt (2 * (Δ S : ℝ)) (Δs : ℝ) with h2 | h2
      · rw [max_eq_right h2]; linarith
      · rw [max_eq_left h2.le]
        have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
        linarith
    · rw [Nat.sub_eq_zero_of_le hlt.le, Nat.cast_zero]
      have h2 : M.supportCutoff S.C s < Δs := by
        rcases max_choice (2 * Δ S) Δs with hm | hm <;> rw [hm] at hlt <;> omega
      have h2R : ((M.supportCutoff S.C s : ℕ) : ℝ) < Δs := by exact_mod_cast h2
      rw [hcR] at h2R
      linarith
  · -- the window's end, plus the clock-ahead bound, is before the support cutoff of slot `s + 1`
    rw [hc1R]
    rw [hcR] at hteR
    linarith

/--

Why: `v`'s tick to `c₀` is one of those ticks, and its step is the step `x.tickStep v c₀` (`tickStep_eq_of_lbl`).
Landed from the forty-sixth re-check's probe theorem 3.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `E`: the environment's facts; `c₀`: the clock value; `k`: the step of `v`'s tick to `c₀`;
  `v`: the validator.

Read aloud: roots name blocks up to `v`'s own tick to `c₀` when they do up to every tick to a value at most
`c₀`. -/
theorem roots_at_own_tick_of_per_tick {A : Activity V} (x : Trace V (NamedObject V) M.N)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {c₀ k : ℕ} {v : V}
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ c₀ →
      RootsNameBlocksUntil M A x (x.time k))
    (hk : x.lbl k = Event.tick v c₀) :
    RootsNameBlocksUntil M A x (x.time (x.tickStep v c₀)) := by
  rw [(tickStep_eq_of_lbl M) x E hk]
  exact hRoots k v c₀ hk le_rfl


/-- **A validator counted active up to its tick to `b` is outside the adversary set at every real time `t` more
than `ΔClockAhead` before `b`.**

Why: its tick to `b` is at a real time at least `b − ΔClockAhead` (`tick_active`), after `t`, so every step at a
real time at most `t` comes before that tick (`lt_of_time_lt`); the validator is outside the adversary set at the
tick, and the adversary set only grows (`corrupted_mono`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `a`, `b`: the reader's window; `t`: the
  real time; `v`: the validator.

Read aloud: a validator active up to its tick to `b` is honest at every time well before `b`. -/
theorem not_mem_corruptedAtTime_of_mem_activeThroughoutToTick {S : Setup V} {A : Activity V}
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {a : ℤ} {b : ℕ} {t : ℝ} {v : V} (hv : v ∈ A.activeThroughoutToTick x a b)
    (ht : t + ΔClockAhead < (b : ℝ)) :
    v ∉ A.corruptedAtTime x t := by
  obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  have hvk : v ∉ A.corrupted k' := (Activity.mem_active.1 (E.tick_active k' v b hk').1).2
  have hk'b := (E.tick_active k' v b hk').2.1
  refine Activity.not_mem_corruptedAtTime.2 fun i hi hvi => hvk ?_
  have hik : i < k' := (lt_of_time_lt M) x R (by linarith)
  exact E.corrupted_mono i k' hik.le hvi

/-- **Roots named up to a real time give roots at every tick to a value at most `c₀`, when that time is at least
`c₀ + ΔClockBehind`.** Every tick to a value `c` is at a real time at most `c + ΔClockBehind` (`tick_active`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `E`: the environment's facts; `T`: the real time; `c₀`: the clock value.

Read aloud: roots named until `T` are named at every tick to a value at most `c₀`, when every such tick is before
`T`. -/
theorem per_tick_roots_of_roots_until {A : Activity V} (x : Trace V (NamedObject V) M.N)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {T : ℝ} {c₀ : ℕ} (hRoots : RootsNameBlocksUntil M A x T) (hT : (c₀ : ℝ) + ΔClockBehind ≤ T) :
    ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ c₀ →
      RootsNameBlocksUntil M A x (x.time k) := by
  intro k u c hk hc
  have hkc := (E.tick_active k u c hk).2.2
  have hcR : (c : ℝ) ≤ c₀ := by exact_mod_cast hc
  exact (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (by linarith) hRoots


open Classical in
/-- **A validator outside the adversary set at every honest validator's tick to `c` is outside it at the step of a
given validator's tick to `c`.** The form of `not_mem_corrupted_tickStep_of_outside_at_honest_ticks` read from the
tick's step, for a receiver known only to tick to `c`: a validator that ticks is outside the adversary set there
(`tick_active`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `E`: the environment's facts; `c`: the clock value; `k`: the step of `w`'s tick to `c`;
  `u`: the voter; `w`: the receiver.

Read aloud: a voter that no honest validator's tick to `c` finds in the adversary set is honest at `w`'s tick to
`c`. -/
theorem not_mem_corrupted_tickStep_of_outside_at_honest_ticks_of_lbl {A : Activity V}
    (x : Trace V (NamedObject V) M.N)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {c k : ℕ} {u w : V} (hk : x.lbl k = Event.tick w c)
    (hu : u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w c ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k)) :
    u ∉ A.corrupted (x.tickStep w c) := by
  rw [(tickStep_eq_of_lbl M) x E hk]
  intro huk
  have hwk : w ∉ A.corrupted k := (Activity.mem_active.1 (E.tick_active k w c hk).1).2
  exact hu (Finset.mem_filter.2 ⟨Finset.mem_univ u, k, w, hk, hwk, huk⟩)

open Classical in
/-- **A validator counted active up to its tick to `b` is outside the adversary set at every honest validator's tick
to a clock value `c` whose tick window ends more than `ΔClockAhead` before `b`.**

Why: a tick to `c` is at a real time at most `c + ΔClockBehind` (`tick_active`), before the validator's own tick to
`b`, at a real time at least `b − ΔClockAhead`; the validator is outside the adversary set at its own tick, and the
adversary set only grows (`corrupted_mono`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `a`, `b`: the reader's window; `c`: the
  clock value; `u`: the validator.

Read aloud: a validator active up to its tick to `b` is honest at every honest tick to a value well before `b`. -/
theorem outside_at_honest_ticks_of_mem_activeThroughoutToTick {S : Setup V} {A : Activity V}
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {a : ℤ} {b c : ℕ} {u : V} (hu : u ∈ A.activeThroughoutToTick x a b)
    (hc : (c : ℝ) + ΔClockBehind + ΔClockAhead < (b : ℝ)) :
    u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w c ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k) := by
  obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hu
  have huk' : u ∉ A.corrupted k' := (Activity.mem_active.1 (E.tick_active k' u b hk').1).2
  have hk'b := (E.tick_active k' u b hk').2.1
  intro h
  obtain ⟨k, w, hk, -, huk⟩ := (Finset.mem_filter.1 h).2
  have hkc := (E.tick_active k w c hk).2.2
  have hkk : k < k' := (lt_of_time_lt M) x R (by linarith)
  exact huk' (E.corrupted_mono k k' hkk.le huk)

end GoldilocksCorrectness.Record.Proofs.Executions
