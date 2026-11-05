module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ExecutionDefs
public import GoldilocksCorrectness.Proofs.Executions.Steps

@[expose] public section

/-!
# Steps, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Steps.lean` over a model `M`, for an
execution `x` of `protocolOf M S`: the order of the steps and of their times, the step before a
time, and the lifting of a per-step relation to the node states before two times. None reads a fact
of the model: they read the framework's atomic semantics only. `rel_of_forall_step` names no member;
the twins read the landed one.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Proofs.Executions (rel_of_forall_step)

open GoldilocksCorrectness.Record.Statements.Executions

open Framework.StsMultisetLog (SignedMsg atomic_time_stepwise tickAllAwake_of_time)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks (NodeState NamedObject RootOrder)
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)
variable {S : Setup V} {A : Activity V} (x : Trace V (NamedObject V) M.N)

/-! ## Times along the steps -/

/-- A step's configuration is at the time of the configuration before it, or later.

The variables:
- `M`: the model;
- `x`: the execution; `i`: the step.

Read aloud: time never goes back from one step to the next. -/
theorem time_le_succ (R : RunFacts M S x) (i : ℕ) : x.time i ≤ x.time (i + 1) :=
  R.time_le_succ i

/-- Times only grow along the steps.

The variables:
- `M`: the model;
- `x`: the execution; `i`, `j`: two steps, `i` no later than `j`.

Read aloud: a later configuration is at the same time or later. -/
theorem time_mono (R : RunFacts M S x) {i j : ℕ} (hij : i ≤ j) : x.time i ≤ x.time j :=
  monotone_nat_of_le_succ (f := fun i => x.time i) ((time_le_succ M) x R) hij

/-- The time is never negative: it starts at `0` and never decreases.

The variables:
- `M`: the model;
- `x`: the execution; `R`: the run's facts; `i`: the step.

Read aloud: every configuration is at a time at least `0`. -/
theorem time_nonneg (R : RunFacts M S x) (i : ℕ) : 0 ≤ x.time i := by
  have := (time_mono M) x R (Nat.zero_le i)
  rwa [R.time_zero] at this

/-- A configuration at an earlier time comes at an earlier step.

The variables:
- `M`: the model;
- `x`: the execution; `i`, `j`: two steps.

Read aloud: if the configuration after `i` steps is at an earlier time than the one after `j`
steps, then `i` is less than `j`. -/
theorem lt_of_time_lt (R : RunFacts M S x) {i j : ℕ} (h : x.time i < x.time j) : i < j := by
  by_contra hji
  exact absurd ((time_mono M) x R (Nat.le_of_not_lt hji)) (not_le.2 h)

/-! ## Honesty and activity read at a time, per step -/

/-- A validator outside `A.corruptedAtTime x t` is outside the adversary set after every step whose
time is at most `t`.

The variables:
- `M`: the model;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `v`: the validator; `t`:
  the time; `i`: the step.

Read aloud: honest at `t` is honest at every step up to `t`. -/
theorem not_mem_corrupted_of_le_time (_R : RunFacts M S x) {deadline} {ok : NamedObject V → Prop}
    {B : Type} {W : ViewVocab V B (NamedObject V)} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (_E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W) {v : V} {t : ℕ}
    (h : v ∉ A.corruptedAtTime x t) {i : ℕ} (hi : x.time i ≤ t) : v ∉ A.corrupted i :=
  (Activity.not_mem_corruptedAtTime.1 h) i hi

/-- A validator outside the adversary set at `t'` is outside it at every time `t ≤ t'`.

The variables:
- `M`: the model;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `v`: the validator; `t`,
  `t'`: the two times.

Read aloud: honest at a time is honest at every earlier time. -/
theorem not_mem_corruptedAtTime_of_le (_R : RunFacts M S x) {deadline} {ok : NamedObject V → Prop}
    {B : Type} {W : ViewVocab V B (NamedObject V)} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (_E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W) {v : V} {t t' : ℕ}
    (hle : t ≤ t') (h : v ∉ A.corruptedAtTime x t') : v ∉ A.corruptedAtTime x t :=
  Activity.not_mem_corruptedAtTime.2 fun i hi =>
    (Activity.not_mem_corruptedAtTime.1 h) i (le_trans hi (by exact_mod_cast hle))

/-- A validator outside the adversary set at `t` has been honest up to `t`.

The variables:
- `M`: the model;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `v`: the validator; `t`:
  the time.

Read aloud: honest at `t` is honest up to `t`. -/
theorem honestThroughTime_of_not_mem_corruptedAtTime (_R : RunFacts M S x) {deadline}
    {ok : NamedObject V → Prop} {B : Type} {W : ViewVocab V B (NamedObject V)} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ}
    (_E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W) {v : V} {t : ℕ}
    (h : v ∉ A.corruptedAtTime x t) : A.HonestThroughTime x t v :=
  Activity.not_mem_corruptedAtTime.1 h

/-- A validator not awake after step `i` and awake after a later step `j` was restarted at a step
from `i` to `j − 1`.

The variables:
- `x`: the execution; `E`: the environment's facts; `v`: the validator; `i ≤ j`: the two steps.

Read aloud: a validator that comes back up between two steps was restarted between them. -/
theorem exists_restart_of_not_awake {deadline} {ok : NamedObject V → Prop}
    {B : Type} {W : ViewVocab V B (NamedObject V)} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W) {v : V} {i j : ℕ} (hij : i ≤ j)
    (hi : v ∉ A.awake i) (hj : v ∈ A.awake j) :
    ∃ m : ℕ, i ≤ m ∧ m < j ∧ ∃ (tRestart : ℕ) (keep : Bool), x.lbl m = Event.restart v tRestart keep := by
  induction j, hij using Nat.le_induction with
  | base => exact absurd hj hi
  | succ j hij ih =>
      by_cases hvj : v ∈ A.awake j
      · obtain ⟨m, h1, h2, hm⟩ := ih hvj
        exact ⟨m, h1, by omega, hm⟩
      · obtain ⟨tR, keep, hl⟩ := E.restart_of_awake j v hvj hj
        exact ⟨j, hij, by omega, tR, keep, hl⟩

/-- A validator active throughout `[a, b]` and throughout `[a', c]`, where the second interval starts
no later than `b`, is active throughout `[a, c]`.

Why: a step whose time is in `[a, c]` has its time at most `b`, and is in the first interval, or
more than `b`, so at least `a'`, and is in the second.

The variables:
- `M`: the model;
- `x`: the execution; `R`: the run's facts (the time is monotone); `a`, `b`: the first interval; `a'`, `c`: the second; `v`: the validator.

Read aloud: two overlapping intervals of activity give activity throughout their union. -/
theorem mem_activeThroughout_union (R : RunFacts M S x) {a b a' c : ℝ} {v : V}
    (h₁ : v ∈ A.activeThroughout x a b) (h₂ : v ∈ A.activeThroughout x a' c) (hov : a' ≤ b) :
    v ∈ A.activeThroughout x a c :=
  Activity.mem_activeThroughout_of_forall fun i h1 h2 => by
    rcases le_or_gt (x.time i) b with hb | hb
    · exact Activity.mem_activeThroughout.1 h₁ i hb h2
    · exact Activity.mem_activeThroughout.1 h₂ i h1
        (le_trans hov (le_trans hb.le (R.time_mono (Nat.le_succ i))))

/-- A validator not awake after step `i` and awake after a later step `j` has a last restart `r`
from `i` to `j − 1`, after which it is awake after every step up to `j`.

The variables:
- `x`: the execution; `E`: the environment's facts; `v`: the validator; `i ≤ j`: the two steps;
- `r`: the step of the last restart.

Read aloud: a validator that comes back up between two steps stays up from its last restart
there. -/
theorem exists_last_restart_of_not_awake {deadline} {ok : NamedObject V → Prop}
    {B : Type} {W : ViewVocab V B (NamedObject V)} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W) {v : V} {i j : ℕ} (hij : i ≤ j)
    (hi : v ∉ A.awake i) (hj : v ∈ A.awake j) :
    ∃ r : ℕ, i ≤ r ∧ r < j ∧ (∃ (tRestart : ℕ) (keep : Bool), x.lbl r = Event.restart v tRestart keep) ∧
      ∀ l : ℕ, r < l → l ≤ j → v ∈ A.awake l := by
  classical
  obtain ⟨m, hm1, hm2, hm⟩ := (exists_restart_of_not_awake M) x E hij hi hj
  let P : ℕ → Prop := fun r => i ≤ r ∧ r < j ∧
    ∃ (tRestart : ℕ) (keep : Bool), x.lbl r = Event.restart v tRestart keep
  have hP : P (Nat.findGreatest P j) := Nat.findGreatest_spec (P := P) hm2.le ⟨hm1, hm2, hm⟩
  obtain ⟨h1, h2, h3⟩ := hP
  refine ⟨Nat.findGreatest P j, h1, h2, h3, fun l hl1 hl2 => ?_⟩
  by_contra hnl
  obtain ⟨m', hm'1, hm'2, hm'⟩ := (exists_restart_of_not_awake M) x E hl2 hnl hj
  exact Nat.findGreatest_is_greatest (P := P) (show Nat.findGreatest P j < m' by omega) hm'2.le
    ⟨by omega, hm'2, hm'⟩


--

/-! ## The ticks, per node -/

/-- A tick of `v` to the reading `t` is the step `x.tickStep v t`: a validator ticks at most once to
each reading (`E.tick_unique`).

The variables:
- `M`: the model;
- `R`: the run's facts; `E`: the environment's facts; `i`: the step; `v`: the validator; `t`: the
  reading.

Read aloud: the step of `v`'s tick to `t` is the one tick of `v` to `t`. -/
theorem tickStep_eq_of_lbl     {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {i : ℕ} {v : V} {t : ℕ} (hl : x.lbl i = Event.tick v t) : x.tickStep v t = i := by
  classical
  have hex : ∃ i : ℕ, x.lbl i = Event.tick v t := ⟨i, hl⟩
  unfold Trace.tickStep
  rw [dif_pos hex]
  exact E.tick_unique _ _ v t (Nat.find_spec hex) hl

/-- Two ticks of one validator to clock values `c < c'` are at steps `i < j`: the validator is
outside the adversary set at its tick `i` (`tick_active`), so a tick to `c'` at a step before `i`
would contradict `clock_mono`, and a tick to `c'` at `i` itself is the tick to `c`.

The variables:
- `M`: the model;
- `E`: the environment's facts; `i`, `j`: the two steps; `w`: the validator; `c`, `c'`: the two
  clock values.

Read aloud: when `w` ticks to `c` at step `i` and to `c'` at step `j`, and `c < c'`, then `i < j`. -/
theorem tick_lt_of_clock_lt {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {i j : ℕ} {w : V} {c c' : ℕ}
    (hi : x.lbl i = Event.tick w c) (hj : x.lbl j = Event.tick w c') (hcc : c < c') : i < j := by
  by_contra hle
  rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hle) with hlt | heq
  · have hhon : w ∉ A.corrupted i :=
      Activity.not_mem_corrupted_of_mem_active (E.tick_active i w c hi).1
    have := E.clock_mono j i w c' c hlt hhon (Or.inl hj) (Or.inl hi)
    omega
  · subst heq
    rw [hi] at hj
    cases hj
    exact lt_irrefl _ hcc

/-- A tick to the clock value `t` starts and ends at a real time in
`[t − ΔClockAhead, t + ΔClockBehind]`.

The variables:
- `M`: the model;
- `R`: the run's facts; `E`: the environment's facts; `i`: the step; `v`: the validator; `t`: the
  clock value.

Read aloud: the step of a tick to `t`, and the configuration it leaves, are within the two bounds of
the real time `t`. -/
theorem time_of_lbl_tick (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {i : ℕ} {v : V} {t : ℕ} (hl : x.lbl i = Event.tick v t) :
    ((t : ℝ) - ΔClockAhead ≤ x.time i ∧ x.time i ≤ t + ΔClockBehind) ∧
      ((t : ℝ) - ΔClockAhead ≤ x.time (i + 1) ∧ x.time (i + 1) ≤ t + ΔClockBehind) := by
  refine ⟨(E.tick_active i v t hl).2, ?_⟩
  rw [R.time_keep i (by rw [hl]; exact nofun)]
  exact (E.tick_active i v t hl).2

/-- A step that is not of the kind `other` keeps the time.

The variables:
- `M`: the model;
- `R`: the run's facts; `E`: the environment's facts; `i`: the step.

Read aloud: a tick, a wake or a delivery happens at the time of the step before it. -/
theorem time_succ_of_not_other (R : RunFacts M S x)
    
    {i : ℕ} (hl : x.lbl i ≠ Event.other) : x.time (i + 1) = x.time i := by
  exact R.time_keep i hl

/-- The step `x.stepBefore t` is at a real time less than `t`, and the step after it at a real time
at least `t`, for `t ≥ 1` (the time reaches `t`: `time_div`).

The variables:
- `M`: the model;
- `R`: the run's facts; `E`: the environment's facts; `t`: the time, at least `1`.

Read aloud: `x.stepBefore t` is the last step at a time before `t`, and the step after it is at the
time `t` or later. -/
theorem stepBefore_time (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {t : ℕ} (ht : 1 ≤ t) :
    x.time (x.stepBefore t) < t ∧ (t : ℝ) ≤ x.time (x.stepBefore t + 1) := by
  classical
  have hex : ∃ i : ℕ, (t : ℝ) ≤ x.time i := E.time_div t
  have hfa : x.firstAt t = Nat.find hex := by
    unfold Trace.firstAt
    rw [dif_pos hex]
  have hspec : (t : ℝ) ≤ x.time (Nat.find hex) := Nat.find_spec hex
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
    · rw [h0, R.time_zero] at hspec
      linarith
    · exact h0
  have hmin : ¬ (t : ℝ) ≤ x.time (Nat.find hex - 1) := Nat.find_min hex (by omega)
  have hsb : x.stepBefore t = Nat.find hex - 1 := by
    unfold Trace.stepBefore
    rw [hfa]
  have hsucc : Nat.find hex - 1 + 1 = Nat.find hex := by omega
  rw [hsb, hsucc]
  exact ⟨lt_of_not_ge hmin, hspec⟩

/-- The step after `x.stepBefore t` is at the time `t` or later, for every `t`: for `t ≥ 1` it is the
first step at a time at least `t` (`stepBefore_time`); at `t = 0` every time is at least `0`
(`time_zero`, `time_mono`).

The variables:
- `M`: the model;
- `R`: the run's facts; `E`: the environment's facts; `t`: the time.

Read aloud: the step right after the last step before `t` is at `t` or later. -/
theorem le_time_stepBefore_succ (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (t : ℕ) : (t : ℝ) ≤ x.time (x.stepBefore t + 1) := by
  rcases Nat.eq_zero_or_pos t with h0 | h1
  · subst h0
    have h00 := (time_mono M) x R (Nat.zero_le (x.stepBefore 0 + 1))
    rw [R.time_zero] at h00
    exact_mod_cast h00
  · exact ((stepBefore_time M) x R E h1).2

/-- A step that is not of the kind `other`, at a time before `t`, is before `x.stepBefore t`.

The variables:
- `M`: the model;
- `R`: the run's facts; `E`: the environment's facts; `i`: the step; `t`: the time.

Read aloud: a tick, a wake or a delivery before `t` comes before the step before `t`. -/
theorem lt_stepBefore_of_not_other (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {i t : ℕ} (hl : x.lbl i ≠ Event.other) (hi : x.time i < t) : i < x.stepBefore t := by
  have hk := R.time_keep i hl
  have h0 : (0 : ℝ) ≤ x.time i := R.time_zero ▸ (time_mono M) x R (Nat.zero_le i)
  have ht1 : 1 ≤ t := by
    have : (0 : ℝ) < t := lt_of_le_of_lt h0 hi
    exact_mod_cast this
  obtain ⟨-, h2⟩ := (stepBefore_time M) x R E ht1
  by_contra hle
  have := (time_mono M) x R (show x.stepBefore t + 1 ≤ i + 1 by omega)
  linarith

/-- For `t ≥ 1` and `v` active throughout `[t − ΔClockAhead, t + ΔClockBehind]`, the step of `v`'s
tick to `t` is a tick of `v` to `t`, at a real time in that window.

The variables:
- `M`: the model;
- `R`: the run's facts; `E`: the environment's facts; `t`: the clock value; `v`: the validator.

Read aloud: a validator active through the window of the clock value `t` ticks to `t` inside it. -/
theorem tickStep_spec (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {t : ℕ} (ht : 1 ≤ t) {v : V}
    (hv : v ∈ A.activeThroughout x ((t : ℝ) - ΔClockAhead) ((t : ℝ) + ΔClockBehind)) :
    x.lbl (x.tickStep v t) = Event.tick v t ∧ (t : ℝ) - ΔClockAhead ≤ x.time (x.tickStep v t) ∧
      x.time (x.tickStep v t) ≤ t + ΔClockBehind := by
  obtain ⟨i, hi, -⟩ := E.tick_of_mem_activeThroughout (fun _ _ h => R.time_mono h) hv le_rfl le_rfl ht
  exact ⟨x.lbl_tickStep ⟨i, hi⟩, E.time_tickStep ⟨i, hi⟩⟩

/-! ## The step before a time -/

/-- No step ticks at the time `0`, so `stepBefore M x 0` is the first step.

The variables:
- `M`: the model;
- `x`: the execution.

Read aloud: the configuration before the time `0` is the initial one. -/
theorem stepBefore_zero (R : RunFacts M S x) : x.stepBefore 0 = 0 := by
  classical
  have h0 : ((0 : ℕ) : ℝ) ≤ x.time 0 := by rw [R.time_zero]; simp
  have hex : ∃ i : ℕ, ((0 : ℕ) : ℝ) ≤ x.time i := ⟨0, h0⟩
  unfold Trace.stepBefore Trace.firstAt
  rw [dif_pos hex]
  have : Nat.find hex = 0 := (Nat.find_eq_zero hex).2 h0
  rw [this]

/-- A configuration is at a time before `t ≥ 1` exactly when its step comes no later than
`stepBefore M x t`.

The variables:
- `M`: the model;
- `x`: the execution; `i`: the step; `t`: the time.

Read aloud: the configurations before the time `t` are those up to the one the tick at `t` starts
from. -/
theorem time_lt_iff_le_stepBefore (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {i t : ℕ} (ht : 1 ≤ t) :
    x.time i < t ↔ i ≤ x.stepBefore t := by
  obtain ⟨h1, h2⟩ := (stepBefore_time M) x R E ht
  constructor
  · intro hi
    by_contra hlt
    have := (time_mono M) x R (show x.stepBefore t + 1 ≤ i by omega)
    linarith
  · intro hle
    have := (time_mono M) x R hle
    linarith

/-- A step comes strictly before `stepBefore M x t` exactly when the configuration it produces is
at a time before `t`, so its effect is in `x[stepBefore M x t]`. No condition on `t`: at `t = 0`
neither side holds.

The variables:
- `M`: the model;
- `x`: the execution; `i`: the step; `t`: the time.

Read aloud: the steps whose effect `stateBefore M x t` holds are those that end before the time
`t`. -/
theorem lt_stepBefore_iff (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {i t : ℕ} :
    i < x.stepBefore t ↔ x.time (i + 1) < t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [(stepBefore_zero M) x R]
    have := (time_mono M) x R (Nat.zero_le (i + 1))
    rw [R.time_zero] at this
    simp only [Nat.cast_zero, Nat.not_lt_zero, false_iff, not_lt]
    exact this
  · rw [show i < x.stepBefore t ↔ i + 1 ≤ x.stepBefore t from Nat.lt_iff_add_one_le,
      ← (time_lt_iff_le_stepBefore M) x R E ht]

/-- A configuration at the time `t ≥ 1` or later comes after `stepBefore M x t`.

The variables:
- `M`: the model;
- `x`: the execution; `j`: the step; `t`: the time.

Read aloud: a configuration at `t` or later is past the one the tick at `t` starts from. -/
theorem stepBefore_lt_of_le_time (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {j t : ℕ} (ht : 1 ≤ t)
    (hj : t ≤ x.time j) : x.stepBefore t < j := by
  by_contra hle
  have := ((time_lt_iff_le_stepBefore M) x R E ht).2 (Nat.le_of_not_lt hle)
  linarith

/-- A later time has a later step before it.

The variables:
- `M`: the model;
- `x`: the execution; `t`, `t'`: two times, `t` no later than `t'`.

Read aloud: the configuration before `t'` comes no earlier than the configuration before `t`. -/
theorem stepBefore_mono (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {t t' : ℕ} (h : t ≤ t') :
    x.stepBefore t ≤ x.stepBefore t' := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [(stepBefore_zero M) x R]
    exact Nat.zero_le _
  · have h1 := ((stepBefore_time M) x R E ht).1
    have h' : (t : ℝ) ≤ t' := by exact_mod_cast h
    exact ((time_lt_iff_le_stepBefore M) x R E (by omega)).1 (by linarith)

/-- A validator outside the adversary set after every step whose time is at most that of step `j` has been honest up to
step `j`: the steps up to `j` are at times at most that of `j`.

The variables:
- `M`: the model;
- `x`: the execution; `R`: the run's facts; `j`: the step; `v`: the validator.

Read aloud: honest up to the time of a step is honest up to that step. -/
theorem honestThrough_of_honestThroughTime (R : RunFacts M S x) {j : ℕ} {v : V}
    (h : A.HonestThroughTime x (x.time j) v) : x.HonestThrough A j v :=
  fun i hi => h i ((time_mono M) x R hi)

/-- A delivery at a time before `t` comes strictly before `stepBefore M x t`: the node state the
delivery produces, `x[j + 1][v].st`, is at or before the one `stateBefore M x t v` reads.

The variables:
- `M`: the model;
- `x`: the execution; `j`: the step of the delivery; `v`: the receiver; `sm`: the signed message
  delivered; `t`: the time.

Read aloud: what a validator receives before the time `t` is in its node state before `t`. -/
theorem deliver_before_of_time (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {j t : ℕ} {v : V}
    {sm : SignedMsg V (NamedObject V)} (hl : x.lbl j = Event.deliver v sm)
    -- the delivery happens before `t`
    (hj : x.time j < t) : j < x.stepBefore t := by
  exact (lt_stepBefore_of_not_other M) x R E (by rw [hl]; exact nofun) hj

/-! ## Lifting a per-step relation -/

/-- A relation on node states that every step from `stepBefore M x t` to `stepBefore M x t'` keeps
for the validator `v` holds from `v`'s node state before `t` to its node state before `t'`, for
`t ≤ t'`. The step before `t` comes no later than the step before `t'`
(`stepBefore_mono`).

The variables:
- `M`: the model;
- `x`: the execution; `R`: the relation; `t`, `t'`: two times, `t` no later than `t'`; `v`: the
  validator.

Read aloud: what each step keeps between `v`'s node states holds between `v`'s node state before
`t` and its node state before `t'`. -/
theorem rel_stateBefore_of_step (Run : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (R : M.N → M.N → Prop)
    -- the relation is reflexive
    (hrefl : ∀ n, R n n)
    -- the relation is transitive
    (htrans : ∀ n n' n'', R n n' → R n' n'' → R n n'')
    {t t' : ℕ} (h : t ≤ t') (v : V)
    -- every step from the one before `t` to the one before `t'` keeps the relation for `v`
    (hstep : ∀ i, x.stepBefore t ≤ i → i < x.stepBefore t' → R (x.st i v) (x.st (i + 1) v)) :
    R (x.stateBefore t v) (x.stateBefore t' v) := by
  exact rel_of_forall_step R hrefl htrans (fun i => x.st i v) ((stepBefore_mono M) x Run E h) hstep

/-- A relation on node states that every step from `j` to `stepBefore M x t` keeps for the
validator `v` holds from `v`'s node state at the step `j` to its node state before `t`, when the
configuration `x[j]` is at a time before `t ≥ 1`.

The variables:
- `M`: the model;
- `x`: the execution; `R`: the relation; `j`: the step; `t`: the time; `v`: the validator.

Read aloud: what each step keeps between `v`'s node states holds between `v`'s node state at a
configuration before `t` and its node state before `t`. -/
theorem rel_getElem_stateBefore (Run : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (R : M.N → M.N → Prop)
    -- the relation is reflexive
    (hrefl : ∀ n, R n n)
    -- the relation is transitive
    (htrans : ∀ n n' n'', R n n' → R n' n'' → R n n'')
    {j t : ℕ} (ht : 1 ≤ t)
    -- the configuration `x[j]` is at a time before `t`
    (hj : x.time j < t) (v : V)
    -- every step from `j` to the one before `t` keeps the relation for `v`
    (hstep : ∀ i, j ≤ i → i < x.stepBefore t → R (x.st i v) (x.st (i + 1) v)) :
    R (x.st j v) (x.stateBefore t v) := by
  exact rel_of_forall_step R hrefl htrans (fun i => x.st i v)
    (((time_lt_iff_le_stepBefore M) x Run E ht).1 hj) hstep

/-- A relation on node states that every step from `stepBefore M x t` to `j` keeps for the
validator `v` holds from `v`'s node state before `t` to its node state at the step `j`, when the
configuration `x[j]` is at the time `t ≥ 1` or later.

The variables:
- `M`: the model;
- `x`: the execution; `R`: the relation; `t`: the time; `j`: the step; `v`: the validator.

Read aloud: what each step keeps between `v`'s node states holds between `v`'s node state before
`t` and its node state at a configuration at `t` or later. -/
theorem rel_stateBefore_getElem (Run : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (R : M.N → M.N → Prop)
    -- the relation is reflexive
    (hrefl : ∀ n, R n n)
    -- the relation is transitive
    (htrans : ∀ n n' n'', R n n' → R n' n'' → R n n'')
    {t j : ℕ} (ht : 1 ≤ t)
    -- the configuration `x[j]` is at `t` or later
    (hj : t ≤ x.time j) (v : V)
    -- every step from the one before `t` to `j` keeps the relation for `v`
    (hstep : ∀ i, x.stepBefore t ≤ i → i < j → R (x.st i v) (x.st (i + 1) v)) :
    R (x.stateBefore t v) (x.st j v) := by
  exact rel_of_forall_step R hrefl htrans (fun i => x.st i v)
    (Nat.le_of_lt ((stepBefore_lt_of_le_time M) x Run E ht hj)) hstep

/-- The time of the configuration `stepBefore M x t` is at most `t`.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `t`: the time.

Read aloud: the configuration `stepBefore x t` is at a time at most `t`. -/
theorem time_stepBefore_le {S : Setup V} {A : Activity V}
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (t : ℕ) : x.time (x.stepBefore t) ≤ t := by
  have h0 : x.time 0 ≤ (t : ℝ) := by rw [R.time_zero]; positivity
  unfold Trace.stepBefore Trace.firstAt
  split_ifs with h
  · by_cases hz : Nat.find h = 0
    · rw [hz]; exact h0
    · exact (not_le.1 (Nat.find_min h (show Nat.find h - 1 < Nat.find h by omega))).le
  · exact h0

end GoldilocksCorrectness.Record.Proofs.Executions

