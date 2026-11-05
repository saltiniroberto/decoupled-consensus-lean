module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.PhaseDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.PhaseKitStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.PhaseFrameStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.PhaseChainStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestChainAfterHealingStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealingStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.LockProvenanceStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.SleepyStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestChainStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma80
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PhaseChain
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Wake
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Monotone
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ACStore
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ScoreACStore
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma79
public import GoldilocksCorrectness.Proofs.Executions.Lemma89f
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickWindowKit
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89f, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89f.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: the kit of times, sets, frames and locks,
the bundle `FrontHyps` of the hypotheses its theorems read, the base at slot `b₀`, the induction
over the live lock blocks, and Lemma 89f with the frame hypotheses its proof reads. The page's
routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff
  dutyWindowStart_le_voteTime dutyWindowStart_mono one_le_Δ slotStart_mono supportCutoff_eq
  supportCutoff_mono voteTime_eq voteTime_mono voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (compatible_symm')

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

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
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  compatible_of_ancestorEq_compatible)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution, and `x[i][v]` into a configuration, has the valid-index
-- predicate `fun _ _ => True`; this rule, local to the file, proves it at once
--. No statement and no proof term
-- changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## The kit: times and sets -/

/-- **A duty window starts before a recovery window inside it.** When `voteTime S.C s ≤ b + 3Δ` and
`max (Δ S) Δs ≤ b`, with `max (Δ S) Δs + 3Δ < 4Δk`, the duty window of slot `s` starts strictly before
`b − max (Δ S) Δs`, or both are `0` (the duty window's start is clamped at `0` in the first slots; the
arithmetic of `activeThroughout_of_dutyWindow`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `S`: the setup; `Δs`: the sync delay;
  `s`: the slot; `b`: the window's end.

Read aloud: the recovery window before `b` starts after the duty window's start, unless both are `0`. -/
theorem dutyWindowStart_le_sub_max (U : UniformSchedule M.toSlotLayout) (S : Setup V)
    {Δs : ℕ} {ΔClockAhead ΔClockBehind : ℝ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hA0 : 0 ≤ ΔClockAhead) (hB0 : 0 ≤ ΔClockBehind) {s b : ℕ}
    (hb : M.voteTime S.C s ≤ b + 3 * Δ S) (hcb : max (Δ S) Δs ≤ b) :
    M.dutyWindowStart S.C s < b - max (Δ S) Δs ∨
      (M.dutyWindowStart S.C s = 0 ∧ b - max (Δ S) Δs = 0) := by
  -- the bound on the sync delay, over the naturals: `max (Δ S) Δs + 3Δ < 4Δk`
  have hm : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have h : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h
  have hdw := U.dutyWindowStart_eq S s
  have hvt := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  omega

/-- **An honest active validator's window, inside its duty window.** A validator of
`honestActiveAt M S A x s` is active through every window `[a, e]` with `a` more than `ΔClockBehind`
after the protocol's duty window start of slot `s` and `e` more than `ΔClockAhead` before the support
cutoff of slot `s + 1`.

Why: it is active up to its tick to the cutoff (`honestActiveAt_window`), so
`mem_activeThroughout_of_mem_activeThroughoutToTick`. (The tick to the cutoff is at a real time at least
the cutoff minus `ΔClockAhead`; in the reader's second case the tick to a value at most the duty window's
start is at a real time at most that start plus `ΔClockBehind`, and the configurations before it are not
counted.)

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `s`: the slot; `v`: the
  validator; `a`, `e`: the window.

Read aloud: an honest active validator is active through every window inside its duty window. -/
theorem mem_activeThroughout_of_honestActiveAt {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {s : ℕ} {v : V} (hv : v ∈ honestActiveAt M S A x s) {a e : ℕ}
    (ha : ((duty_window_start S.C s : ℤ) : ℝ) + ΔClockBehind < a)
    (he : (e : ℝ) + ΔClockAhead < M.supportCutoff S.C (s + 1)) :
    v ∈ A.activeThroughout x a e :=
  (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E
    ((honestActiveAt_window M F) S A s v E hv) ha he

/-- **An updater's window, inside its duty window.** A validator of `updaterAt M S A x s` is active
through every window `[a, e]` with `a` more than `ΔClockBehind` after the protocol's duty window start
of slot `s + 1` and `e` more than `ΔClockAhead` before the support cutoff of slot `s + 1`.

Why: `mem_activeThroughout_of_mem_activeThroughoutToTick`, with the two clock bounds as for
`mem_activeThroughout_of_honestActiveAt`.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `s`: the slot; `v`: the
  updater; `a`, `e`: the window.

Read aloud: an updater is active through every window inside its duty window. -/
theorem mem_activeThroughout_of_updater {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {s : ℕ} {v : V} (hv : v ∈ updaterAt M S A x s) {a e : ℕ}
    (ha : ((duty_window_start S.C (s + 1) : ℤ) : ℝ) + ΔClockBehind < a)
    (he : (e : ℝ) + ΔClockAhead < M.supportCutoff S.C (s + 1)) :
    v ∈ A.activeThroughout x a e :=
  (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E hv ha he

/-- **An honest active validator's honesty, up to the support cutoff.** A validator of
`honestActiveAt M S A x s` is outside the adversary set after every step read as a time at most the
support cutoff of slot `s + 1`.

Why: the set's definition gives it after every step whose time is at most the cutoff.

The variables:
- `M`: the model;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `s`: the slot; `v`: the
  validator; `t`: the time.

Read aloud: an honest active validator of a slot is honest at every time up to the next support
cutoff. -/
theorem not_mem_corruptedAtTime_of_honestActiveAt {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {ok : NamedObject V → Prop}
    {B : Type} {W : ViewVocab V B (NamedObject V)} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    {s : ℕ} {v : V} (hv : v ∈ honestActiveAt M S A x s) {t : ℕ}
    (ht : t ≤ M.supportCutoff S.C (s + 1)) :
    v ∉ A.corruptedAtTime x t :=
  Activity.not_mem_corruptedAtTime.2 fun i hi =>
    Activity.not_mem_corruptedAtTime.1 (fun h => (Finset.mem_sdiff.1 hv).2 (Finset.mem_union_left _ h)) i
      (le_trans hi (by exact_mod_cast ht))

/-- **The awake half of an activity at a time.** A validator active after every step read as `t` is
awake after every step read as `t`.

The variables:
- `A`: the activity; `x`: the trace; `t`: the time; `v`: the validator.

Read aloud: active at a time is awake at it. -/
theorem mem_awakeAtTime_of_mem_activeAtTime {A : Activity V} {Msg N : Type}
    {x : Trace V Msg N} {t : ℕ} {v : V} (h : v ∈ A.activeAtTime x t) : v ∈ A.awakeAtTime x t :=
  Activity.mem_awakeAtTime.2 fun i h1 h2 =>
    Activity.mem_awake_of_mem_active (Activity.mem_activeAtTime.1 h i h1 h2)

/-- **The phase's awake premise, read for a validator honest at a time of the phase.** With the
premise `hAwake`, a validator outside the adversary set at a time `b` of
the phase is active in every configuration in force at a time of `[a, b]`, for `tGAT ≤ a`.

Why: a configuration after `i` steps in force at a time of `[a, b]` has `x.time i ≤ b ≤ tAwakeEnd` and
`tGAT ≤ a ≤ x.time (i + 1)`, so `hAwake` reads it; the validator is outside the adversary set after `i`
steps since `x.time i ≤ b`.

The variables:
- `M`: the model;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `tGAT`, `tAwakeEnd`:
  the phase; `hAwake`: the premise; `a`, `b`: the interval; `v`: the validator.

Read aloud: a validator honest at a time of the phase is active from any later start of the phase
up to that time. -/
theorem mem_activeThroughout_of_hAwake_honest_at {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {ok : NamedObject V → Prop}
    {B : Type} {W : ViewVocab V B (NamedObject V)} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W) {tGAT tAwakeEnd : ℕ}
    -- every validator outside the adversary set in a configuration in force at a time of `[tGAT, tAwakeEnd]` is awake in it
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    {a b : ℕ} (ha : tGAT ≤ a) (hb : b ≤ tAwakeEnd) {v : V} (hv : v ∉ A.corruptedAtTime x b) :
    v ∈ A.activeThroughout x a b := by
  refine Activity.mem_activeThroughout.2 fun i h1 h2 => ?_
  have hci : v ∉ A.corrupted i := Activity.not_mem_corruptedAtTime.1 hv i h1
  refine Activity.mem_active.2 ⟨hAwake i v (le_trans h1 (by exact_mod_cast hb)) ?_ hci, hci⟩
  exact le_trans (by exact_mod_cast ha) h2

/-- **The phase's awake premise for a shorter phase.** The premise `hAwake` over `[tGAT, T]` gives the
same premise over `[tGAT, T']` for `T' ≤ T`: every validator outside the adversary set in a configuration
in force at a time of `[tGAT, T']` is awake in it.

Why: such a configuration is in force at a time of `[tGAT, T]`.

The variables:
- `M`: the model;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `tGAT`, `T`: the phase;
  `hAwake`: the premise; `T'`: the shorter phase's end.

Read aloud: the awake premise of a phase holds for every shorter phase with the same start. -/
theorem hAwake_shorter {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {ok : NamedObject V → Prop}
    {B : Type} {W : ViewVocab V B (NamedObject V)} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W) {tGAT T T' : ℕ}
    -- every validator outside the adversary set in a configuration in force at a time of `[tGAT, T]` is awake in it
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ T → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hT : T' ≤ T) :
    ∀ (i : ℕ) (v : V), x.time i ≤ T' → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i :=
  fun i w h1 h2 hw => hAwake i w (le_trans h1 (by exact_mod_cast hT)) h2 hw

open Classical in
/-- **A validator active through a slot's duty window to the next support cutoff is an honest active
validator of the slot.** A validator active in every configuration in force at a time from `ΔClockAhead`
before the duty window's start of slot `s` to `ΔClockBehind` after the support cutoff of slot `s + 1` is in
`honestActiveAt M S A x s`.

Why: it ticks to the cutoff and is awake up to that tick
(`mem_activeThroughoutToTick_of_mem_activeThroughout`), and it is outside the adversary set after
every step read as the cutoff.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `A`: the activity; `x`: the execution; `R`: the run's facts; `E`: the environment's
  facts; `s`: the slot; `v`: the validator.

Read aloud: active through the slot's duties is honest active for the slot. -/
theorem mem_honestActiveAt_of_mem_activeThroughout (U : UniformSchedule M.toSlotLayout) {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {s : ℕ} {v : V} (hab : M.dutyWindowStart S.C s ≤ M.supportCutoff S.C (s + 1))
    (hv : v ∈ A.activeThroughout x ((M.dutyWindowStart S.C s : ℝ) - ΔClockAhead)
      ((M.supportCutoff S.C (s + 1) : ℝ) + ΔClockBehind)) :
    v ∈ honestActiveAt M S A x s := by
  have hn : v ∈ A.activeThroughout x (M.dutyWindowStart S.C s) (M.supportCutoff S.C (s + 1)) :=
    Activity.mem_activeThroughout_of_le (by linarith [E.ahead_nonneg]) (by linarith [E.behind_nonneg]) hv
  have h1 : 1 ≤ M.supportCutoff S.C (s + 1) :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot M.toSlotLayout F.sched) S s).2
  -- honest through the real time `ΔClockBehind` after the cutoff, so at every tick to the cutoff
  have hnB : v ∉ A.corruptedAtTime x ((M.supportCutoff S.C (s + 1) : ℝ) + ΔClockBehind) :=
    E.not_mem_corruptedAtTime_of_mem_activeThroughout R.time_zero (fun _ _ h => R.time_mono h)
      (by have : (M.dutyWindowStart S.C s : ℝ) ≤ M.supportCutoff S.C (s + 1) := by exact_mod_cast hab
          linarith [E.ahead_nonneg, E.behind_nonneg]) hv
  unfold honestActiveAt activeAt
  refine Finset.mem_sdiff.2 ⟨Activity.mem_awakeThroughoutToTick_of_mem_activeThroughoutToTick
    ((mem_activeThroughoutToTick_of_mem_activeThroughout M F) x R E h1
      (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_le_dutyWindowStart
        M.toSlotLayout F.sched U) S s) (by exact_mod_cast hab))
      ((activeThroughout_duty_window_start M F U) R E.ahead_nonneg hv)), fun h => ?_⟩
  rcases Finset.mem_union.1 h with h1 | h2
  · exact E.not_mem_corruptedAtTime_of_mem_activeThroughout R.time_zero (fun _ _ h => R.time_mono h)
      (by exact_mod_cast hab) hn h1
  · obtain ⟨k, w, hk, -, hvk⟩ := (Finset.mem_filter.1 h2).2
    exact hnB ((Activity.mem_corruptedAtTime (A := A) (x := x)).2
      ⟨k, (E.tick_active k w _ hk).2.2, hvk⟩)

/-- **A validator active through the duty window of slot `s + 1` to its support cutoff, the window widened by
the two clock bounds, is an updater of slot `s`.**

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `A`: the activity; `x`: the execution; `R`: the run's facts; `E`: the environment's
  facts; `s`: the slot; `v`: the validator.

Read aloud: active through the update's duty window is an updater. -/
theorem mem_updaterAt_of_mem_activeThroughout (U : UniformSchedule M.toSlotLayout) {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {s : ℕ} {v : V} (hab : M.dutyWindowStart S.C (s + 1) ≤ M.supportCutoff S.C (s + 1))
    (hv : v ∈ A.activeThroughout x ((M.dutyWindowStart S.C (s + 1) : ℝ) - ΔClockAhead)
      ((M.supportCutoff S.C (s + 1) : ℝ) + ΔClockBehind)) :
    v ∈ updaterAt M S A x s :=
  (mem_activeThroughoutToTick_of_mem_activeThroughout M F) x R E
    ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot M.toSlotLayout F.sched) S s).2
    (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_le_dutyWindowStart
        M.toSlotLayout F.sched U) S (s + 1)) (by exact_mod_cast hab))
    ((activeThroughout_duty_window_start M F U) R E.ahead_nonneg hv)

/-- **The members' windows.** With permanent corruption, every validator honest at a time from
`tGAT` to `tAwakeEnd` awake then, `tGAT` at most the duty window's start of slot `s_w`, the members
of each slot `s₁` from `s_w` to `s'` honest at the support cutoff of slot `s₁ + 1`, and that cutoff
of slot `s' + 1` at most `tAwakeEnd`: a member of slot `s₁` is awake and honest at every time from
the duty window's start of slot `s₁` to the support cutoff of slot `s₁ + 1`.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `Sched`: the schedule; `tGAT`, `tAwakeEnd`: the phase; `s_w`, `s'`: the ends
  of the range; `Hon`: the member sets; `s₁`: the slot; `v`: the member.

Read aloud: a member of slot `s₁` is awake and honest from the duty window's start of slot `s₁` to
the support cutoff of slot `s₁ + 1`. -/
theorem front_member_window (S : Setup V) (A : Activity V) (tGAT tAwakeEnd s_w s' s₁ : ℕ)
    (Hon : ℕ → Finset V) (v : V) {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hHon : ∀ s₁, s_w ≤ s₁ → s₁ ≤ s' → ∀ v ∈ Hon s₁,
      v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₁ + 1)))
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hsw : tGAT ≤ M.dutyWindowStart S.C s_w) (hEnd : M.supportCutoff S.C (s' + 1) ≤ tAwakeEnd)
    (h1 : s_w ≤ s₁) (h2 : s₁ ≤ s') (hv : v ∈ Hon s₁) :
    v ∈ A.activeThroughout x (M.dutyWindowStart S.C s₁) (M.supportCutoff S.C (s₁ + 1)) := by
  have hd := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_mono M.toSlotLayout F.sched) S h1
  have hc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show s₁ + 1 ≤ s' + 1 by omega)
  exact (mem_activeThroughout_of_hAwake_honest_at M F) R E hAwake (by omega) (by omega) (hHon s₁ h1 h2 v hv)

omit [RootOrder] in
/-- **The member sets shrink over a range.** When the set of slot `s₁ + 1` is inside that of slot
`s₁` for every slot from `s_w` to before `s'`, the set of a slot `b` is inside that of every slot
`a` from `s_w` to `b`, for `b ≤ s'`.

The variables:
- `M`: the model; `F`: its facts;
- `s_w`, `s'`: the ends of the range; `Hon`: the member sets.

Read aloud: the member sets shrink from slot to slot over the range. -/
theorem front_hon_anti (s_w s' : ℕ) (Hon : ℕ → Finset V)
    (hHonMono : ∀ s₁, s_w ≤ s₁ → s₁ < s' → Hon (s₁ + 1) ⊆ Hon s₁) :
    ∀ a b, s_w ≤ a → a ≤ b → b ≤ s' → Hon b ⊆ Hon a := by
  intro a b ha hab hb
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => exact subset_rfl
  | succ d ih =>
      exact (hHonMono (a + d) (by omega) (by omega)).trans (ih (by omega) (by omega))

/-! ## The kit: frames and locks -/

/-- **`StepFrameAt` holds for an ancestor.** When `StepFrameAt M S Sched x B s' w` holds and `C` is
`B` or an ancestor of `B`, `StepFrameAt M S Sched x C s' w` holds.

Why: a block compatible with `B` is compatible with `C`; a root that is `C` or an ancestor of it
is `B` or an ancestor of it, and a viable head descending from `B` descends from `C`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `B`, `C`: the blocks; `s'`: the slot;
  `w`: the member.

Read aloud: `StepFrameAt` relative to a block holds relative to each of its ancestors. -/
theorem stepFrameAt_of_ancestorEq (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (B C : Block V) (s' : ℕ) (w : V)
    (hCB : C.AncestorEq B)
    (h : StepFrameAt M S A x B s' w) : StepFrameAt M S A x C s' w := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, fun hR => ?_, ?_⟩
  · exact compatible_symm' (compatible_of_ancestorEq_compatible hCB (compatible_symm' h1))
  · obtain ⟨W, hW, hWv, hBW⟩ := h2 (ancestorEq_trans hR hCB)
    exact ⟨W, hW, hWv, ancestorEq_trans hCB hBW⟩
  · exact compatible_symm' (compatible_of_ancestorEq_compatible hCB (compatible_symm' h3))

/-- **A finalized block compatible later is compatible earlier.** In an execution where every time
is reached, when `v`'s finalized block before `t'` is compatible with `B` and `t ≤ t'`, `v`'s
finalized block before `t` is compatible with `B`.

Why: the earlier finalized block is an ancestor of the later one, or it.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `v`: the validator; `t ≤ t'`: the
  times; `B`: the block.

Read aloud: a finalized block compatible with `B` at a later time was compatible with `B` at every
earlier time. -/
theorem F_compatible_of_le (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (v : V) {t t' : ℕ}
    (h : t ≤ t') (B : Block V) (hc : (x.stateBefore t' v).finalized.compatible B = true) :
    (x.stateBefore t v).finalized.compatible B = true :=
  compatible_of_ancestorEq_compatible ((stateBefore_grows M F) x R E v h).2.1 hc

/-- **A held lock entry, with the update that added it.** In an execution that reaches every time, a lock entry `e`
that `u` holds at its own tick to `t` (in the state that tick starts from, `x.tickInput u t`) has the deadline of a lock
of some slot `σ` whose update ran at a clock value less than `t`; that update is an outcome `(n'', sent)` of `u`'s tick to
the support cutoff of slot `σ + 1`, from a state awake for slot `σ + 1`; it added an entry `e₀` with `e`'s deadline,
`e`'s block equal to `e₀`'s or an ancestor of it; and `e₀`'s block is the confirmation of slot `σ` that `u` holds right
after that cutoff, or an ancestor of it.

Why: Lemma 39 gives the slot, the update's outcome and its entry, on the update's saved confirmation or an ancestor of
it; `update_state_of_tick` identifies the update's saved confirmations with the state right after its tick; `u`'s clock
values are increasing over its ticks (`clock_mono`), so the cutoff is less than `t`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, the run's and the environment's facts; `t`: the
  clock value; `u`: the holder; `e`: the entry.

Read aloud: a lock entry a validator holds was added by its update of a slot, on the confirmation that update saved. -/
theorem lock_entry_update (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (t : ℕ) (u : V) (e : M.LE)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (he : e ∈ (x.tickInput u t).lockEntries) :
    ∃ σ : ℕ, e.d = S.C.t_ (σ + S.C.k) + 5 * S.C.Δ ∧ M.supportCutoff S.C (σ + 1) < t ∧
      ∃ (n'' : M.N) (sent : List (NamedObject V)),
        .ok (n'', sent) ∈ M.tick S.C S.P S.X (x.tickInput u (M.supportCutoff S.C (σ + 1)))
          ((M.supportCutoff S.C (σ + 1) : ℕ) : Int) ∧
        GoldilocksCorrectness.Record.Statements.Routines.AwakeFor M S.C (x.tickInput u (M.supportCutoff S.C (σ + 1))) (σ + 1) ∧
        ∃ e₀ ∈ M.lockEntries n'', e₀.d = e.d ∧ e.B.AncestorEq e₀.B ∧
          ∃ C' : Block V,
            (x.tickOutput u (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C' ∧
            e₀.B.AncestorEq C' := by
  have he' : e ∈ (x.st (x.tickStep u t) u).lockEntries := he
  obtain ⟨σ, hd, hk, hl, ⟨τ, hτ, hτle⟩, h3⟩ :=
    (GoldilocksCorrectness.Record.Statements.Executions.lem39_lock_entry_provenance M F U) S A x R
      (x.tickStep u t) u e E he'
  -- the outcome of `u`'s tick at the support cutoff of slot `σ + 1` that the state right after it
  -- holds
  obtain ⟨n'', sent, hrun, hA, hsave, -⟩ := (update_state_of_tick M F U) S A x R σ u E hl ⟨τ, hτ, hτle⟩
  obtain ⟨e₀, he₀, hd₀, -, -, ⟨C', hC', hBC⟩, -, heB₀, -⟩ := h3 n'' sent hrun hA
  -- the tick to the cutoff comes before the tick to `t`, so the cutoff is less than `t`
  have hexT : ∃ i : ℕ, x.lbl i = Event.tick u t := by
    by_contra hno
    have h0 : x.tickStep u t = 0 := by
      unfold Trace.tickStep
      rw [dif_neg hno]
    omega
  have hlT := x.lbl_tickStep hexT
  have hle := E.clock_mono _ _ u _ _ hk (E.not_mem_corrupted_of_tick hlT) (Or.inl hl) (Or.inl hlT)
  have hne : M.supportCutoff S.C (σ + 1) ≠ t := fun h => by
    have hl' : x.lbl (x.tickStep u (M.supportCutoff S.C (σ + 1))) = Event.tick u t := by
      rw [hl, h]
    have := E.tick_unique _ _ u _ hl' hlT
    omega
  refine ⟨σ, hd, lt_of_le_of_ne hle hne, n'', sent, hrun, hA, e₀, he₀, hd₀, heB₀, C', ?_, hBC⟩
  rw [hsave]
  exact hC'

/-- **A held lock entry is on its holder's saved confirmation.** In an execution that reaches every
time, a lock entry `e` that `u` holds at its own tick to `t` (in the state that tick starts from,
`x.tickInput u t`) has the deadline of a lock of some slot `σ` whose update ran at a clock value less
than `t`, and `e`'s block is the confirmation of slot `σ` that `u` holds right after
the support cutoff of slot `σ + 1`, or an ancestor of it.

Why: Lemma 39 gives the slot, the update's answer and its entry, on the update's saved
confirmation or an ancestor of it, and the trace from the added entry's block to `e`'s;
`update_state_of_lock_entry` identifies the update's answer with the state right after its tick.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `u`: the holder;
  `e`: the entry.

Read aloud: a lock entry a validator holds is on its holder's saved confirmation of the lock's slot.
-/
theorem lock_entry_confirmation (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (t : ℕ) (u : V) (e : M.LE)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (he : e ∈ (x.tickInput u t).lockEntries) :
    ∃ σ : ℕ, e.d = S.C.t_ (σ + S.C.k) + 5 * S.C.Δ ∧ M.supportCutoff S.C (σ + 1) < t ∧
      ∃ C' : Block V,
        (x.tickOutput u (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C' ∧
        e.B.AncestorEq C' := by
  obtain ⟨σ, hd, hcut, -, -, -, -, e₀, -, -, heB₀, C', hsv, hBC⟩ := (lock_entry_update M F U) S A x R t u e E he
  exact ⟨σ, hd, hcut, C', hsv, ancestorEq_trans heB₀ hBC⟩

/-- **The lock invariant relative to the live lock blocks.** For every family `𝓒` holding the
block of every lock entry `u` holds live in the state its own tick to the vote time of slot `s + 1`
starts from, `u` satisfies
`LiveLocksOnFamilyAt M S Sched x 𝓒 s`.

Why: every entry the revocation of slot `s + 1` leaves is on an ancestor of the block of a live
entry of its input (Lemma 38), an entry of `u`'s state.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `𝓒`: the family; `s`: the slot;
  `u`: the validator.

Read aloud: when a family holds every live lock block of `u`, the locks the revocation of slot
`s + 1` leaves at `u` are on the family's blocks. -/
theorem liveLocksOnFamilyAt_of_live (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (𝓒 : Block V → Prop) (s : ℕ) (u : V)
    (h𝓒 : ∀ e ∈ (x.tickInput u (M.voteTime S.C (s + 1))).lockEntries,
      M.is_live (x.tickInput u (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → 𝓒 e.B) :
    LiveLocksOnFamilyAt M S A x 𝓒 s u := by
  -- every outcome of `u`'s tick at the vote time of slot `s + 1` revoked the locks there
  refine (liveLocksOnFamilyAt_of_locksRevoked M F U) S A x R E 𝓒 s u (fun n' hR e he _ => ?_)
  obtain ⟨e₁, he₁, hl₁, -, hee₁, -⟩ :=
    GoldilocksCorrectness.Record.Statements.Routines.lem38_revoke_locks_entries_moved
      (Nat.le_add_left 1 s) hR e he
  exact ⟨e₁.B, h𝓒 e₁ he₁ hl₁, hee₁⟩

/-- **The confirmations of a slot extend a block its votes extend (Lemma 78).** In an execution
where every time is reached, corruption is permanent, blocks and Goldfish votes are delivered
within `Δ` after `GST`, a root names one block among what honest
validators hold, a block reaches a validator only once it holds the parent, and nobody votes in an
honest validator's name: if `GST` is at most the vote time of slot `s`; `Hon` is a set of honest
active validators of slot `s` with more than half of the committee of slot `s`; every slot-`s` vote
of a member of `Hon` is its vote for a block it holds that is `C` or a descendant of `C`; `v` is an
updater of slot `s`; and `v`'s finalized block before the support cutoff of slot `s + 1` is
compatible with `C` — then `C` is an ancestor of, or equal to, the confirmation of slot `s` that
`v` holds right after that cutoff.

Why: `chainInvFor_updater_confirmation`'s proof, which reads only the first clause of the
invariant.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot; `Hon`: the voters; `C`: the block; `v`: the updater.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C s`: Lemma 78,
which the proof calls at slot `s`, reads them up to the real time of `v`'s own tick to that cutoff.

Read aloud: when a majority of slot `s`'s committee votes for `C` or its descendants, every
updater's confirmation of slot `s` is `C` or a descendant of `C`. -/
theorem confirmations_of_votes_clause (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hon : Finset V) (C : Block V) (v : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hHon : Hon ⊆ honestActiveAt M S A x s)
    (hCommittee : |S.P.committee s| < 2 * |S.P.committee s ∩ Hon|)
    (hC1 : ∀ u ∈ Hon, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C s)).tree,
        vote = GoldfishVote.mk u s H_u.root ∧ C.AncestorEq H_u)
    (hv : v ∈ updaterAt M S A x s)
    (hF : (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.compatible C = true) :
    ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C' →
      C.AncestorEq C' := by
  -- the voters: the committee members of `Hon`, each voting for a block it holds on `C`'s chain
  obtain ⟨H, hH⟩ := (voters_of_votes_clause M F U) S A x R s (S.P.committee s ∩ Hon) C E hSkew
    (fun u hu => ⟨hHon (Finset.mem_inter.1 hu).2, (Finset.mem_inter.1 hu).1⟩)
    (fun u hu => hC1 u (Finset.mem_inter.1 hu).2)
  -- `v`'s tick to the support cutoff of slot `s` (inside its reader), for the roots
  obtain ⟨kR, hkR, -⟩ := (updater_reader_gives_core_window M F U) x R E hΔs hSkew hv
  -- each voter is awake and honest from the duty window's start of slot `s + 1` up to its tick to the support cutoff
  -- of slot `s + 1`
  have hUpdU : ∀ u ∈ S.P.committee s ∩ Hon, u ∈ updaterAt M S A x s := fun u hu =>
    Activity.mem_activeThroughoutToTick_of_le (GoldilocksCorrectness.Proofs.Routines.duty_window_start_mono S (Nat.le_succ s))
      (E.mem_activeThroughoutToTick_of_awakeThroughoutToTick
        (Finset.mem_sdiff.1 (hHon (Finset.mem_inter.1 hu).2)).1)
  exact (GoldilocksCorrectness.Record.Statements.Executions.lem78_update_confirmation_extends_voter_majority_chain M F U)
    S A x R GST s (S.P.committee s ∩ Hon) H C v E hNet hSkew hRedeliver Sy hΔs
    ((roots_at_own_tick_of_per_tick M F) x E hRoots hkR) hParent hOwner hGST
    (fun u hu => ⟨(Finset.mem_inter.1 hu).1,
      (not_mem_corrupted_tickStep_of_outside_at_honest_ticks M F) x E hv
        (fun hX => (Finset.mem_sdiff.1 (hHon (Finset.mem_inter.1 hu).2)).2 (Finset.mem_union_right _ hX)),
      (hH u hu).1, (hH u hu).2.1, (hH u hu).2.2⟩)
    (fun u hu => (holder_window_of_updater_reader M F U) x R E hΔs hSkew hGST (hUpdU u hu))
    (by
      unfold Trace.tickInput
      exact (GoldilocksCorrectness.Record.Proofs.Routines.voters_count_lt_of_committee_majority M F)
        ((GoldilocksCorrectness.Record.Statements.Executions.pool_committee_of_exec M F) S A x R E _ v s)
        ((committee_sdiff_lt M F) _ _ hCommittee))
    hv hF

/-! ## The hypotheses of the copy, bundled -/

/-- `FrontHyps M S Sched x GST tGAT tAwakeEnd s_w s' Hon`: the hypotheses of `lem89fq_front` the
kit theorems of this file read, but `hs'` and `hRootsOn`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the phase; `s_w`: a slot whose duty window starts
  at or after `tGAT`; `s'`: the slot of the conclusion; `Hon`: the member sets.

Read aloud: the hypotheses of Lemma 89f its kit reads, bundled. -/
structure FrontHyps (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (GST tGAT tAwakeEnd s_w s' : ℕ) (Hon : ℕ → Finset V) (Δs : ℕ) (release : (NamedObject V) → Option ℕ) (ΔRedeliver : ℕ) (ΔClockAhead ΔClockBehind : ℝ) (ΔNet : ℕ) : Prop where
  /-- The environment's facts on the trace, for the delay `(Δ S)` from `GST`. -/
  E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST release acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks
  /-- The network delay and the two clock bounds fit in the delay `Δ S`. -/
  hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S
  /-- The two clock bounds together are less than one delay `Δ S`. -/
  hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S
  /-- A re-delivery after the receiver's clock reaches an object's release clock value, plus both clock bounds, fits in one delay `Δ S`. -/
  hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S
  /-- What an honest validator active at a time `t` would serve at `t` reaches every validator active
  from `t` within `Δs` of the later of `t` and `GST`. -/
  Sy : SyncedWithin A x (servesMin M S.C) acObject release ΔRedeliver Δs GST
  /-- The sync delay is at most the protocol's slow window less three delays. -/
  hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k
  /-- A root names one block among what honest validators hold, until the support cutoff of
  slot `s'`. -/
  hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C s')
  /-- Roots name blocks also up to the real time of every validator's tick to a clock value at most the support cutoff of
  slot `s'`. -/
  hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s' →
    RootsNameBlocksUntil M A x (x.time k)
  /-- A block reaches a validator only once it holds the parent. -/
  hParent : ParentHeldAtDelivery M x
  /-- Nobody votes in an honest validator's name. -/
  hOwner : VotesCastByOwner M A x
  /-- The network is synchronous from `tGAT` on. -/
  hGST : GST ≤ tGAT
  /-- The recovery delay after `GST` has elapsed by the view freeze of slot `s_w`. -/
  hGSTw : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s_w
  /-- The set of slot `s₁ + 1` is inside that of slot `s₁`, from `s_w` to before `s'`. -/
  hHonMono : ∀ s₁, s_w ≤ s₁ → s₁ < s' → Hon (s₁ + 1) ⊆ Hon s₁
  /-- Every member of the set of slot `s₁` is honest at the support cutoff of slot `s₁ + 1`. -/
  hHon : ∀ s₁, s_w ≤ s₁ → s₁ ≤ s' → ∀ v ∈ Hon s₁,
    v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₁ + 1))
  /-- Every validator honest at a time from `tGAT` to `tAwakeEnd` is awake then. -/
  hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
    v ∉ A.corrupted i → v ∈ A.awake i
  /-- At every slot of the phase, every validator honest at the slot's update is an honest active validator and an
  updater of the slot. -/
  hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
    ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
      v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s
  /-- The committee of every slot from `s_w + k` to `s'` has its majority in the slot's set. -/
  hCommittees : ∀ s₁, s_w + S.C.k ≤ s₁ → s₁ ≤ s' →
    (S.P.committee s₁).card < 2 * (S.P.committee s₁ ∩ Hon s₁).card
  /-- The duty window of slot `s_w` starts at or after `tGAT`. -/
  hsw : tGAT ≤ M.dutyWindowStart S.C s_w
  /-- The support cutoff of slot `s' + 1` is at most `tAwakeEnd`. -/
  hEnd : M.supportCutoff S.C (s' + 1) ≤ tAwakeEnd
  /-- At every slot `s₁` from `s_w + k − 1` to `s' − 1`, every member of `Hon (s₁ + 1)` satisfies
  `StepFrameAt M` relative to every confirmation a member of `Hon (σ + 1)` saved for a slot `σ`
  from `s_w + k − 1` to `s₁`. -/
  hFrame : ∀ s₁, s_w + S.C.k - 1 ≤ s₁ → s₁ < s' →
    ∀ σ, s_w + S.C.k - 1 ≤ σ → σ ≤ s₁ → ∀ v ∈ Hon (σ + 1), ∀ C : Block V,
      (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C →
      ∀ w ∈ Hon (s₁ + 1), StepFrameAt M S A x C s₁ w

namespace FrontHyps
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd s_w s' : ℕ} {Hon : ℕ → Finset V} {Δs : ℕ}

/-- The members' windows, read off the bundle (`front_member_window`).

The variables:
- `M`: the model; `F`: its facts;
- `H`: the bundle; `s₁`: the slot.

Read aloud: under the bundle, a member of a slot is awake and honest through that slot's duty
window. -/
theorem window {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (H : FrontHyps M S A x GST tGAT tAwakeEnd s_w s' Hon Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (R : RunFacts M S x) (s₁ : ℕ) (h1 : s_w ≤ s₁)
    (h2 : s₁ ≤ s') : ∀ v ∈ Hon s₁,
      v ∈ A.activeThroughout x (M.dutyWindowStart S.C s₁) (M.supportCutoff S.C (s₁ + 1)) :=
  fun v hv => (GoldilocksCorrectness.Record.Proofs.Executions.front_member_window M F) S A tGAT tAwakeEnd s_w s' s₁ Hon v R H.E
    H.hHon H.hAwake H.hsw H.hEnd h1 h2 hv

/-- The member sets shrink over the range, read off the bundle (`front_hon_anti`).

The variables:
- `M`: the model; `F`: its facts;
- `H`: the bundle; `a ≤ b`: the two slots.

Read aloud: under the bundle, the member set of a later slot is inside that of an earlier one. -/
theorem anti {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (H : FrontHyps M S A x GST tGAT tAwakeEnd s_w s' Hon Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (a b : ℕ) (ha : s_w ≤ a)
    (hab : a ≤ b) (hb : b ≤ s') : Hon b ⊆ Hon a :=
  (GoldilocksCorrectness.Record.Proofs.Executions.front_hon_anti M F) s_w s' Hon H.hHonMono a b ha hab hb

/-- `GST` is at most the vote time of every slot from `s_w` on.

The variables:
- `M`: the model; `F`: its facts;
- `H`: the bundle; `s`: the slot.

Read aloud: under the bundle, the network is synchronous from the vote time of every slot from `s_w`
on. -/
theorem gst {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (H : FrontHyps M S A x GST tGAT tAwakeEnd s_w s' Hon Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (s : ℕ) (h : s_w ≤ s) :
    GST ≤ M.voteTime S.C s := by
  have h1 := H.hGST
  have h2 := H.hsw
  have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_mono M.toSlotLayout F.sched) S h
  have h4 := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_le_voteTime M.toSlotLayout F.sched) S s
  omega

/-- `GST` is at least one delay or one sync delay before the support cutoff of every slot from `s_w`
on that is at least `S.C.k`.

Why: `GST ≤ tGAT ≤ M.dutyWindowStart S.C s`, and the duty window starts `4 Δ k` before the vote time
(`dutyWindowStart_cases`), while `Δs + 3 Δ ≤ 4 Δ k`; when the duty window is cut at `0`, `GST = 0`
and the support cutoff of a slot at least `k` is at least `4 Δ k + 2 Δ`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `H`: the bundle; `s`: the slot.

Read aloud: under the bundle, the network is synchronous one sync delay before the support cutoff of
every slot from `s_w` on, past the first `k` slots. -/
theorem gstSync (U : UniformSchedule M.toSlotLayout) {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (H : FrontHyps M S A x GST tGAT tAwakeEnd s_w s' Hon Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    (s : ℕ) (h : s_w ≤ s) (hk : S.C.k ≤ s) :
    GST + max (Δ S) Δs ≤ M.supportCutoff S.C s := by
  have h1 := H.hGST
  have h2 := H.hsw
  have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_mono M.toSlotLayout F.sched) S h
  have h4 := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S s
  have h5 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have h6 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have h7 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  -- the bundle's sync bound, with both clock bounds nonnegative, read on the natural numbers
  have h8 : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have hA := H.E.ahead_nonneg
    have hB := H.E.behind_nonneg
    have hR := H.hΔs
    have : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  have h9 := Nat.mul_le_mul_left (4 * Δ S) hk
  have := le_max_left (Δ S) Δs
  have := le_max_right (Δ S) Δs
  rcases max_cases (Δ S) Δs with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] at h8 ⊢ <;> omega

/-- The members of a slot are honest active validators of it.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `H`: the bundle; `s₁`: the slot.

Read aloud: under the bundle, the members of a slot are honest active validators of it. -/
theorem honestActive (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (H : FrontHyps M S A x GST tGAT tAwakeEnd s_w s' Hon Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (s₁ : ℕ)
    (R : RunFacts M S x) (h1 : s_w ≤ s₁) (h2 : s₁ ≤ s') : Hon s₁ ⊆ honestActiveAt M S A x s₁ := by
  intro u hu
  have hd := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_mono M.toSlotLayout F.sched) S h1
  have hc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
    (show s₁ + 1 ≤ s' + 1 by omega)
  exact (H.hActive s₁ (le_trans H.hsw hd) (le_trans hc H.hEnd) u (H.hHon s₁ h1 h2 u hu)).1

/-- The members of a slot are updaters of it.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `H`: the bundle; `s₁`: the slot.

Read aloud: under the bundle, the members of a slot are updaters of it. -/
theorem updater (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (H : FrontHyps M S A x GST tGAT tAwakeEnd s_w s' Hon Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (s₁ : ℕ)
    (R : RunFacts M S x) (h1 : s_w ≤ s₁) (h2 : s₁ ≤ s') : Hon s₁ ⊆ updaterAt M S A x s₁ := by
  intro u hu
  have hd := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_mono M.toSlotLayout F.sched) S h1
  have hc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
    (show s₁ + 1 ≤ s' + 1 by omega)
  exact (H.hActive s₁ (le_trans H.hsw hd) (le_trans hc H.hEnd) u (H.hHon s₁ h1 h2 u hu)).2

/-- Every member of the committee of a slot in the slot's set put a slot-`s₁` Goldfish vote on the
wire at its tick at the vote time of slot `s₁` (`honest_votes_of_window`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `H`: the bundle; `s₁`: the slot.

Read aloud: under the bundle, every member of a slot's committee sends its Goldfish vote of that
slot. -/
theorem voters (R : RunFacts M S x) (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (H : FrontHyps M S A x GST tGAT tAwakeEnd s_w s' Hon Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (s₁ : ℕ)
    (h1 : s_w ≤ s₁) (h2 : s₁ ≤ s') :
    ∀ u ∈ S.P.committee s₁ ∩ Hon s₁, u ∈ Hon s₁ ∧ u ∈ S.P.committee s₁ ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s₁ ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s₁) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i := by
  intro u hu
  obtain ⟨hK, huH⟩ := Finset.mem_inter.1 hu
  -- `u` is an honest active validator of slot `s₁` (the bundle's `hActive`), so active from the duty
  -- window's start up to its tick to the vote time (`hSkew`); that tick starts awake since then
  have hw := (GoldilocksCorrectness.Record.Proofs.Executions.voteTime_tick_window_of_honestActiveAt M F U) S A x R s₁ u H.E
    H.hSkew (H.honestActive M F U s₁ R h1 h2 huH)
  obtain ⟨k', hl, hAw⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.tick_and_wake_of_tick_window M F U) S A x R s₁ u H.E hw
  obtain ⟨vote, hvi, hvs, hsent⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.honest_votes_of_window M F U) S A x R s₁ u H.E
    hl hAw hK
  exact ⟨huH, hK, vote, hvi, hvs, k', hl, hsent⟩

/-- Roots name blocks until every time at most the support cutoff of slot `s'`, read off the
bundle.

The variables:
- `M`: the model; `F`: its facts;
- `H`: the bundle; `t`: the time.

Read aloud: under the bundle, roots name blocks until every time up to the support cutoff of slot
`s'`. -/
theorem rootsAt {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (H : FrontHyps M S A x GST tGAT tAwakeEnd s_w s' Hon Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {t : ℕ}
    (ht : t ≤ M.supportCutoff S.C s') : RootsNameBlocksUntil M A x t :=
  (GoldilocksCorrectness.Record.Statements.Executions.RootsNameBlocksUntil.mono M) ht H.hRoots


/-- Roots name blocks up to the real time of every validator's tick to a clock value at most `c₀`, for every `c₀` at most
the support cutoff of slot `s'`, read off the bundle.

The variables:
- `M`: the model; `F`: its facts;
- `H`: the bundle; `c₀`: the clock value.

Read aloud: under the bundle, roots name blocks up to every tick to a clock value at most `c₀`. -/
theorem rootsTickAt {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (H : FrontHyps M S A x GST tGAT tAwakeEnd s_w s' Hon Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {c₀ : ℕ}
    (hc₀ : c₀ ≤ M.supportCutoff S.C s') :
    ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ c₀ → RootsNameBlocksUntil M A x (x.time k) :=
  fun k u c hk hc => H.hRootsTick k u c hk (le_trans hc hc₀)

end FrontHyps

/-! ## The base -/

/-- **The carry, one slot.** Under the bundle, at a slot `s₁` from `s_w + k` with `s₁ + 1 ≤ s'`:
when `StepFrameAt M S Sched x B s₁ w` holds at every member `w` of `Hon (s₁ + 1)`,
`HonestChainExtends` at slot `s₁` for `Hon s₁` relative to `B` gives it at slot `s₁ + 1` for
`Hon (s₁ + 1)`.

Why: `lem79_step_sets`, with the honest voters `S.P.committee s ∩ Hon s` of each slot and the
counting from the committee majorities (`counting_of_committee_majority`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `H`: the bundle; `s₁`: the slot; `B`: the block.

Read aloud: under the bundle, `HonestChainExtends` relative to `B` carries from one slot's members
to the next slot's, when the next slot's members satisfy `StepFrameAt` relative to `B`. -/
theorem front_carry_step (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {GST tGAT tAwakeEnd s_w s' : ℕ} {Hon : ℕ → Finset V}
    (H : FrontHyps M S A x GST tGAT tAwakeEnd s_w s' Hon Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (s₁ : ℕ) (h1 : s_w + S.C.k ≤ s₁)
    (h2 : s₁ + 1 ≤ s') (B : Block V)
    (hSt : ∀ w ∈ Hon (s₁ + 1), StepFrameAt M S A x B s₁ w)
    (hInv : HonestChainExtends M S A x (Hon s₁) B s₁) :
    HonestChainExtends M S A x (Hon (s₁ + 1)) B (s₁ + 1) := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hA0 := H.E.ahead_nonneg
  have hB0 := H.E.behind_nonneg
  have hs₁w : s_w ≤ s₁ := by omega
  have hc : M.supportCutoff S.C (s₁ + 1) ≤ M.supportCutoff S.C s' :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h2
  have hHA' := H.honestActive M F U (s₁ + 1) R (by omega) h2
  -- the members of slot `s₁ + 1`, active up to their ticks to the vote time of slot `s₁ + 1`, inside their windows as
  -- honest active validators of slot `s₁ + 1`
  have hvt := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₁ + 1)
  have hvt2 : M.voteTime S.C (s₁ + 1 + 1) = M.voteTime S.C (s₁ + 1) + 4 * Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ M.toSlotLayout F.sched U) S (s₁ + 1)
  have hc2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s₁ + 1 + 1)
  have hss1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s₁ + 1)
  have hss0 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s₁
  rw [Nat.mul_add, Nat.mul_one] at hss1
  have hdN : M.dutyWindowStart S.C (s₁ + 1) ≤ M.slotStart S.C s₁ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_le_slotStart M.toSlotLayout F.sched) S s₁
  have hdv : M.dutyWindowStart S.C (s₁ + 1) + 5 * Δ S ≤ M.voteTime S.C (s₁ + 1) := by omega
  have hvc : M.voteTime S.C (s₁ + 1) + 4 * Δ S ≤ M.supportCutoff S.C (s₁ + 1 + 1) := by omega
  have hdvR : ((M.dutyWindowStart S.C (s₁ + 1) : ℕ) : ℝ) + 5 * Δ S ≤ ((M.voteTime S.C (s₁ + 1) : ℕ) : ℝ) := by
    exact_mod_cast hdv
  have hvcR : ((M.voteTime S.C (s₁ + 1) : ℕ) : ℝ) + 4 * Δ S ≤ ((M.supportCutoff S.C (s₁ + 1 + 1) : ℕ) : ℝ) := by
    exact_mod_cast hvc
  have hdle := (duty_window_start_le_real M F U) S (s₁ + 1)
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hSk := H.hSkew
  have hwinV : ∀ v ∈ Hon (s₁ + 1),
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s₁ + 1)) (M.voteTime S.C (s₁ + 1)) := by
    intro v hv
    refine (mem_activeThroughoutToTick_of_le_end_int M) x R H.E (by omega) (by linarith) (by linarith)
      ((honestActiveAt_window M F) S A (s₁ + 1) v H.E (hHA' hv))
  exact (lem79_step_sets M F U) S A x R GST s₁ (Hon s₁) (Hon (s₁ + 1))
    (fun s => S.P.committee s ∩ Hon s) B H.E H.hNet H.hSkew H.hRedeliver H.Sy H.hΔs
    (H.rootsTickAt M F hc) H.hParent H.hOwner (H.gstSync M F U s₁ hs₁w (by omega)) hInv
    (H.hHonMono s₁ hs₁w (by omega)) (H.updater M F U s₁ R hs₁w (by omega)) hwinV
    (H.updater M F U (s₁ + 1) R (by omega) h2)
    (fun u hu hX => (Finset.mem_sdiff.1 (hHA' hu)).2 (Finset.mem_union_right _ hX))
    (H.voters M F R U s₁ hs₁w (by omega)) (H.voters M F R U (s₁ + 1) (by omega) h2)
    (fun w _ votes sv hcv => ((counting_of_committee_majority_st M F) S A x R H.E s₁
      (x.tickStep w (M.voteTime S.C (s₁ + 1))) (Hon s₁) w (H.hCommittees s₁ (by omega) (by omega))).2.2 votes sv hcv)
    (fun v _ => ((counting_of_committee_majority_st M F) S A x R H.E (s₁ + 1)
      (x.tickStep v (M.supportCutoff S.C (s₁ + 1 + 1))) (Hon (s₁ + 1)) v (H.hCommittees (s₁ + 1) (by omega) h2)).2.1)
    (fun w hw => (hSt w hw).1) (fun w hw => (hSt w hw).2.1) (fun v hv => (hSt v hv).2.2)

/-- **The windows of the lock base, over the naturals.** At a slot `σ` with `S.C.k ≤ σ + 1`: the duty window of slot
`σ + 1` starts at least one delay before the view freeze of slot `σ` less `max (3 * Δ S) Δs`, and at or before that view
freeze less `max (Δ S) Δs`, and at or before the support cutoff of slot `σ + 1` less `max (Δ S) Δs`; each of the two
later times plus `Δs` is at most the support cutoff of slot `σ + 2`.

Why: the schedule is uniform (`times_eq`, `dutyWindowStart_eq`) and `max (Δ S) Δs + 3 Δ < 4 Δ k` (`hΔs`), `k ≥ 2`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `S`: the setup; `σ`: the slot.

Read aloud: Lemma 45b's windows at slot `σ` fit inside the members' windows of slot `σ + 1`. -/
theorem front_lock_windows (U : UniformSchedule M.toSlotLayout) (S : Setup V) {Δs : ℕ} {ΔClockAhead ΔClockBehind : ℝ}
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hA0 : 0 ≤ ΔClockAhead) (hB0 : 0 ≤ ΔClockBehind) {σ : ℕ} (hσk : S.C.k ≤ σ + 1) :
    M.dutyWindowStart S.C (σ + 1) + Δ S ≤ M.viewFreeze S.C σ - max (3 * Δ S) Δs ∧
    M.dutyWindowStart S.C (σ + 1) ≤ M.viewFreeze S.C σ - max (Δ S) Δs ∧
    M.viewFreeze S.C σ - max (Δ S) Δs + Δs ≤ M.supportCutoff S.C (σ + 1 + 1) ∧
    M.dutyWindowStart S.C (σ + 1) ≤ M.supportCutoff S.C (σ + 1) - max (Δ S) Δs ∧
    M.supportCutoff S.C (σ + 1) - max (Δ S) Δs + Δs ≤ M.supportCutoff S.C (σ + 1 + 1) := by
  have hk := S.C.k_ge_two
  obtain ⟨hv0, hc0, hf0, hs0, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
  obtain ⟨hv1, hc1, -, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  obtain ⟨-, hc2, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1 + 1)
  have hdw1 := U.dutyWindowStart_eq S (σ + 1)
  have hssσ := U.slotStart_eq S σ
  have hK : 4 * Δ S * S.C.k ≤ M.slotStart S.C σ + 4 * Δ S := by
    have := Nat.mul_le_mul_left (4 * Δ S) hσk
    rw [hssσ]
    nlinarith
  have hk8 : 8 * Δ S ≤ 4 * Δ S * S.C.k := by
    have := Nat.mul_le_mul_left (4 * Δ S) hk
    omega
  have hm : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have h : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h
  have hmx0 : Δ S ≤ max (Δ S) Δs := le_max_left _ _
  have hmx1 : Δs ≤ max (Δ S) Δs := le_max_right _ _
  have hm3 : max (3 * Δ S) Δs + 3 * Δ S ≤ 4 * Δ S * S.C.k := by
    rcases le_total (3 * Δ S) Δs with h | h
    · rw [max_eq_right h]; omega
    · rw [max_eq_left h]; omega
  have hm13 : max (Δ S) Δs ≤ max (3 * Δ S) Δs := max_le_max (by omega) le_rfl
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- **The votes clause of the lock base (Lemma 45b).** Under the bundle, at a slot `σ` from `s_w + k − 1` with
`σ + 1 ≤ s'`: when a member `u` of `Hon (σ + 1)` ran the update of slot `σ + 1` at its tick to the support cutoff of
slot `σ + 1`, with outcome `(n'', sent'')`, and that update added the lock entry `e₀` of slot `σ`, whose block is an
ancestor of, or equal to, a block `C'` relative to which every member of `Hon (σ + 1)` satisfies `StepFrameAt` at slot
`σ` — then every slot-`(σ + 1)` vote a member of `Hon (σ + 1)` put on the wire is for a block of its tick input that is
`e₀`'s block or a descendant of it.

Why: Lemma 45b (`lem45b_honest_vote_extends_lock_held`) at slot `σ`, its two finality-gadget conditions from
`StepFrameAt` relative to `e₀`'s block (`stepFrameAt_of_ancestorEq`); its windows: `u` is an updater of slot `σ` and
active through the member window of slot `σ + 1`; the voter `w` is an honest active validator of slot `σ`, active from
the duty window's start of slot `σ + 1` up to its tick to the vote time of slot `σ + 1`
(`lockStep_window_of_honestActiveAt`), and through the member window of slot `σ + 1` (`front_lock_windows`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `H`: the bundle; `σ`: the lock's slot; `u`: the updater; `n''`, `sent''`: its update's outcome; `e₀`: the added
  entry; `C'`: the block the frames follow.

Read aloud: the members' votes of the slot after the lock's extend the lock's block. -/
theorem front_lock_votes (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ}
    {GST tGAT tAwakeEnd s_w s' : ℕ} {Hon : ℕ → Finset V}
    (H : FrontHyps M S A x GST tGAT tAwakeEnd s_w s' Hon Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    {σ : ℕ} (hσlo : s_w + S.C.k - 1 ≤ σ) (hσs : σ + 1 ≤ s') {u : V} (hu₁ : u ∈ Hon (σ + 1))
    {n'' : M.N} {sent'' : List (NamedObject V)}
    (hrun'' : .ok (n'', sent'') ∈ M.tick S.C S.P S.X (x.tickInput u (M.supportCutoff S.C (σ + 1)))
      ((M.supportCutoff S.C (σ + 1) : ℕ) : Int))
    (hA'' : GoldilocksCorrectness.Record.Statements.Routines.AwakeFor M S.C
      (x.tickInput u (M.supportCutoff S.C (σ + 1))) (σ + 1))
    {e₀ : M.LE} (he₀ : e₀ ∈ M.lockEntries n'') (hd₀ : e₀.d = S.C.t_ (σ + S.C.k) + 5 * S.C.Δ)
    {C' : Block V} (he₀C' : e₀.B.AncestorEq C')
    (hFr : ∀ w ∈ Hon (σ + 1), StepFrameAt M S A x C' σ w) :
    ∀ w ∈ Hon (σ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (σ + 1)) ∧
        (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_w ∈ (x.tickInput w (M.voteTime S.C (σ + 1))).tree,
        vote = GoldfishVote.mk w (σ + 1) H_w.root ∧ e₀.B.AncestorEq H_w := by
  intro w hw vote hSend
  have hk := S.C.k_ge_two
  have hA0 := H.E.ahead_nonneg
  have hB0 := H.E.behind_nonneg
  have hSk := H.hSkew
  obtain ⟨hW1, hW2, hW3, hW4, hW5⟩ := (front_lock_windows M F U) S H.hΔs hA0 hB0 (σ := σ) (by omega)
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀, σ₀ + 1 = σ := ⟨σ - 1, by omega⟩
  have hF := (stepFrameAt_of_ancestorEq M F) S A x C' e₀.B σ w he₀C' (hFr w hw)
  have hu₀ : u ∈ Hon σ := H.anti M F σ (σ + 1) (by omega) (by omega) hσs hu₁
  -- `GST` is early enough for Lemma 45b at slot `σ`
  have hGST45 : GST + max (Δ S) Δs ≤ M.viewFreeze S.C (σ + 1 - S.C.k) := by
    have h1 := H.hGSTw
    have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (show s_w ≤ σ + 1 - S.C.k by omega)
    have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S (σ + 1 - S.C.k)
    have h4 := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s_w
    omega
  have hcσ1 : M.supportCutoff S.C (σ + 1) ≤ M.supportCutoff S.C s' :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S hσs
  -- `w` is an honest active validator of slot `σ`, active from the duty window's start of slot `σ + 1` up to its
  -- tick to the vote time of slot `σ + 1`
  have hwσ : w ∈ honestActiveAt M S A x (σ₀ + 1) := by
    have := H.honestActive M F U σ R (by omega) (by omega)
      (H.anti M F σ (σ + 1) (by omega) (by omega) hσs hw)
    rwa [← hσ₀] at this
  have hwT : w ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (σ + 1) : ℕ) : ℤ)
      (M.voteTime S.C (σ + 1)) := by
    have := (lockStep_window_of_honestActiveAt M F U) S A R H.E H.hSkew σ₀ hwσ
    rwa [show σ₀ + 2 = σ + 1 by omega] at this
  have hWR : (((M.dutyWindowStart S.C (σ + 1) : ℕ) : ℤ) : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.viewFreeze S.C σ - max (3 * Δ S) Δs : ℕ) : ℝ) := by
    have h1 : ((M.dutyWindowStart S.C (σ + 1) : ℕ) : ℝ) + Δ S ≤
        ((M.viewFreeze S.C σ - max (3 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hW1
    push_cast
    linarith
  have hv₀ : u ∈ A.activeThroughout x ((M.viewFreeze S.C σ - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C σ - max (Δ S) Δs : ℕ) : ℝ) + Δs) :=
    Activity.mem_activeThroughout_of_le (by exact_mod_cast hW2) (by exact_mod_cast hW3)
      (H.window M F R (σ + 1) (by omega) hσs u hu₁)
  have hw₀ : w ∈ A.activeThroughout x ((M.supportCutoff S.C (σ + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (σ + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) :=
    Activity.mem_activeThroughout_of_le (by exact_mod_cast hW4) (by exact_mod_cast hW5)
      (H.window M F R (σ + 1) (by omega) hσs w hw)
  exact (GoldilocksCorrectness.Record.Proofs.Executions.lem45b_honest_vote_extends_lock_held M F U) S A x R GST σ u w e₀
    vote H.E H.hNet H.hSkew H.hRedeliver H.Sy H.hΔs (H.rootsAt M F hcσ1) H.hParent hGST45
    (H.updater M F U σ R (by omega) (by omega) hu₀) _ hWR hwT hv₀ hw₀ n'' sent'' hrun'' hA'' he₀
    hd₀ hF.1 hF.2.1 hSend

/-- **The base, one lock.** Under the bundle, with `b₀ + 2 = s_w + 2k` and `b₀ ≤ s'`: for every
lock entry `e` that a member `u` of `Hon M b₀` holds live before the vote time of slot `b₀ + 1`,
`HonestChainExtends M S Sched x (Hon M b₀) e.B b₀` holds.

Why: `e` was added, as an entry `e₀` on `u`'s saved confirmation `C'` of a slot `σ` or an ancestor
of it, by `u`'s update of slot `σ + 1`, and `e`'s block is an ancestor of `e₀`'s (Lemma 39); `e`
being live at the vote time of slot `b₀ + 1 = s_w + 2k − 1` makes `σ ≥ s_w + k − 1` (Lemma 41),
and the update ran before that vote time, so `σ + 1 ≤ b₀`. At slot `σ + 1`: every member's vote
extends `e₀`'s block (Lemma 45b, its frame conditions from `hFrame` at slot `σ` relative to `C'`,
`GST` before the vote time of slot `σ + 1 − k ≥ s_w`); those votes are a majority of the
committee of slot `σ + 1` for blocks on `e`'s chain, and every member's finalized block before the
support cutoff of slot `σ + 2` is compatible with `e`'s block (`hFrame` at slot `σ` relative to
`C'`, its third conjunct), so every lock entry the revocation of slot `σ + 2` leaves at a member
is compatible with `e`'s block (`locks_clause_of_votes`: Lemma 12, then Lemma 5); no two live
locks are compared, and no lock older than slot `σ` is read. Every member's confirmation of slot
`σ + 1` extends `e`'s block (Lemma 78, `hFrame`'s third conjunct). Then `front_carry_step` at
every slot from `σ + 1` to `b₀ − 1`, `hFrame` relative to `C'`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `H`: the bundle; `b₀`: the base slot; `u`: the holder; `e`: the lock entry.

Read aloud: under the bundle, every live lock a member of slot `b₀` holds is extended by the votes,
locks and confirmations of the members at slot `b₀`. -/
theorem front_lock_base (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {GST tGAT tAwakeEnd s_w s' : ℕ} {Hon : ℕ → Finset V}
    (H : FrontHyps M S A x GST tGAT tAwakeEnd s_w s' Hon Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (b₀ : ℕ)
    (hb₀ : b₀ + 2 = s_w + 2 * S.C.k) (hb : b₀ ≤ s') (u : V) (hu : u ∈ Hon b₀) (e : M.LE)
    (he : e ∈ (x.tickInput u (M.voteTime S.C (b₀ + 1))).lockEntries)
    (hlive : M.is_live (x.tickInput u (M.voteTime S.C (b₀ + 1)))
      ((M.voteTime S.C (b₀ + 1) : ℕ) : Int) e = true) :
    HonestChainExtends M S A x (Hon b₀) e.B b₀ := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  -- where `e` comes from: the update of a slot `σ` that added an entry `e₀` on `u`'s saved confirmation `C'`
  obtain ⟨σ, hd, hcut, n'', sent'', hrun'', hA'', e₀, he₀, hd₀, heB₀, C', hsv, he₀C'⟩ :=
    (lock_entry_update M F U) S A x R _ u e H.E he
  have hlive' := hlive
  simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)] at hlive'
  -- the slot of the lock is from `s_w + k − 1` to `b₀ − 1`
  have hσlo : s_w + S.C.k - 1 ≤ σ :=
    (GoldilocksCorrectness.Record.Statements.Executions.lem41_slot_of_live_entry M F U) S (s_w + S.C.k - 1) σ
      (M.voteTime S.C (b₀ + 1)) e hd hlive'.1
      ((GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono M.toSlotLayout F.sched) S (by omega))
  have hσhi : σ + 1 ≤ b₀ := by
    by_contra h
    have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show b₀ + 1 ≤ σ + 1 by omega)
    have h1' := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (b₀ + 1)
    have h2' := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (σ + 1)
    have h3' := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (σ + 1)
    omega
  have hu₁ : u ∈ Hon (σ + 1) := H.anti M F (σ + 1) b₀ (by omega) hσhi hb hu
  -- the frames relative to `C'`
  have hFr : ∀ s₁, σ ≤ s₁ → s₁ < s' → ∀ w ∈ Hon (s₁ + 1), StepFrameAt M S A x C' s₁ w :=
    fun s₁ h1 h2 => H.hFrame s₁ (by omega) h2 σ hσlo h1 u hu₁ C' hsv
  have heC' : e.B.AncestorEq C' := ancestorEq_trans heB₀ he₀C'
  have hcσ1 : M.supportCutoff S.C (σ + 1) ≤ M.supportCutoff S.C s' :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  have hHA1 := H.honestActive M F U (σ + 1) R (by omega) (by omega)
  -- clause 1 at slot `σ + 1`: Lemma 45b at the entry `e₀` `u`'s update of slot `σ + 1` added
  have hc1' : ∀ w ∈ Hon (σ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (σ + 1)) ∧
        (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_w ∈ (x.tickInput w (M.voteTime S.C (σ + 1))).tree,
        vote = GoldfishVote.mk w (σ + 1) H_w.root ∧ e.B.AncestorEq H_w := by
    intro w hw vote hSend
    obtain ⟨H_w, hHT, hvt, hBH⟩ := (front_lock_votes M F U) R H hσlo (by omega) hu₁ hrun'' hA'' he₀
      (hd₀.trans hd) he₀C' (fun w hw => hFr σ le_rfl (by omega) w hw) w hw vote hSend
    exact ⟨H_w, hHT, hvt, ancestorEq_trans heB₀ hBH⟩
  have hbase : HonestChainExtends M S A x (Hon (σ + 1)) e.B (σ + 1) := by
    refine ⟨hc1', fun w hw n₂ sent₂ hrun₂ hA₂ e₂ he₂ _ => ?_, fun v hv C'' hC'' => ?_⟩
    · -- clause 2: `locks_clause_of_votes` against the members' votes of slot `σ + 1`
      obtain ⟨Hv, hHv⟩ := (voters_of_votes_clause M F U) S A x R (σ + 1)
        (S.P.committee (σ + 1) ∩ Hon (σ + 1)) e.B H.E H.hSkew
        (fun u' hu' => ⟨hHA1 (Finset.mem_inter.1 hu').2, (Finset.mem_inter.1 hu').1⟩)
        (fun u' hu' => hc1' u' (Finset.mem_inter.1 hu').2)
      exact (locks_clause_of_votes M F U) S A x R GST (σ + 1) (Hon (σ + 1)) e.B Hv H.E H.hNet H.hSkew
        H.hRedeliver H.Sy H.hΔs (H.rootsTickAt M F hcσ1) H.hParent H.hOwner
        (H.gstSync M F U (σ + 1) (by omega) (by omega)) (H.updater M F U (σ + 1) R (by omega) (by omega))
        (H.hCommittees (σ + 1) (by omega) (by omega)) hHv
        (fun v hv => ((stepFrameAt_of_ancestorEq M F) S A x C' e.B σ v heC'
          (hFr σ le_rfl (by omega) v hv)).2.2)
        w hw n₂ ((locksRevoked_of_voteTime_outcome M F U) S A x R H.E (σ + 1 + 1) w n₂ sent₂ hrun₂ hA₂)
        e₂ he₂
    · -- clause 3: Lemma 78
      have hF := ((stepFrameAt_of_ancestorEq M F) S A x C' e.B σ v heC'
        (hFr σ le_rfl (by omega) v hv)).2.2
      exact (confirmations_of_votes_clause M F U) S A x R GST (σ + 1) (Hon (σ + 1)) e.B v H.E H.hNet H.hSkew
        H.hRedeliver H.Sy H.hΔs (H.rootsTickAt M F hcσ1) H.hParent H.hOwner
        (H.gstSync M F U (σ + 1) (by omega) (by omega)) hHA1
        (H.hCommittees (σ + 1) (by omega) (by omega)) hc1'
        (H.updater M F U (σ + 1) R (by omega) (by omega) hv) hF C'' hC''
  -- the carry to slot `b₀`
  have key : ∀ d, σ + 1 + d ≤ b₀ →
      HonestChainExtends M S A x (Hon (σ + 1 + d)) e.B (σ + 1 + d) := by
    intro d
    induction d with
    | zero => intro _; exact hbase
    | succ d ih =>
        intro hd'
        rw [show σ + 1 + (d + 1) = σ + 1 + d + 1 by omega]
        exact (front_carry_step M F U R E hNet hSkew hRedeliver Sy hΔs) H (σ + 1 + d) (by omega) (by omega) e.B
          (fun w hw => (stepFrameAt_of_ancestorEq M F) S A x C' e.B _ w heC'
            (hFr (σ + 1 + d) (by omega) (by omega) w hw))
          (ih (by omega))
  have := key (b₀ - (σ + 1)) (by omega)
  rwa [show σ + 1 + (b₀ - (σ + 1)) = b₀ by omega] at this

/-! ## The induction over the live lock blocks -/

/-- `liveLockAncestors M S Sched x Hon s₁ C`: `C` is the block of a lock entry some member of `Hon`
holds live in the state its own tick to the vote time of slot `s₁ + 1` starts from, or an ancestor of
that block. The lock part of
`FrontFamily M S Sched x Hon s₁`, closed under ancestors.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Hon`: the members; `s₁`: the slot;
  `C`: the block.

Read aloud: `C` is a live lock block of a member, or an ancestor of one. -/
def liveLockAncestors (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (Hon : Finset V) (s₁ : ℕ) (C : Block V) : Prop :=
  ∃ u ∈ Hon, ∃ e ∈ (x.tickInput u (M.voteTime S.C (s₁ + 1))).lockEntries,
    M.is_live (x.tickInput u (M.voteTime S.C (s₁ + 1)))
      ((M.voteTime S.C (s₁ + 1) : ℕ) : Int) e = true ∧ C.AncestorEq e.B

/-- **The live lock blocks of the next slot.** Under the bundle, at a slot `s₁` from `s_w` with
`s₁ + 1 ≤ s'`: a block on the chain of a live lock a member of `Hon M (s₁ + 1)` holds before the
vote time of slot `s₁ + 2` is on the chain of a live lock a member of `Hon M s₁` holds before the
vote time of slot `s₁ + 1`, or is an ancestor of, or equal to, a member's confirmation of slot `s₁`.

Why: `live_lock_entry_source` at the vote time of slot `s₁ + 2`: the entry is on the holder's own
confirmation of slot `s₁`, or on an ancestor of an entry the revocation of slot `s₁ + 1` left live,
itself on an ancestor of a live entry of its input (Lemma 38); the holder is a member of `Hon M s₁`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `H`: the bundle; `s₁`: the slot.

Read aloud: a live lock block of the next slot's members is one of this slot's, or on a member's
confirmation of this slot. -/
theorem liveLockAncestors_succ (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {GST tGAT tAwakeEnd s_w s' : ℕ} {Hon : ℕ → Finset V}
    {Δs : ℕ} {ΔNet : ℕ} (H : FrontHyps M S A x GST tGAT tAwakeEnd s_w s' Hon Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (s₁ : ℕ) (h1 : s_w ≤ s₁)
    (h2 : s₁ + 1 ≤ s') (C : Block V)
    (hC : liveLockAncestors M S A x (Hon (s₁ + 1)) (s₁ + 1) C) :
    liveLockAncestors M S A x (Hon s₁) s₁ C ∨ ∃ v ∈ Hon (s₁ + 1), ∃ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s₁ + 1))).savedConfirmation s₁ = some C' ∧
      C.AncestorEq C' := by
  obtain ⟨u, hu, e, he, hl, hCe⟩ := hC
  have hl' := hl
  simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)] at hl'
  have hΔ := one_le_Δ S
  have hc1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s₁ + 1)
  have hc2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s₁ + 1 + 1)
  have hv2 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ M.toSlotLayout F.sched U) S (s₁ + 1)
  -- `u` is active from its tick to a value at most the duty window's start of slot `s₁ + 2` up to its
  -- tick to the vote time of slot `s₁ + 2`: the member window of slot `s₁ + 1` holds every step from one
  -- clock bound before that start to one clock bound after that vote time
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hSk := H.hSkew
  have hwin := H.window M F R (s₁ + 1) (by omega) h2 u hu
  have hdw1 := U.dutyWindowStart_eq S (s₁ + 1)
  have hdw2 := U.dutyWindowStart_eq S (s₁ + 1 + 1)
  have hss1 := U.slotStart_eq S (s₁ + 1)
  have hss2 := U.slotStart_eq S (s₁ + 1 + 1)
  have hΔR : (0 : ℝ) ≤ (Δ S : ℝ) := Nat.cast_nonneg _
  have hwin' : u ∈ A.activeThroughout x
      ((((M.dutyWindowStart S.C (s₁ + 1 + 1) : ℕ) : ℤ) : ℝ) - ΔClockAhead)
      (((M.voteTime S.C (s₁ + 1 + 1) : ℕ) : ℝ) + ΔClockBehind) := by
    refine Activity.mem_activeThroughout_of_forall fun i h1 h2 => ?_
    refine Activity.mem_activeThroughout.1 hwin i ?_ ?_
    · have : ((M.supportCutoff S.C (s₁ + 1 + 1) : ℕ) : ℝ) = ((M.voteTime S.C (s₁ + 1 + 1) : ℕ) : ℝ) + (Δ S : ℝ) := by
        exact_mod_cast hc2
      linarith
    · have ht0 := (time_nonneg M) x R (i + 1)
      have hcast : ((((M.dutyWindowStart S.C (s₁ + 1 + 1) : ℕ) : ℤ) : ℝ)) =
          ((M.dutyWindowStart S.C (s₁ + 1 + 1) : ℕ) : ℝ) := Int.cast_natCast _
      rw [hcast] at h2
      rcases Nat.eq_zero_or_pos (M.dutyWindowStart S.C (s₁ + 1)) with h0 | hpos
      · rw [h0]
        exact_mod_cast ht0
      · have hss' : M.slotStart S.C (s₁ + 1 + 1) = M.slotStart S.C (s₁ + 1) + 4 * Δ S := by
          rw [hss1, hss2]
          ring
        have hle : M.dutyWindowStart S.C (s₁ + 1) + 4 * Δ S ≤ M.dutyWindowStart S.C (s₁ + 1 + 1) := by
          omega
        have hleR : ((M.dutyWindowStart S.C (s₁ + 1) : ℕ) : ℝ) + 4 * (Δ S : ℝ) ≤
            ((M.dutyWindowStart S.C (s₁ + 1 + 1) : ℕ) : ℝ) := by exact_mod_cast hle
        linarith
  have hab : ((M.dutyWindowStart S.C (s₁ + 1 + 1) : ℕ) : ℤ) ≤ ((M.voteTime S.C (s₁ + 1 + 1) : ℕ) : ℤ) := by
    have := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_le_supportCutoff M.toSlotLayout F.sched U)
      S (show s₁ + 1 + 1 ≤ s₁ + 1 + S.C.k by have := S.C.k_ge_two; omega)
    have hc1' := hc1
    have hv1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₁ + 1)
    have hv2' := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₁ + 1 + 1)
    have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (show s₁ + 1 ≤ s₁ + 1 + 1 by omega)
    exact_mod_cast (show M.dutyWindowStart S.C (s₁ + 1 + 1) ≤ M.voteTime S.C (s₁ + 1 + 1) by omega)
  have hTick := (mem_activeThroughoutToTick_of_mem_activeThroughout M F) x R E
    (by have := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₁ + 1 + 1); omega) hab hwin'
  rcases (live_lock_entry_source M F U) S A x R s₁ (M.voteTime S.C (s₁ + 1 + 1)) u E H.hSkew hTick (by omega)
      le_rfl e he hl'.1 with ⟨C', hC', heC'⟩ | ⟨n₃, sent₃, hrun₃, hA₃, e', he', hl₃, hee'⟩
  · exact Or.inr ⟨u, hu, C', hC', ancestorEq_trans hCe heC'⟩
  · -- the outcome `n₃` of `u`'s tick at the vote time of slot `s₁ + 1` revoked the locks there
    obtain ⟨e₁, he₁, hl₁, -, he'₁, -⟩ :=
      GoldilocksCorrectness.Record.Statements.Routines.lem38_revoke_locks_entries_moved
        (Nat.le_add_left 1 s₁)
        ((locksRevoked_of_voteTime_outcome M F U) S A x R E (s₁ + 1) u n₃ sent₃ hrun₃ hA₃) e' he'
    exact Or.inl ⟨u, H.hHonMono s₁ h1 (by omega) hu, e₁, he₁, hl₁,
      ancestorEq_trans hCe (ancestorEq_trans hee' he'₁)⟩

/-- **The frames of the step.** Under the bundle, with `b₀ + 2 = s_w + 2k`, at a slot `s₁` with
`b₀ ≤ s₁ < s'`: for every block on the chain of a live lock a member of `Hon s₁` holds before the
vote time of slot `s₁ + 1`, and every confirmation of slot `s₁` a member of `Hon (s₁ + 1)` holds,
`StepFrameAt M S Sched x C s₁ w` holds at every member `w` of `Hon (s₁ + 1)`.

Why: a live lock at the vote time of slot `s₁ + 1 ≥ s_w + 2k − 1` is of a slot `σ ≥ s_w + k − 1`
(Lemma 41) on its holder's confirmation of slot `σ`, or an ancestor of it
(`lock_entry_confirmation`), with `σ + 1 ≤ s₁`; `hFrame` at slot `s₁` relative to that
confirmation, or to the member's confirmation of slot `s₁`, and `stepFrameAt_of_ancestorEq`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `H`: the bundle; `b₀`: the base slot; `s₁`: the slot.

Read aloud: under the bundle, from slot `b₀` on, the next slot's members satisfy `StepFrameAt`
relative to every live lock block and every member's confirmation of the slot. -/
theorem front_step_frames (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GST tGAT tAwakeEnd s_w s' : ℕ} {Hon : ℕ → Finset V}
    {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (H : FrontHyps M S A x GST tGAT tAwakeEnd s_w s' Hon Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (b₀ : ℕ)
    (hb₀ : b₀ + 2 = s_w + 2 * S.C.k) (s₁ : ℕ) (h1 : b₀ ≤ s₁) (h2 : s₁ < s') :
    ∀ C : Block V, (liveLockAncestors M S A x (Hon s₁) s₁ C ∨ ∃ v ∈ Hon (s₁ + 1),
        (x.tickOutput v (M.supportCutoff S.C (s₁ + 1))).savedConfirmation s₁ = some C) →
      ∀ w ∈ Hon (s₁ + 1), StepFrameAt M S A x C s₁ w := by
  have hk := S.C.k_ge_two
  intro C hC w hw
  rcases hC with ⟨u, hu, e, he, hl, hCe⟩ | ⟨v, hv, hC⟩
  · have hl' := hl
    simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)] at hl'
    obtain ⟨σ, hd, hcut, C', hsv, heC'⟩ := (lock_entry_confirmation M F U) S A x R _ u e H.E he
    have hσlo : s_w + S.C.k - 1 ≤ σ :=
      (GoldilocksCorrectness.Record.Statements.Executions.lem41_slot_of_live_entry M F U) S (s_w + S.C.k - 1) σ
        (M.voteTime S.C (s₁ + 1)) e hd hl'.1 ((GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono M.toSlotLayout F.sched) S (by omega))
    have hσhi : σ + 1 ≤ s₁ := by
      by_contra h
      have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show s₁ + 1 ≤ σ + 1 by omega)
      have h1' := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₁ + 1)
      have h2' := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (σ + 1)
      have h3' := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (σ + 1)
      omega
    have hu' : u ∈ Hon (σ + 1) := H.anti M F (σ + 1) s₁ (by omega) hσhi (by omega) hu
    exact (stepFrameAt_of_ancestorEq M F) S A x C' C s₁ w (ancestorEq_trans hCe heC')
      (H.hFrame s₁ (by omega) h2 σ hσlo (by omega) u hu' C' hsv w hw)
  · exact H.hFrame s₁ (by omega) h2 s₁ (by omega) le_rfl v hv C hC w hw

/-- **The chain relative to the live lock blocks, from slot `b₀`.** Under the bundle, with
`b₀ + 2 = s_w + 2k`: at every slot `b₀ + d < s'`, `ChainInvFor` holds at `Hon (b₀ + d)` for the
blocks on the chain of a live lock a member of that set holds before the vote time of the next
slot.

Why: at `b₀`, `front_lock_base` for each lock and `honestChainExtends_of_ancestorEq`; from `b₀ + d`
to `b₀ + d + 1`, the phase step `lem89s_phase_step` with the family of slot `b₀ + d`, its lock
invariant from Lemma 38 (`liveLocksOnFamilyAt_of_live`), its frames from `front_step_frames`, and
the family of the next slot inside the step's (`liveLockAncestors_succ`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `H`: the bundle; `b₀`: the base slot.

Read aloud: under the bundle, from slot `b₀` on, `ChainInvFor` holds at the members for their live
lock blocks. -/
theorem front_locks_chain (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {GST tGAT tAwakeEnd s_w s' : ℕ} {Hon : ℕ → Finset V}
    (H : FrontHyps M S A x GST tGAT tAwakeEnd s_w s' Hon Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (b₀ : ℕ)
    (hb₀ : b₀ + 2 = s_w + 2 * S.C.k) :
    ∀ d, b₀ + d < s' → ChainInvFor M S A x (Hon (b₀ + d))
      (liveLockAncestors M S A x (Hon (b₀ + d)) (b₀ + d)) (b₀ + d) := by
  have hk := S.C.k_ge_two
  intro d
  induction d with
  | zero =>
      intro hd C hC
      obtain ⟨u, hu, e, he, hl, hCe⟩ := hC
      exact (honestChainExtends_of_ancestorEq M F) S A x _ e.B C _ hCe
        ((front_lock_base M F U) R E hNet hSkew hRedeliver Sy hΔs H b₀ hb₀ (by omega) u hu e he hl)
  | succ d ih =>
      intro hd
      have ih' := ih (by omega)
      rw [show b₀ + (d + 1) = b₀ + d + 1 by omega]
      have hc : M.supportCutoff S.C (b₀ + d + 1) ≤ M.supportCutoff S.C s' :=
        (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
      have hstep := ((lem89s_phase_step M F U) S A x R GST (b₀ + d) (Hon (b₀ + d)) (Hon (b₀ + d + 1))
        (liveLockAncestors M S A x (Hon (b₀ + d)) (b₀ + d)) H.E H.hNet H.hSkew H.hRedeliver H.Sy H.hΔs
        (H.rootsAt M F hc) (H.rootsTickAt M F hc) H.hParent H.hOwner
        (H.gstSync M F U _ (by omega) (by omega))
        (H.honestActive M F U (b₀ + d) R (by omega) (by omega))
        (H.honestActive M F U (b₀ + d + 1) R (by omega) (by omega))
        (H.hHonMono (b₀ + d) (by omega) (by omega))
        (H.hCommittees (b₀ + d) (by omega) (by omega))
        (H.hCommittees (b₀ + d + 1) (by omega) (by omega)) ih'
        (fun u hu => (liveLocksOnFamilyAt_of_live M F U) S A x R H.E _ (b₀ + d) u
          (fun e he hl => ⟨u, hu, e, he, hl, ancestorEq_refl e.B⟩))
        ((front_step_frames M F U R) H b₀ hb₀ (b₀ + d) (by omega) (by omega))).1
      intro C hC
      exact hstep C ((liveLockAncestors_succ M F U R H.E) H (b₀ + d) (by omega) (by omega) C hC)

/-! ## Lemma 89f -/

/-- **Lemma 89f with the frame hypotheses its proof reads.** The proof; the audited statement is
in `Statements/Executions/Lemma89fStatements.lean`.

Why: with `b₀ := s_w + 2k − 2` and `s' = m + 1`: `front_locks_chain` at slot `m`, the phase step
`lem89s_phase_step` from `m` to `m + 1`, whose family holds every block of
`FrontFamily M S Sched x (Hon s') s'`: a live lock block by `liveLockAncestors_succ`, a root by
`hRootsOn` and the same. The lock invariant relative to `FrontFamily` is Lemma 38
(`liveLocksOnFamilyAt_of_live`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the phase; `s_w`: a slot whose duty window starts
  at or after `tGAT`; `s'`: the slot; `Hon`: the member sets.

Roots name blocks until `M.supportCutoff S.C s'`: the base reads Lemmas 45b, 12 and 78 at the slot
`σ + 1 ≤ s'` after a lock's slot (`front_lock_base`), the carry and the phase step at slots before
`s'`, up to the support cutoff of slot `s'`.

Read aloud: when, from slot `s_w + k − 1` on, the members' frames follow every member's
confirmation, and at slot `s'` every member's root is behind a member's live lock or confirmation,
then at slot `s'` the votes, live locks and confirmations of the members extend every live lock
block and every root of a member, and the live locks their revocations of slot `s' + 1` leave are on
the chain of one of those blocks. -/
theorem lem89fq_front (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd s_w s' : ℕ) (Hon : ℕ → Finset V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C s'))
    -- roots name blocks also up to the real time of every validator's tick to a clock value at most the
    -- support cutoff of slot `s'`
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s' →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x) (hOwner : VotesCastByOwner M A x)
    (hGST : GST ≤ tGAT)
    (hGSTw : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s_w)
    (hHonMono : ∀ s₁, s_w ≤ s₁ → s₁ < s' → Hon (s₁ + 1) ⊆ Hon s₁)
    (hHon : ∀ s₁, s_w ≤ s₁ → s₁ ≤ s' → ∀ v ∈ Hon s₁,
      v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₁ + 1)))
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : ∀ s₁, s_w + S.C.k ≤ s₁ → s₁ ≤ s' →
      (S.P.committee s₁).card < 2 * (S.P.committee s₁ ∩ Hon s₁).card)
    (hsw : tGAT ≤ M.dutyWindowStart S.C s_w)
    (hs' : s_w + 2 * S.C.k - 1 ≤ s') (hEnd : M.supportCutoff S.C (s' + 1) ≤ tAwakeEnd)
    (hFrame : ∀ s₁, s_w + S.C.k - 1 ≤ s₁ → s₁ < s' →
      ∀ σ, s_w + S.C.k - 1 ≤ σ → σ ≤ s₁ → ∀ v ∈ Hon (σ + 1), ∀ C : Block V,
        (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C →
        ∀ w ∈ Hon (s₁ + 1), StepFrameAt M S A x C s₁ w)
    (hRootsOn : ∀ w ∈ Hon s', ∃ D : Block V,
      ((∃ u ∈ Hon s', ∃ e ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).lockEntries,
          M.is_live (x.tickInput u (M.voteTime S.C (s' + 1)))
            ((M.voteTime S.C (s' + 1) : ℕ) : Int) e = true ∧ e.B = D) ∨
        ∃ v ∈ Hon s',
          (x.tickOutput v (M.supportCutoff S.C s')).savedConfirmation (s' - 1) = some D) ∧
      (M.get_fc_root (x.tickInput w (M.voteTime S.C (s' + 1)))).AncestorEq D) :
    ChainInvFor M S A x (Hon s') (FrontFamily M S A x (Hon s') s') s' ∧
    ∀ u ∈ Hon s', LiveLocksOnFamilyAt M S A x (FrontFamily M S A x (Hon s') s') s' u := by
  have hk := S.C.k_ge_two
  have H : FrontHyps M S A x GST tGAT tAwakeEnd s_w s' Hon Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind
      ΔNet :=
    { E := E, hNet := hNet, hSkew := hSkew, hRedeliver := hRedeliver, Sy := Sy, hΔs := hΔs, hRoots := hRoots,
      hRootsTick := hRootsTick, hParent := hParent, hOwner := hOwner, hGST := hGST, hGSTw := hGSTw,
      hHonMono := hHonMono, hHon := hHon, hAwake := hAwake, hActive := hActive, hCommittees := hCommittees,
      hsw := hsw, hEnd := hEnd, hFrame := hFrame }
  refine ⟨?_, fun u hu => (liveLocksOnFamilyAt_of_live M F U) S A x R E _ s' u
    (fun e he hl => Or.inl ⟨u, hu, e, he, hl, rfl⟩)⟩
  obtain ⟨m, rfl⟩ : ∃ m, s' = m + 1 := ⟨s' - 1, by omega⟩
  have hb₀ : (s_w + 2 * S.C.k - 2) + 2 = s_w + 2 * S.C.k := by omega
  have hm := (front_locks_chain M F U R E hNet hSkew hRedeliver Sy hΔs) H (s_w + 2 * S.C.k - 2) hb₀
    (m - (s_w + 2 * S.C.k - 2)) (by omega)
  rw [show s_w + 2 * S.C.k - 2 + (m - (s_w + 2 * S.C.k - 2)) = m by omega] at hm
  have hstep := ((lem89s_phase_step M F U) S A x R GST m (Hon m) (Hon (m + 1))
    (liveLockAncestors M S A x (Hon m) m) E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent hOwner
    (H.gstSync M F U _ (by omega) (by omega))
    (H.honestActive M F U m R (by omega) (by omega)) (H.honestActive M F U (m + 1) R (by omega) le_rfl)
    (hHonMono m (by omega) (by omega)) (hCommittees m (by omega) (by omega))
    (hCommittees (m + 1) (by omega) le_rfl) hm
    (fun u hu => (liveLocksOnFamilyAt_of_live M F U) S A x R E _ m u
      (fun e he hl => ⟨u, hu, e, he, hl, ancestorEq_refl e.B⟩))
    ((front_step_frames M F U R) H (s_w + 2 * S.C.k - 2) hb₀ m (by omega) (by omega))).1
  intro C hC
  apply hstep C
  rcases hC with ⟨w, hw, e, he, hl, rfl⟩ | ⟨w, hw, rfl⟩
  · exact (liveLockAncestors_succ M F U R E) H m (by omega) le_rfl e.B ⟨w, hw, e, he, hl, ancestorEq_refl e.B⟩
  · obtain ⟨D, hD, hRD⟩ := hRootsOn w hw
    rcases hD with ⟨u, hu, e, he, hl, rfl⟩ | ⟨v, hv, hconf⟩
    · exact (liveLockAncestors_succ M F U R E) H m (by omega) le_rfl _ ⟨u, hu, e, he, hl, hRD⟩
    · rw [Nat.add_sub_cancel] at hconf
      exact Or.inr ⟨v, hv, D, hconf, hRD⟩

end GoldilocksCorrectness.Record.Proofs.Executions

