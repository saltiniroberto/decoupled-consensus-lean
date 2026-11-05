module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Wake
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickWindowKit

@[expose] public section

/-!
# WakeStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/WakeStatements.lean`, over a model
`M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 16b, the wake rule from
awakeness, and its corollary, the duty test of a slot passes. That `awakeSince` is kept while the
validator stays awake is `awakeSince_kept_of_awake_steps`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (dutyWindowStart)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Lemma 16b, the wake rule from awakeness.** In an execution where every time is reached, a
validator `v` counted active from `a` up to its own tick to `b` (`A.activeThroughoutToTick`), `a < b`,
ticks to `b` from a state whose `awakeSince` is some time `τ` that is the initial value
`proposal_window_start S.C 0` or at most `a`; and `τ` is the initial value when `v` is active at every
step up to that tick.

Why: `awakeSince_le_of_mem_activeThroughoutToTick` for the first part: in the reader's first case `v`
was never restarted up to its tick and keeps the initial value; in its second case it ticked after its
last restart to a clock value at most `a`, which stored a value at most that one. The second part is
`tickInput_awakeSince_of_awake_up_to_tick`: awake at every step up to the tick, `v` was never woken, so
the initial value is kept.

 under the clock-behind bound a restart to `t` after the real
time `t` precedes the tick, and the conjunct fails after a restart followed by a tick to the value `0`
. At both clock bounds `0` the new text gives
the earlier one.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `A`: the activity; `x`: the execution;
- `a`: the opening value of the reader's window; `b`: the clock value of the tick; `v`: the validator.

Read aloud: a validator active up to its tick to `b` from a window opening at `a` has, at that tick, been
awake since the start or since a time at most `a`, and since the start when it was active at every
step up to the tick. -/
theorem lem16b_awakeSince_of_awake_throughout (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (a : ℤ) (b : ℕ) (v : V)
    -- every time is reached
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- `a` is before `b`
    (hab : a < b)
    -- `v` is active from `a` up to its own tick to `b`
    (hv : v ∈ A.activeThroughoutToTick x a b) :
    -- then `v`'s tick to `b` starts from a record of awakeness since the start or since `τ ≤ a`
    ∃ τ : Time, (x.tickInput v b).awakeSince = some τ ∧
      (τ = proposal_window_start S.C 0 ∨ τ ≤ a) ∧
      ((∀ i : ℕ, i ≤ x.tickStep v b → v ∈ A.active i) → τ = proposal_window_start S.C 0) := by
  obtain ⟨τ, hτ, hor⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.awakeSince_le_of_mem_activeThroughoutToTick
    M F) x R E hab hv
  refine ⟨τ, hτ, hor, fun hall => ?_⟩
  obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  have h0 := (GoldilocksCorrectness.Record.Proofs.Executions.tickInput_awakeSince_of_awake_up_to_tick M F) x R E
    (x.lbl_tickStep ⟨k', hk'⟩) (fun i hi => Activity.mem_awake_of_mem_active (hall i hi))
  rw [hτ] at h0
  exact Option.some.inj h0

/-- **The wake rule passes the duty test.** In an execution where every time is reached, a
validator `v` counted active from the duty window's start of slot `s'` up to its own tick to `t`
(`A.activeThroughoutToTick`), with `M.dutyWindowStart S.C s' < t`, ticks to `t` from a state whose
`awakeSince` is some time at most `duty_window_start S.C s'`: the duty test of slot `s'` passes (the
hypothesis `hAwake` of Lemmas 13 and 15).

Why: `awakeSince_le_of_mem_activeThroughoutToTick`: the stored wake time is the initial one, at most
every duty window's start, or a time at most the window's start (the reader's second case: a tick
after the last restart to a clock value at most the window's start, active from that tick on).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `s'`: the slot of the duty; `t`: the time of the tick; `v`: the validator.

Read aloud: a validator that ticks to `t` and either was never restarted up to that tick, or ticked
after its last restart to a clock value at most the duty window's start of slot `s'` and stayed active
up to its tick to `t`, reads at that tick a stored wake time at most that start: slot `s'`'s duty test
passes. -/
theorem awakeSince_le_dutyWindowStart_b (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s' t : ℕ) (v : V)
    -- every time is reached
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- corruption is permanent
    -- the duty window's start of slot `s'` is before `t`
    (ht : M.dutyWindowStart S.C s' < t)
    -- `v` is awake and honest from the duty window's start of slot `s'` up to its own tick to `t`
    (hAwake : v ∈ A.activeThroughoutToTick x (duty_window_start S.C s') t) :
    -- then `v`'s tick at `t` starts from a record that passes slot `s'`'s duty test
    ∃ τ : Time, (x.tickInput v t).awakeSince = some τ ∧
      τ ≤ duty_window_start S.C s' := by
  have hb : duty_window_start S.C s' < t := by
    have he := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_eq_toNat
      M.toSlotLayout F.sched U) S s'
    rw [he] at ht
    have h1 : duty_window_start S.C s' ≤ ((duty_window_start S.C s').toNat : Int) := Int.self_le_toNat _
    have h2 : (((duty_window_start S.C s').toNat : ℕ) : Int) < (t : Int) := by exact_mod_cast ht
    exact lt_of_le_of_lt h1 h2
  exact (GoldilocksCorrectness.Record.Proofs.Executions.tickInput_awakeSince_of_mem_activeThroughoutToTick
    M F U) x R E hAwake hb

end GoldilocksCorrectness.Record.Statements.Executions

