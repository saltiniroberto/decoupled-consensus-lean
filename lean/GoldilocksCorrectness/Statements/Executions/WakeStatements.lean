module
public import GoldilocksCorrectness.Proofs.Executions.Wake

@[expose] public section

/-!
# The wake rule over executions

The audited statements about the time since which a node has been awake (`awakeSince`), proved in
`GoldilocksCorrectness/Proofs/Executions/Wake.lean`.

Lemma 16 and its corollary `awakeSince_le_dutyWindowStart`, the plan's statements, were stated
without `hTicks` and could not be proved from their hypotheses: the validator's tick at the start of
the window must answer, and nothing in them says it does. The forms with `hTicks`, Lemma 16b and `awakeSince_le_dutyWindowStart_b`, are proved
and kept under their names (lemma numbers are append-only).



## Rendering note for the copies

What was tried. Lemma 16's route, without `hTicks` (the plan's section 5, steps 1 to 5), went
through for `t₀ = 0`: every step keeps the initial `awakeSince`. For `t₀ ≥ 1` it reads the tick of
`v` at `t₀`. When `v` enters the awake set at `t₀` (asleep at `t₀ − 1`), the tick starts from the
woken state, whose `awakeSince` is `none`; if the tick answers, `record_awake` writes `t₀`; if it
fails, the wiring's reaction keeps the woken state
(`GoldilocksCorrectness/Statements/Executions/WiringDefs.lean`, `reaction`, the error branch), so
`awakeSince` stays `none`, and the next tick that answers records a time later than `t₀`. Nothing
in Lemma 16's hypotheses said the tick at `t₀` answers; that is the library's assumption
`TicksSucceed` (`ExecutionDefs.lean`), whose derivation from the routines (no routine of a
reachable honest tick raises) is not in the library and not in the plan. The statement was
therefore not provable as written, and false in an execution in which `v`'s ticks fail from `t₀`
on.

The change. Lemma 16b and `awakeSince_le_dutyWindowStart_b` take the hypothesis
`hTicks : TicksSucceed S Sched x`. Read aloud: every honest awake validator's tick answers.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (dutyWindowStart)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 16b, the wake rule from awakeness.** In an execution where every time is reached
and corruption is permanent, a validator `v` awake at every time from `t₀` to `t`, `t₀ < t`, and
honest at `t`, starts its tick at `t` with `awakeSince` some time `τ ≤ t₀`; when `t₀ = 0`, `τ` is
the initial value `proposal_window_start S.C 0`.

The conclusion rests on the tick at `t₀` answering (`ticksSucceed_of_exec`): a validator that
entered the awake set at `t₀` and whose tick at `t₀` failed would keep `awakeSince` absent, and its
next tick that answers would record a time later than `t₀`.

Why: a stored `awakeSince` is at most the node's clock (`awakeSince_le_clock`); the tick at `t₀`
answers (`tick_step_outcome`), so it writes `t₀` over an absent value or leaves a value at most the
clock, which is before `t₀`; every later step before `t` keeps it, since `v` is awake at every tick
in between and at the time before it, so it does not enter the awake set and is not woken; and `v`
does not enter the awake set at `t` either.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `t₀`: the time from which `v` is awake; `t`: the time of the tick; `v`: the validator.

Read aloud: the node state `v`'s tick at `t` starts from records
that `v` has been awake since a time `τ` at most `t₀`; a validator awake since time `0` still
carries the initial value. -/
theorem lem16b_awakeSince_of_awake_throughout (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t₀ t : ℕ) (v : V)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- `t₀` is before `t`
    (ht₀ : t₀ < t)
    -- `v` is awake at every time from `t₀` to `t`
    (hAwake : ∀ t' : ℕ, t₀ ≤ t' → t' ≤ t → v ∈ Sched.awake (t' : Int))
    -- `v` is honest at `t`
    (hHonest : v ∉ Sched.adv (t : Int)) :
    -- then `v`'s tick at `t` starts from a record of awakeness since `τ ≤ t₀`
    ∃ τ : Time, (tickInputState x (stepBefore x t) t v).awakeSince = some τ ∧
      τ ≤ (t₀ : Int) ∧ (t₀ = 0 → τ = proposal_window_start S.C 0) :=
  GoldilocksCorrectness.Proofs.Executions.lem16b_awakeSince_of_awake_throughout S Sched x t₀ t v
    hDiv hMono ht₀ hAwake hHonest

/-- **The wake rule passes the duty test.** In an execution where every time is reached and
corruption is permanent, a validator `v` awake at every time from `dutyWindowStart S s'` to `t`,
`dutyWindowStart S s' < t`, and honest at `t`, starts its tick at `t` with `awakeSince` some time at
most `duty_window_start S.C s'`: the duty test of slot `s'` passes (the hypothesis `hAwake` of
Lemmas 13 and 15).

The conclusion rests on the tick at `dutyWindowStart S s'` answering (`ticksSucceed_of_exec`): a
validator that entered the awake set there and whose tick failed would keep `awakeSince` absent,
and its next tick that answers would record a time later than the duty window's start.

Why: Lemma 16b at `t₀ := dutyWindowStart S s'`; when the spec's value is negative, `t₀ = 0` and
the initial value `proposal_window_start S.C 0` is at most `duty_window_start S.C s'`.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `s'`: the slot of the duty; `t`: the time of the tick; `v`: the validator.

Read aloud: a validator awake from the duty window's start of
slot `s'` through `t`, honest at `t`, starts its tick at `t` with `awakeSince` passing slot `s'`'s
duty test. -/
theorem awakeSince_le_dutyWindowStart_b (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s' t : ℕ) (v : V)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- the duty window's start of slot `s'` is before `t`
    (ht : dutyWindowStart S s' < t)
    -- `v` is awake at every time from the duty window's start to `t`
    (hAwake : ∀ t' : ℕ, dutyWindowStart S s' ≤ t' → t' ≤ t → v ∈ Sched.awake (t' : Int))
    -- `v` is honest at `t`
    (hHonest : v ∉ Sched.adv (t : Int)) :
    -- then `v`'s tick at `t` starts from a record that passes slot `s'`'s duty test
    ∃ τ : Time, (tickInputState x (stepBefore x t) t v).awakeSince = some τ ∧
      τ ≤ duty_window_start S.C s' :=
  GoldilocksCorrectness.Proofs.Executions.awakeSince_le_dutyWindowStart_b S Sched x s' t v hDiv
    hMono ht hAwake hHonest

/-- **`awakeSince` is kept while the validator stays awake.** In an execution where every time is
reached: when `v`'s tick at `t₀` starts from a node state whose `awakeSince` is some time `τ`,
`t₀ ≤ t`, and `v` is awake at every time from `t₀` to `t`, then `v`'s tick at `t` starts from a
node state whose `awakeSince` is the same `τ`.

Why: the tick input at `t₀` is `v`'s stored state, since a validator entering the awake set
starts from the woken state, whose `awakeSince` is absent. The step that ticks at `t₀` keeps the
present value: an answering tick's `record_awake` keeps a present value, a failed tick keeps the
state, and a validator outside the ticking set keeps its state. Every later step before `t` keeps
it too: a delivery keeps `awakeSince`, and `v`, awake at every time from `t₀` to `t`, enters the
awake set at no tick in between, nor at `t` (Lemma 16b's induction, with a present value in place
of the time of the first tick).



The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `t₀`, `t`: the two times; `v`: the validator; `τ`: the time recorded.

Read aloud: a validator that never sleeps keeps the time it has been awake since. -/
theorem awakeSince_kept_of_awake_throughout (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t₀ t : ℕ) (v : V) (τ : Time)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- `t₀` is at most `t`
    (ht : t₀ ≤ t)
    -- `v`'s tick at `t₀` starts from a record of awakeness since `τ`
    (hτ : (tickInputState x (stepBefore x t₀) t₀ v).awakeSince = some τ)
    -- `v` is awake at every time from `t₀` to `t`
    (hAwake : ∀ t' : ℕ, t₀ ≤ t' → t' ≤ t → v ∈ Sched.awake (t' : Int)) :
    -- then `v`'s tick at `t` starts from the same record
    (tickInputState x (stepBefore x t) t v).awakeSince = some τ :=
  GoldilocksCorrectness.Proofs.Executions.awakeSince_kept_of_awake_throughout S Sched x t₀ t v τ
    hDiv ht hτ hAwake

end GoldilocksCorrectness.Statements.Executions
