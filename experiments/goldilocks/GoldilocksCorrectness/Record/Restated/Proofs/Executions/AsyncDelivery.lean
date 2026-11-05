module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AsyncResilienceDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Network
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# AsyncDelivery, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/AsyncDelivery.lean` over a model `M`, for
an execution `x` of `protocolOf M S`: the delivery premises at the ordinary deadline, up to a bound,
and suspended on one asynchronous period; and the environment's promises up to a bound
(`EnvFactsUpTo`) and suspended on one period (`EnvFactsOutside`) giving those premises on a
wake-shaped trace; and the pushed catch-up (`EnvFactsSync`, `EnvFactsUpTo`, `EnvFactsOutside`)
giving the sync fact (`SyncedWithin`, `SyncedWithinUpTo`, `SyncedWithinOutside`) at `max Δ Δw`, for
any selection whose objects every honest holder put on the wire itself once it served them. None
reads a fact of the model. `deadlineOutside_le` names
no member and reads no execution; the twins read the landed one.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Proofs.Executions (deadlineOutside_le mem_awakeThroughout_iff)

open GoldilocksCorrectness.Record.Statements.Executions

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)

section Delivery

variable (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)

/-- `SynchronyFromWake` is `SynchronyFromWakeBy` at the deadline `max t GST + Δ`.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Δ`: the delay; `GST`: the time
  from which the network is synchronous; `ok`: the object class.

Read aloud: synchrony is the deadline form at the ordinary deadline. -/
theorem synchronyFromWake_iff_by (Δ GST : ℕ) (ok : NamedObject V → Prop) {release ΔRedeliver} :
    x.SynchronyFromWake A Δ ΔRedeliver GST release ok ↔
      x.SynchronyFromWakeBy A (fun t => max t GST + Δ) release ΔRedeliver ok :=
  Iff.rfl

/-- `CatchUpOnWake` is `CatchUpOnWakeBy` at the deadline `max t GST + Δ`.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Δ`: the delay; `GST`: the time
  from which the network is synchronous; `ok`: the object class; `release`, `ΔRedeliver`: the
  release clock value of an object and the re-delivery delay.

Read aloud: catch-up on wake is the deadline form at the ordinary deadline. -/
theorem catchUpOnWake_iff_by (Δ GST : ℕ) (ok : NamedObject V → Prop) {release ΔRedeliver} :
    x.CatchUpOnWake A Δ ΔRedeliver GST release ok ↔
      x.CatchUpOnWakeBy A (fun t => max t GST + Δ) release ΔRedeliver ok :=
  Iff.rfl

end Delivery

section DeliveryFacts

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} {Δ GST : ℕ}
  {ok : NamedObject V → Prop}

/-- Synchrony up to `b'` gives synchrony up to every `b ≤ b'`.

The variables:
- `M`: the model;
- `b`, `b'`: the two bounds; `hle`: `b ≤ b'`; `h`: synchrony up to `b'`.

Read aloud: a bound on the deadlines can be lowered. -/
theorem SynchronyFromWakeUpTo.mono {b b' : ℕ} (hle : b ≤ b')
    {release ΔRedeliver} (h : SynchronyFromWakeUpTo M A x Δ ΔRedeliver GST release ok b') : SynchronyFromWakeUpTo M A x Δ ΔRedeliver GST release ok b := by
  intro i k v sm t hs hok hb hk hik hwin hdk hrel
  exact h i k v sm t hs hok (le_trans hb (by exact_mod_cast hle)) hk hik hwin hdk hrel

/-- Catch-up on wake up to `b'` gives catch-up on wake up to every `b ≤ b'`.

The variables:
- `M`: the model;
- `b`, `b'`: the two bounds; `hle`: `b ≤ b'`; `h`: catch-up on wake up to `b'`.

Read aloud: a bound on the deadlines can be lowered. -/
theorem CatchUpOnWakeUpTo.mono {Δw b b' : ℕ} (hle : b ≤ b') {release ΔRedeliver}
    (h : CatchUpOnWakeUpTo M A x Δ Δw ΔRedeliver GST release ok b') :
    CatchUpOnWakeUpTo M A x Δ Δw ΔRedeliver GST release ok b := by
  intro i k v sm t keep k' c' hs hok hk hik hb1 hb2 hkk' hk' hcc' hwin hrel
  have hle' : (b : ℝ) ≤ b' := by exact_mod_cast hle
  exact h i k v sm t keep k' c' hs hok hk hik (le_trans hb1 hle') (le_trans hb2 hle') hkk' hk' hcc' hwin
    hrel

/-- `SynchronyFromWake` gives `SynchronyFromWakeUpTo` at every bound.

The variables:
- `M`: the model;
- `b`: the bound; `h`: synchrony.

Read aloud: the premise gives every bounded one. -/
theorem synchronyFromWakeUpTo_of_synchronyFromWake (b : ℕ)
    {release ΔRedeliver} (h : x.SynchronyFromWake A Δ ΔRedeliver GST release ok) : SynchronyFromWakeUpTo M A x Δ ΔRedeliver GST release ok b := by
  intro i k v sm t hs hok _ hk hik hwin hdk hrel
  exact h i k v sm t hs hok hk hik hwin hdk hrel

/-- Synchrony suspended on `[b₀, b₁)` gives synchrony up to `b₀`.

Why: a send due by `b₀` has `deadlineOutside Δ GST b₀ b₁` equal to its ordinary deadline.

The variables:
- `M`: the model;
- `b₀`, `b₁`: the start and the end of the period; `h`: synchrony suspended on `[b₀, b₁)`.

Read aloud: before the period, the suspended premise is the premise restricted to the sends due
by `b₀`. -/
theorem synchronyFromWakeUpTo_of_outside {b₀ b₁ : ℕ}
    {release ΔRedeliver} (h : x.SynchronyFromWakeOutside A Δ ΔRedeliver GST release ok b₀ b₁) :
    SynchronyFromWakeUpTo M A x Δ ΔRedeliver GST release ok b₀ := by
  intro i k v sm t hs hok hb hk hik hwin hdk hrel
  refine h i k v sm t hs hok hk hik hwin ?_ hrel
  rw [GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR_of_le hb]
  exact hdk

/-- Catch-up on wake suspended on `[b₀, b₁)` gives `CatchUpOnWakeUpTo` up to `b₀` with the
catch-up delay `Δ`.

Why: when the restart's deadline `max x[k].time GST + Δ` is at most `b₀`, `deadlineOutsideR Δ GST b₀ b₁`
at the restart's time is that deadline (`deadlineOutsideR_of_le`), at most the catch-up deadline the
bounded form reads, so a tick at a clock value at least the catch-up deadline is one at least the
suspended deadline, and the two promises read the same tick with the same premise and clause
.

The variables:
- `M`: the model;
- `R`: the run's facts (not read); `E`: the environment's facts (not read); `b₀`, `b₁`: the start
  and the end of the period; `h`: catch-up on wake suspended on `[b₀, b₁)`.

Read aloud: before the period, the suspended catch-up gives the bounded catch-up. -/
theorem catchUpOnWakeUpTo_of_outside_wake (R : RunFacts M S x)
    {deadline : SignedMsg V (NamedObject V) → ℝ → Option ℝ}
    {ok' : NamedObject V → Prop}
    {B : Type} {W : ViewVocab V B (NamedObject V)}
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok' W)
 {b₀ b₁ : ℕ}
    (h : x.CatchUpOnWakeOutside A Δ ΔRedeliver GST release ok b₀ b₁) :
    CatchUpOnWakeUpTo M A x Δ Δ ΔRedeliver GST release ok b₀ := by
  intro i k v sm t keep k' c' hs hok hk hik _ hb2 hkk' hk' hcc' hwin hrel
  refine GoldilocksCorrectness.Statements.AbstractTrace.Trace.CatchUpOnWakeBy.apply_tick h hs hok hk hik
    hkk' hk' ?_ hwin hrel
  rw [GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR_of_le hb2]
  exact le_trans (le_max_right _ _) hcc'

/-- The trace premises `SynchronyFromWake` and `CatchUpOnWake` at `Δ`, beside the non-delivery facts
of any instance `E`, give the synchronous promises with the catch-up delay `Δ`, on a wake-shaped
trace.

Why: the restart's deadline `max x[k].time GST + Δ` is at most the catch-up deadline, and the
catch-up premise and the catch-up promise both read the receiver at any of its ticks after the
restart at a clock value at least the deadline, with the same re-delivery premise and admission clause
.

The variables:
- `M`: the model;
- `R`: the run's facts; `E`: the environment's facts, for their non-delivery fields; `hWS`: the
  trace is wake-shaped (not read); `hs`, `hc`: synchrony and catch-up on wake at `Δ` from `GST`.

Read aloud: the two trace premises are the synchronous promises with the catch-up delay `Δ`. -/
theorem envFactsSync_of_trace (R : RunFacts M S x)
    {deadline : SignedMsg V (NamedObject V) → ℝ → Option ℝ}
    {ok' : NamedObject V → Prop}
    {B : Type} {W : ViewVocab V B (NamedObject V)}
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok' W)
 (hs : x.SynchronyFromWake A Δ ΔRedeliver GST release ok)
    (hc : x.CatchUpOnWake A Δ ΔRedeliver GST release ok) :
    GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsSync A x ΔClockAhead ΔClockBehind Δ Δ ΔRedeliver GST release ok W := by
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  refine { toEnvFactsBy := (envFactsBy_of_synchronyFromWakeBy M) x E hs, caught_up := ?_ }
  intro i k v sm t keep c k' c' hs' hok hk hlt hc' hkk' hk' hcc' hwin hrel
  have hik := htime (show i + 1 ≤ k from hlt)
  have hc'' : max (max (x.time (i + 1)) GST + Δ) (max (x.time k) GST + Δ) = c :=
    Option.some.inj hc'
  -- the catch-up premise read at the same tick, at a clock value at least `c`
  exact GoldilocksCorrectness.Statements.AbstractTrace.Trace.CatchUpOnWakeBy.apply_tick hc hs' hok hk hlt hkk' hk'
    (show max (x.time k) (GST : ℝ) + Δ ≤ c' by
      have := le_max_right (max (x.time (i + 1)) (GST : ℝ) + Δ) (max (x.time k) (GST : ℝ) + Δ)
      linarith) hwin hrel

/-- Synchrony suspended on `[b₀, b₁)` gives `SynchronyFromWake` at `GST' := max b₁ GST`: every
send is delivered within `Δ` of the latest of its time, `b₁` and `GST`. No hypothesis `b₀ ≤ b₁`
is needed.

Why: `deadlineOutsideR Δ GST b₀ b₁ t ≤ max t (max b₁ GST) + Δ` (`deadlineOutsideR_le_after`), so a
receiver awake and honest through the later deadline is so through the earlier one.

The variables:
- `M`: the model;
- `b₀`, `b₁`: the start and the end of the period; `h`: synchrony suspended on `[b₀, b₁)`.

Read aloud: once the period is over, the network is the ordinary synchronous network whose `GST`
is `b₁`. -/
theorem synchronyFromWake_of_outside_after {b₀ b₁ : ℕ}
    {release ΔRedeliver} (h : x.SynchronyFromWakeOutside A Δ ΔRedeliver GST release ok b₀ b₁) :
    x.SynchronyFromWake A Δ ΔRedeliver (max b₁ GST) release ok := by
  intro i k v sm t hsend hok hk hik hwin hd hrel
  have hle : GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR Δ GST b₀ b₁ (x.time (i + 1)) ≤
      max (x.time (i + 1)) ((max b₁ GST : ℕ) : ℝ) + Δ := by
    rw [Nat.cast_max]
    exact GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR_le_after Δ GST b₀ b₁ _
  exact h i k v sm t hsend hok hk hik hwin (le_trans hle hd) hrel

/-- Catch-up on wake suspended on `[b₀, b₁)` gives `CatchUpOnWake` at `GST' := max b₁ GST`.

Why: as for synchrony, from `deadlineOutsideR_le_after`.

The variables:
- `M`: the model;
- `b₀`, `b₁`: the start and the end of the period; `h`: catch-up on wake suspended on `[b₀, b₁)`.

Read aloud: once the period is over, a waking validator catches up as in the ordinary synchronous
network whose `GST` is `b₁`. -/
theorem catchUpOnWake_of_outside_after {b₀ b₁ : ℕ} {release ΔRedeliver}
    (h : x.CatchUpOnWakeOutside A Δ ΔRedeliver GST release ok b₀ b₁) :
    x.CatchUpOnWake A Δ ΔRedeliver (max b₁ GST) release ok := by
  intro i k v sm t keep k' c' hs hok hk hlt hkk' hk' hcc' hwin hrel
  have hle : GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR Δ GST b₀ b₁ (x.time k) ≤
      max (x.time k) ((max b₁ GST : ℕ) : ℝ) + Δ := by
    rw [Nat.cast_max]
    exact GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR_le_after Δ GST b₀ b₁ _
  exact GoldilocksCorrectness.Statements.AbstractTrace.Trace.CatchUpOnWakeBy.apply_tick h hs hok hk hlt hkk' hk' (le_trans hle hcc') hwin hrel

end DeliveryFacts

section Bridges

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy deadlineUpTo)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsUpTo EnvFactsOutside deadlineUpTo_eq_some
  catchUpUpTo_eq_some add_le_deadlineOutside deadlineOutside_mono_time deadlineOutside_mono_delay)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} {Δ Δw GST : ℕ}
  {ok : NamedObject V → Prop} {B : Type} {W : ViewVocab V B (NamedObject V)}

/-- The delivery promise up to `b` (with any catch-up promise, none included) gives
`SynchronyFromWakeUpTo` at `b`, on a wake-shaped trace and for a delay `Δ ≥ 1`: the step bound of `EnvFactsBy.delivered` gives back the time bound, since the
receiver is awake one time before the deadline and so does not wake at it.

The variables:
- `M`: the model;
- `R`: the run's facts; `hΔ`: `1 ≤ Δ`; `E`: the promises up to `b`.

Read aloud: the bounded promises give the bounded synchrony premise. -/
theorem envFactsUpTo_synchronyFromWakeUpTo (R : RunFacts M S x) (hΔ : 1 ≤ Δ)
    {b : ℕ}
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind (fun _ a => deadlineUpTo Δ GST b a) release ΔRedeliver ok W) :
    SynchronyFromWakeUpTo M A x Δ ΔRedeliver GST release ok b := by
  intro i k v sm t hs hok hb hk hik hwin hdk hrel
  exact E.delivered i k v sm t _ hs hok hk hik hwin (deadlineUpTo_eq_some.2 ⟨hb, rfl⟩) hdk hrel

/-- The delivery promise suspended on `[b₀, b₁)` (with any catch-up promise, none included) gives
`SynchronyFromWakeOutside` on that period, on a wake-shaped trace and for a delay `Δ ≥ 1`.

The variables:
- `M`: the model;
- `R`: the run's facts; `hΔ`: `1 ≤ Δ`; `E`: the promises
  suspended on `[b₀, b₁)`.

Read aloud: the suspended promises give the suspended synchrony premise. -/
theorem envFactsOutside_synchronyFromWakeOutside (R : RunFacts M S x) (hΔ : 1 ≤ Δ)
 {b₀ b₁ : ℕ}
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind (fun _ a => some (GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR Δ GST b₀ b₁ a)) release ΔRedeliver ok W) :
    x.SynchronyFromWakeOutside A Δ ΔRedeliver GST release ok b₀ b₁ := by
  intro i k v sm t hs hok hk hik hwin hdk hrel
  exact E.delivered i k v sm t _ hs hok hk hik hwin rfl hdk hrel

/-- The promises suspended on `[b₀, b₁)` give `CatchUpOnWakeOutside` on that period at the delay
`max Δ Δw`, on a wake-shaped trace and for a delay `Δ ≥ 1`: the catch-up deadline, the later of the
message's and the restart's, is at most `deadlineOutside (max Δ Δw) GST b₀ b₁` at the restart's
time, and the catch-up promise is read at the receiver's tick the premise names
(`CatchUpAfterRestartBy.apply_tick`).

The variables:
- `M`: the model;
- `R`: the run's facts; `hΔ`: `1 ≤ Δ` (not read); (not read); `E`:
  the promises suspended on `[b₀, b₁)`.

Read aloud: the suspended promises give the suspended catch-up premise, at the larger of the two
delays. -/
theorem envFactsOutside_catchUpOnWakeOutside (R : RunFacts M S x) (hΔ : 1 ≤ Δ)
 {b₀ b₁ : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsOutside A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver GST release ok W b₀ b₁) :
    x.CatchUpOnWakeOutside A (max Δ Δw) ΔRedeliver GST release ok b₀ b₁ := by
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  intro i k v sm t keep k' c' hs hok hk hlt hkk' hk' hcc' hwin hrel
  -- the catch-up deadline is at most the suspended deadline at `max Δ Δw`
  have h1 : GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR Δ GST b₀ b₁ (x.time (i + 1)) ≤
      GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR (max Δ Δw) GST b₀ b₁ (x.time k) :=
    le_trans (GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR_mono_time
        (htime (show i + 1 ≤ k from hlt)))
      (GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR_mono_delay (le_max_left _ _))
  have h2 : GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR Δw GST b₀ b₁ (x.time k) ≤
      GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR (max Δ Δw) GST b₀ b₁ (x.time k) :=
    GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR_mono_delay (le_max_right _ _)
  -- the catch-up promise read at the same tick, at a clock reading at least the catch-up deadline
  exact E.caught_up.apply_tick hs hok hk hlt rfl hkk' hk' (le_trans (max_le h1 h2) hcc') hwin hrel

end Bridges

section SyncBridges

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsSync EnvFactsUpTo EnvFactsOutside
  SyncedWithin SyncedWithinUpTo SyncedWithinOutside deadlineUpTo_eq_some deadlineOutside_of_le)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} {Δ Δw GST : ℕ}
  {ok : NamedObject V → Prop}

/-- **The bridge from the delivery field, at a tick.** A message an honest validator put on the
wire at step `i`, whose deadline `d` is at most the time of `v`'s tick `k` (to any reading), with
`v` active after every step from `i + 1` up to `k`, is delivered to `v` at a step after `i` and
before `k`.

Why: a delivery before `k` is the conclusion; when there is none, the field's re-delivery premise
is about a delivery that does not exist, so the field at `k` gives one.

The variables:
- `M`: the model;
- `x`: the execution; `E`: the environment's facts; `i`: the step of the send; `k`: `v`'s tick, to
  the reading `D`; `v`: the receiver; `sm`: the signed message; `d`: its deadline;
- `j`: the step of the delivery.

Read aloud: a message an honest validator put on the wire reaches a receiver active from the send
up to a tick at or after its deadline, before that tick. -/
theorem delivered_before_tick_of_field
    {deadline : SignedMsg V (NamedObject V) → ℝ → Option ℝ} {ok : NamedObject V → Prop}
    {B : Type} {W : ViewVocab V B (NamedObject V)} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver
      ok W)
    {i k : ℕ} {v : V} {sm : SignedMsg V (NamedObject V)} {d : ℝ} {D : ℕ}
    (hsend : x.HonestSendAt A i sm) (hok : ok sm.msg)
    -- the message's deadline from the time after the send is `d`
    (hd : deadline sm (x.time (i + 1)) = some d)
    -- the step `k` is `v`'s tick to `D`, after the send, at a time at least `d`
    (hk : x.lbl k = Event.tick v D) (hik : i < k) (hdk : d ≤ x.time k)
    -- `v` is active after every step from the send on up to `k`
    (hwin : ∀ j : ℕ, i + 1 ≤ j → j ≤ k → v ∈ A.active j) :
    ∃ j : ℕ, i < j ∧ x.lbl j = Event.deliver v sm ∧ j < k := by
  classical
  by_cases hdel : ∃ j₀ : ℕ, i < j₀ ∧ j₀ < k ∧ x.lbl j₀ = Event.deliver v sm
  · obtain ⟨j₀, h1, h2, h3⟩ := hdel
    exact ⟨j₀, h1, h3, h2⟩
  · obtain ⟨j, hij, hjk, hl, -, -⟩ := E.delivered i k v sm D d hsend hok hk hik hwin hd hdk
      (fun _ j₀ _ _ _ hij₀ hl₀ _ hj₀k₁ hk₁k _ _ _ => absurd ⟨j₀, hij₀, by omega, hl₀⟩ hdel)
    exact ⟨j, hij, hl, hjk⟩

/-- **The sync fact from the delivery field and the catch-up field, at the holder's clock values
(T-S1, T-S2).** For every selection `serves` whose objects an honest holder put on the wire itself at
a step after which it already served them at its clock value then (`hrelay`), the sync fact
`SyncedWithinBy A x serves ok sync ΔHolderOnline` holds when, for every receiver `w`, signed message
`sm`, time `t` and sync deadline `d` the fact names, the deadline is at least `t + ΔClockAhead`, the
delivery deadline of a message on the wire at a time `a < t` is at most `d − ΔClockAhead` (`hdel`),
and its catch-up deadline for a restart at a time `r < t` is at most `d` (`hcu`).

Why: the holder `u` serves `o` after its step `k` at a time less than `t`, so it put `⟨u, o⟩` on the
wire at a step `i < k`, at a time less than `t`. The receiver `w` ticks at `k'` to a clock value
`d' ≥ d`, at a real time at least `d' − ΔClockAhead ≥ d − ΔClockAhead ≥ t`
(`tick_active`), so after the send. When `w` is active at every
step from `i + 1` to `k'`, the delivery field `delivered` read at `k'` delivers the message before
`k'`, its deadline being at most the time of `k'`. Otherwise `w` was not awake at some step after the
send (it is outside the adversary set at `k'`, and the adversary set only grows), so it was restarted
at the last such step `r < k'`, at a time less than `t` (`w` is active at every step at a time at least
`t` up to `k'`); the catch-up field, read at `k'` itself, delivers the message before `k'`. In both cases the field's
re-delivery premise is the sync fact's, which covers every delivery of `⟨u, o⟩` to `w`,
and the field's admission clause at `d'` is the sync fact's. The serving step the fact names is
`i + 1`.

The variables:
- `M`: the model;
- `R`: the run's facts; `E`: the environment's facts with the delivery deadline `deadline`; `hcatch`:
  the catch-up promise with the deadline `catchUp`; `serves`: the selection; `sync`: the sync
  deadline; `ΔHolderOnline`: how long the holder is active (not read);
- `hdel`, `hcu`: the two deadlines against the sync deadline; `hrelay`: what an honest holder serves
  at its clock value, it put on the wire itself at a step after which it already served it at its
  clock value then.

Read aloud: when the network delivers each message, and catches each restarted validator up, by the
sync deadline less the clock-ahead bound and by the sync deadline respectively, what an honest
holder serves reaches every receiver active up to a tick of its to a clock value at least the sync
deadline before that tick. -/
theorem syncedWithinBy_of_fields (R : RunFacts M S x)
    {deadline : SignedMsg V (NamedObject V) → ℝ → Option ℝ}
    {catchUp : SignedMsg V (NamedObject V) → ℝ → ℝ → Option ℝ}
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release
      ΔRedeliver ok GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hcatch : GoldilocksCorrectness.Statements.AbstractTrace.CatchUpAfterRestartBy A x catchUp release
      ΔRedeliver ok)
    {serves : M.N → ℕ → NamedObject V → Prop}
    {sync : V → SignedMsg V (NamedObject V) → ℕ → Option ℕ} {ΔHolderOnline : ℝ}
    -- the sync deadline is at least `t + ΔClockAhead`, and a message on the wire at `a < t` is due
    -- at most `ΔClockAhead` before it
    (hdel : ∀ (w : V) (sm : SignedMsg V (NamedObject V)) (t d : ℕ) (a : ℝ), sync w sm t = some d →
      a < t → (t : ℝ) + ΔClockAhead ≤ d ∧ ∃ dd : ℝ, deadline sm a = some dd ∧ dd + ΔClockAhead ≤ d)
    -- a restart at `r < t` catches the receiver up on a message on the wire at `a < t` by the sync
    -- deadline
    (hcu : ∀ (w : V) (sm : SignedMsg V (NamedObject V)) (t d : ℕ) (a r : ℝ), sync w sm t = some d →
      a < t → r < t → ∃ c : ℝ, catchUp sm a r = some c ∧ c ≤ d)
    -- what an honest holder serves at its clock value, it put on the wire itself once it served it
    (hrelay : ∀ (k : ℕ) (u : V) (o : NamedObject V), ok o →
      u ∉ A.corrupted k → serves (x.st k u) (x.clockValue k u) o →
      ∃ i : ℕ, i < k ∧ x.HonestSendAt A i ⟨u, o⟩ ∧ serves (x.st (i + 1) u) (x.clockValue (i + 1) u) o) :
    GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithinBy A x serves ok release ΔRedeliver sync ΔHolderOnline := by
  classical
  intro t k u w o d d' k' hkt _ hu ho hok _ hsync hk' hdd' hwR hprem
  have hdd'R : (d : ℝ) ≤ d' := by exact_mod_cast hdd'
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  obtain ⟨i, hik, hsend, hoi⟩ := hrelay k u o hok (Activity.not_mem_corrupted_of_mem_active hu) ho
  have hit : x.time (i + 1) < t := lt_of_le_of_lt (htime (Nat.succ_le_of_lt hik)) hkt
  -- the deadline is computed at the clock value `⌈t⌉₊ ≥ t` ( with (a′))
  have htc : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
  obtain ⟨htd, dd, hdd, hddle⟩ := hdel w ⟨u, o⟩ ⌈t⌉₊ d (x.time (i + 1)) hsync (lt_of_lt_of_le hit htc)
  have hk'time := (E.tick_active k' w d' hk').2.1
  have htk' : t ≤ x.time k' := by linarith
  have hik' : i < k' := by
    by_contra h
    have := htime (show k' ≤ i + 1 by omega)
    linarith
  have hwk' := Activity.mem_active.1 (hwR k' htk' le_rfl)
  refine Or.inr ?_
  by_cases hall : ∀ j : ℕ, i + 1 ≤ j → j ≤ k' → w ∈ A.active j
  · -- `w` active since the send: the delivery field at `k'`, whose re-delivery premise is the sync
    -- fact's (: over every delivery of `⟨u, o⟩` to `w`)
    obtain ⟨j, hij, hjk, hl, hadm, -⟩ := E.delivered i k' w ⟨u, o⟩ d' dd hsend hok hk' hik' hall hdd
      (by linarith)
      (fun r j₀ k₁ t₁ hr _ hl₀ hnr hj₀k₁ hk₁k' hk₁ hrt₁ hfirst =>
        hprem r j₀ k₁ t₁ hr hl₀ hnr hj₀k₁ hk₁k' hk₁ hrt₁ hfirst)
    exact ⟨j, i + 1, by omega, hit, hoi, hl, hjk, hadm, fun l h1 h2 => hall l (by omega) h2⟩
  · -- `w` not active at a step `l` after the send: not awake there, since outside the adversary set
    push_neg at hall
    obtain ⟨l, hl1, hl2, hlna⟩ := hall
    have hlaw : w ∉ A.awake l := by
      intro haw
      have hc : w ∈ A.corrupted l := by
        by_contra hc
        exact hlna (Activity.mem_active.2 ⟨haw, hc⟩)
      exact hwk'.2 (E.corrupted_mono l k' hl2 hc)
    -- the last step before `k'` at which `w` is not awake, a restart
    obtain ⟨r, hr⟩ : ∃ r, r = Nat.findGreatest (fun r => w ∉ A.awake r) k' := ⟨_, rfl⟩
    have hlr : l ≤ r := hr ▸ Nat.le_findGreatest (P := fun r => w ∉ A.awake r) hl2 hlaw
    have hrna : w ∉ A.awake r := hr ▸ Nat.findGreatest_spec (P := fun r => w ∉ A.awake r) hl2 hlaw
    have hrk : r < k' := by
      refine lt_of_le_of_ne (hr ▸ Nat.findGreatest_le k') ?_
      intro h
      rw [h] at hrna
      exact hrna hwk'.1
    have hafter : ∀ j : ℕ, r < j → j ≤ k' → w ∈ A.awake j := fun j h1 h2 => by
      by_contra h
      exact Nat.findGreatest_is_greatest (P := fun r => w ∉ A.awake r) (hr ▸ h1) h2 h
    have hactive : ∀ j : ℕ, r < j → j ≤ k' → w ∈ A.active j := fun j h1 h2 =>
      Activity.mem_active.2 ⟨hafter j h1 h2, fun hc => hwk'.2 (E.corrupted_mono j k' h2 hc)⟩
    obtain ⟨tr, keep, hlr'⟩ := E.restart_of_awake r w hrna (hafter (r + 1) (by omega) (by omega))
    have hrt : x.time r < t := by
      by_contra h
      push_neg at h
      exact hrna (Activity.mem_active.1 (hwR r h hrk.le)).1
    obtain ⟨c, hc, hcd⟩ := hcu w ⟨u, o⟩ ⌈t⌉₊ d (x.time (i + 1)) (x.time r) hsync (lt_of_lt_of_le hit htc)
      (lt_of_lt_of_le hrt htc)
    -- the catch-up field read at `k'` itself (: any tick at a clock value at least `c`), its
    -- re-delivery premise from the sync fact's, its admission clause at `d'`
    obtain ⟨j, hrj, hjk, hl, hadm, -⟩ := hcatch i r w ⟨u, o⟩ tr keep c k' d' hsend hok hlr'
      (by omega) hc hrk hk' (le_trans hcd hdd'R) hactive
      (fun r' j₀ k₁ t₁ hr' _ hl₀ hnr hj₀k₁ hk₁k' hk₁ hrt₁ hfirst =>
        hprem r' j₀ k₁ t₁ hr' hl₀ hnr hj₀k₁ hk₁k' hk₁ hrt₁ hfirst)
    exact ⟨j, i + 1, by omega, hit, hoi, hl, hjk, hadm, fun l h1 h2 => hactive l (by omega) h2⟩

/-- The suspended delivery deadline of a message on the wire at a real time `a ≤ t`, plus `A ≥ 0`, is
at most the suspended sync deadline of `t` when `Δ + A ≤ Δs`: both deadlines grow with the time and
the delay, and the bound `b₀` cuts both at the same time.

The variables:
- `Δ`, `Δs`: the two delays; `GST`, `b₀`, `b₁`: the synchrony time and the period; `a`, `t`: the two
  times; `A`: the slack.

Read aloud: a message on the wire no later than `t` is due, suspended, at least `A` before the
suspended sync deadline of `t` when the sync delay exceeds the delay by `A`. -/
theorem deadlineOutsideR_add_le_deadlineOutside {Δ Δs GST b₀ b₁ t : ℕ} {a A : ℝ} (hA : 0 ≤ A)
    (hΔ : (Δ : ℝ) + A ≤ Δs) (hat : a ≤ t) :
    GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR Δ GST b₀ b₁ a + A ≤
      (GoldilocksCorrectness.Statements.Network.deadlineOutside Δs GST b₀ b₁ t : ℝ) := by
  have hm1 : max a (GST : ℝ) ≤ max (t : ℝ) GST := max_le_max hat le_rfl
  have hm2 : max a (max (b₁ : ℝ) GST) ≤ max (t : ℝ) (max b₁ GST) := max_le_max hat le_rfl
  have hm3 : max (t : ℝ) GST ≤ max (t : ℝ) (max b₁ GST) := max_le_max le_rfl (le_max_right _ _)
  have hm4 : max a (GST : ℝ) ≤ max a (max (b₁ : ℝ) GST) := max_le_max le_rfl (le_max_right _ _)
  unfold GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR
    GoldilocksCorrectness.Statements.Network.deadlineOutside
  split_ifs with h1 h2 h2
  · push_cast; linarith
  · push_cast; linarith
  · have h2' : max (t : ℝ) GST + Δs ≤ b₀ := by exact_mod_cast h2
    exfalso; exact h1 (by linarith)
  · push_cast; linarith

/-- The pushed catch-up up to `b` gives the sync fact up to `b` at every sync delay `Δs` with
`Δ + ΔClockAhead ≤ Δs` and `max Δ Δw ≤ Δs` (T-S2), for every selection whose objects an honest holder
put on the wire itself at a step after which it already served them at its clock value then (T-S1):
`syncedWithinBy_of_fields`, the deadlines of the bounded promises being at most the bounded sync
deadline less `ΔClockAhead` (the delivery) and at most it (the catch-up).

The variables:
- `M`: the model;
- `R`: the run's facts; `b`: the bound; `E`: the promises up to `b`; `Δs`: the sync delay; `hΔA`,
  `hΔw`: the sync delay is at least the delay plus the clock-ahead bound, and at least the catch-up
  delay; `serves`: the selection; `hrelay`: what an honest holder serves at its clock value, it put on
  the wire itself at a step after which it already served it at its clock value then.

Read aloud: a network that pushes the backlog within `Δw` of a wake is one in which what honest
active validators would serve spreads within `Δs`, up to the bound `b`. -/
theorem syncedWithinUpTo_of_envFactsUpTo (R : RunFacts M S x)
    {b : ℕ}
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsUpTo A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver GST release ok
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b)
    {Δs : ℕ} (hΔA : (Δ : ℝ) + ΔClockAhead ≤ Δs) (hΔw : max Δ Δw ≤ Δs)
    {serves : M.N → ℕ → NamedObject V → Prop}
    (hrelay : ∀ (k : ℕ) (u : V) (o : NamedObject V), ok o →
      u ∉ A.corrupted k → serves (x.st k u) (x.clockValue k u) o →
      ∃ i : ℕ, i < k ∧ x.HonestSendAt A i ⟨u, o⟩ ∧ serves (x.st (i + 1) u) (x.clockValue (i + 1) u) o) :
    SyncedWithinUpTo A x serves ok release ΔRedeliver Δs GST b := by
  have hA := E.ahead_nonneg
  have hΔs : (Δ : ℝ) ≤ Δs := by exact_mod_cast le_trans (le_max_left _ _) hΔw
  have hΔws : (Δw : ℝ) ≤ Δs := by exact_mod_cast le_trans (le_max_right _ _) hΔw
  refine (syncedWithinBy_of_fields M) R E.toEnvFactsBy E.caught_up ?_ ?_ hrelay
  · intro w sm t d a hd ha
    obtain ⟨hb, rfl⟩ := deadlineUpTo_eq_some.1 hd
    have hbR : ((max t GST + Δs : ℕ) : ℝ) ≤ b := by exact_mod_cast hb
    push_cast at hbR
    have hm : max a (GST : ℝ) ≤ max (t : ℝ) GST := max_le_max ha.le le_rfl
    have ht : (t : ℝ) ≤ max (t : ℝ) GST := le_max_left _ _
    refine ⟨by push_cast; linarith, max a GST + Δ, deadlineUpTo_eq_some.2 ⟨by linarith, rfl⟩,
      by push_cast; linarith⟩
  · intro w sm t d a r hd ha hr
    obtain ⟨hb, rfl⟩ := deadlineUpTo_eq_some.1 hd
    have hbR : ((max t GST + Δs : ℕ) : ℝ) ≤ b := by exact_mod_cast hb
    push_cast at hbR
    have hm : max a (GST : ℝ) ≤ max (t : ℝ) GST := max_le_max ha.le le_rfl
    have hm' : max r (GST : ℝ) ≤ max (t : ℝ) GST := max_le_max hr.le le_rfl
    refine ⟨max (max a GST + Δ) (max r GST + Δw),
      GoldilocksCorrectness.Statements.AbstractTrace.catchUpUpTo_eq_some.2 ⟨by linarith, by linarith, rfl⟩, ?_⟩
    push_cast
    exact max_le (by linarith) (by linarith)

/-- The pushed catch-up gives the sync fact at every sync delay `Δs` with `Δ + ΔClockAhead ≤ Δs` and
`max Δ Δw ≤ Δs` (T-S2), for every selection whose objects an honest holder put on the wire itself at
a step after which it already served them at its clock value then (T-S1): `syncedWithinBy_of_fields`.

The variables:
- `M`: the model;
- `R`: the run's facts; `E`: the synchronous promises; `Δs`: the sync delay; `hΔA`, `hΔw`: the sync
  delay is at least the delay plus the clock-ahead bound, and at least the catch-up delay; `serves`:
  the selection; `hrelay`: what an honest holder serves at its clock value, it put on the wire itself
  at a step after which it already served it at its clock value then.

Read aloud: a network that pushes the backlog within `Δw` of a wake is one in which what honest
active validators would serve spreads within `Δs`, whatever the selection, provided an honest
validator put on the wire itself, once it served it, everything it serves. -/
theorem syncedWithin_of_envFactsSync (R : RunFacts M S x)
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsSync A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver GST release ok GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {Δs : ℕ} (hΔA : (Δ : ℝ) + ΔClockAhead ≤ Δs) (hΔw : max Δ Δw ≤ Δs)
    {serves : M.N → ℕ → NamedObject V → Prop}
    (hrelay : ∀ (k : ℕ) (u : V) (o : NamedObject V), ok o →
      u ∉ A.corrupted k → serves (x.st k u) (x.clockValue k u) o →
      ∃ i : ℕ, i < k ∧ x.HonestSendAt A i ⟨u, o⟩ ∧ serves (x.st (i + 1) u) (x.clockValue (i + 1) u) o) :
    SyncedWithin A x serves ok release ΔRedeliver Δs GST := by
  have hA := E.ahead_nonneg
  have hΔs : (Δ : ℝ) ≤ Δs := by exact_mod_cast le_trans (le_max_left _ _) hΔw
  have hΔws : (Δw : ℝ) ≤ Δs := by exact_mod_cast le_trans (le_max_right _ _) hΔw
  refine (syncedWithinBy_of_fields M) R E.toEnvFactsBy E.caught_up ?_ ?_ hrelay
  · intro w sm t d a hd ha
    simp only [GoldilocksCorrectness.Statements.AbstractTrace.syncDeadline, Option.some.injEq] at hd
    subst hd
    have hm : max a (GST : ℝ) ≤ max (t : ℝ) GST := max_le_max ha.le le_rfl
    have ht : (t : ℝ) ≤ max (t : ℝ) GST := le_max_left _ _
    refine ⟨by push_cast; linarith, max a GST + Δ, rfl, by push_cast; linarith⟩
  · intro w sm t d a r hd ha hr
    simp only [GoldilocksCorrectness.Statements.AbstractTrace.syncDeadline, Option.some.injEq] at hd
    subst hd
    have hm : max a (GST : ℝ) ≤ max (t : ℝ) GST := max_le_max ha.le le_rfl
    have hm' : max r (GST : ℝ) ≤ max (t : ℝ) GST := max_le_max hr.le le_rfl
    refine ⟨max (max a GST + Δ) (max r GST + Δw), rfl, ?_⟩
    push_cast
    exact max_le (by linarith) (by linarith)

/-- The pushed catch-up gives the sync fact over the minimal selection `servesMin M S.C` at every sync
delay `Δs` with `Δ + ΔClockAhead ≤ Δs` and `max Δ Δw ≤ Δs`: `syncedWithin_of_envFactsSync` at that
selection.

The variables:
- `M`: the model;
- `R`: the run's facts; `E`: the synchronous promises; `Δs`: the sync delay; `hΔA`, `hΔw`: its two
  bounds; `hrelay`: what an honest holder serves at its clock value by the minimal selection, it put
  on the wire itself at a step after which it already served it at its clock value then.

Read aloud: the pushed catch-up gives the sync fact over the minimal selection. -/
theorem syncedWithin_servesMin_of_envFactsSync (R : RunFacts M S x)
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsSync A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver GST release ok GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {Δs : ℕ} (hΔA : (Δ : ℝ) + ΔClockAhead ≤ Δs) (hΔw : max Δ Δw ≤ Δs)
    (hrelay : ∀ (k : ℕ) (u : V) (o : NamedObject V), ok o →
      u ∉ A.corrupted k → servesMin M S.C (x.st k u) (x.clockValue k u) o →
      ∃ i : ℕ, i < k ∧ x.HonestSendAt A i ⟨u, o⟩ ∧
        servesMin M S.C (x.st (i + 1) u) (x.clockValue (i + 1) u) o) :
    SyncedWithin A x (servesMin M S.C) ok release ΔRedeliver Δs GST :=
  syncedWithin_of_envFactsSync M R E hΔA hΔw hrelay

/-- The pushed catch-up suspended on `[b₀, b₁)` gives the sync fact suspended on it at every sync
delay `Δs` with `Δ + ΔClockAhead ≤ Δs` and `max Δ Δw ≤ Δs` (T-S2), for every selection whose objects
an honest holder put on the wire itself at a step after which it already served them at its clock
value then (T-S1): `syncedWithinBy_of_fields`, the suspended deadlines growing with the time and the
delay (`deadlineOutsideR_add_le_deadlineOutside`).

The variables:
- `M`: the model;
- `R`: the run's facts; `E`: the promises suspended on `[b₀, b₁)`; `Δs`: the sync delay; `hΔA`,
  `hΔw`: its two bounds; `serves`: the selection; `hrelay`: what an honest holder serves at its clock
  value, it put on the wire itself at a step after which it already served it at its clock value then.

Read aloud: the suspended pushed catch-up gives the suspended sync fact, whatever the selection
whose objects the holder put on the wire once it served them. -/
theorem syncedWithinOutside_of_envFactsOutside (R : RunFacts M S x)
    {b₀ b₁ : ℕ}
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsOutside A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver GST release ok
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b₀ b₁)
    {Δs : ℕ} (hΔA : (Δ : ℝ) + ΔClockAhead ≤ Δs) (hΔw : max Δ Δw ≤ Δs)
    {serves : M.N → ℕ → NamedObject V → Prop}
    (hrelay : ∀ (k : ℕ) (u : V) (o : NamedObject V), ok o →
      u ∉ A.corrupted k → serves (x.st k u) (x.clockValue k u) o →
      ∃ i : ℕ, i < k ∧ x.HonestSendAt A i ⟨u, o⟩ ∧ serves (x.st (i + 1) u) (x.clockValue (i + 1) u) o) :
    SyncedWithinOutside A x serves ok release ΔRedeliver Δs GST b₀ b₁ := by
  have hA := E.ahead_nonneg
  have hΔs : (Δ : ℝ) ≤ Δs := by exact_mod_cast le_trans (le_max_left _ _) hΔw
  have hΔws : (Δw : ℝ) ≤ Δs := by exact_mod_cast le_trans (le_max_right _ _) hΔw
  have hΔ0 : (0 : ℝ) ≤ Δ := Nat.cast_nonneg _
  refine (syncedWithinBy_of_fields M) R E.toEnvFactsBy E.caught_up ?_ ?_ hrelay
  · intro w sm t d a hd ha
    simp only [Option.some.injEq] at hd
    subst hd
    have h1 := deadlineOutsideR_add_le_deadlineOutside (Δ := Δ) (Δs := Δs) (GST := GST) (b₀ := b₀)
      (b₁ := b₁) (t := t) hA hΔA ha.le
    have h2 := GoldilocksCorrectness.Statements.AbstractTrace.add_le_deadlineOutsideR Δ GST b₀ b₁ (t : ℝ)
    have h3 := deadlineOutsideR_add_le_deadlineOutside (Δ := Δ) (Δs := Δs) (GST := GST) (b₀ := b₀)
      (b₁ := b₁) (t := t) hA hΔA (le_refl (t : ℝ))
    exact ⟨by linarith, _, rfl, h1⟩
  · intro w sm t d a r hd ha hr
    simp only [Option.some.injEq] at hd
    subst hd
    refine ⟨_, rfl, max_le ?_ ?_⟩
    · have := deadlineOutsideR_add_le_deadlineOutside (Δ := Δ) (Δs := Δs) (GST := GST) (b₀ := b₀)
        (b₁ := b₁) (t := t) (A := 0) le_rfl (by linarith) ha.le
      linarith
    · have := deadlineOutsideR_add_le_deadlineOutside (Δ := Δw) (Δs := Δs) (GST := GST) (b₀ := b₀)
        (b₁ := b₁) (t := t) (A := 0) le_rfl (by linarith) hr.le
      linarith

end SyncBridges


end GoldilocksCorrectness.Record.Proofs.Executions

