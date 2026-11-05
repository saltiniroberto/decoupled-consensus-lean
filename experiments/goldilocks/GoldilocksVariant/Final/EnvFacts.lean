import GoldilocksVariant.Final.Network
import GoldilocksVariant.Final.Unforgeable

/-!
# The environment's facts on the projection of a run of Goldilocks

For a run `π` of `variantProtocolOf M S`, read as the trace `toTrace (M.initial S.C) π` with the
activity `activityOf π` and the vocabulary `Vocab.goldilocks`, the structures the top statements
take, assembled field by field from `GoldilocksVariant.Final.Instance` (the fields that read no
protocol fact), `GoldilocksVariant.Final.Unforgeable` (`other_sent`) and
`GoldilocksVariant.Final.Network` (`delivered`, `caught_up`):

- `envFactsBy_toTrace`: `EnvFactsBy` at any deadline function of the trace at least the run's
  deadline `dl`, any release readings, any re-delivery delay and any class of messages;
  `envFactsBy_toTrace_some` at the trace's deadline `some (dl sm.msg a)`;
- `envFactsDelivery_toTrace`: `EnvFactsDelivery`, the synchronous delivery promise, from the run's
  synchronous deadline `syncDeadline tGST ΔDelay`;
- `envFactsDeliveryOutside_toTrace`: `EnvFactsDeliveryOutside`, the delivery promise suspended on an
  asynchronous period, from the run's `deadlineOutside tGST ΔDelay tAsyncStart tAsyncEnd`;
- `envFactsSync_toTrace`: `EnvFactsSync`, the synchronous delivery promise and the catch-up after a
  restart;
- `envFactsNoDelivery_toTrace`: `EnvFactsBy` with no delivery promised, from the conditions on the
  run that read no delivery;
- `envFactsOutside_toTrace`: `EnvFactsOutside`, the delivery promise and the catch-up after a
  restart, both suspended on an asynchronous period.

Each takes exactly the conditions on the run that its fields use. The sync fact is assembled on
`GoldilocksVariant.Final.Sync`.

`releaseOf_goldilocks`: at the spec's model, the trace's release readings `releaseOf M S.C` are
LARuns's `goldilocksRelease S`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GoldilocksVariant.Final

open RStsVariant2 (Exec Envelope Protocol)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFactsBy EnvFactsDelivery
  EnvFactsSync EnvFactsDeliveryOutside EnvFactsOutside deadlineOutsideR)
open GoldilocksCorrectness.Record (GoldilocksModel Facts)
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks author)
open GoldilocksCorrectness.Statements.Routines (carries)
open Goldilocks (NamedObject RootOrder)
open Goldilocks.Sts (Setup)
open Framework.StsMultisetLog (SignedMsg)
open LARuns.GoldilocksInstance (RedeliveredAfterReleaseFromDelivery)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## 1. Goldilocks only broadcasts -/

/-- Every reaction of `variantProtocolOf M S` sends each of its objects to every validator
(Goldilocks's wiring).

Why: a tick's reaction broadcasts the objects of an `.ok` outcome of the model's tick, or sends
nothing; a delivery's broadcasts the model's relays (`variant_step_tick`, `variant_step_recv`).

The variables:
- `M`: the model; `S`: the setup. -/
theorem sendsToAll_variant (M : GoldilocksModel V) (S : Setup V) :
    SendsToAll (variantProtocolOf M S) := by
  intro p r s ev res h a ha
  cases ev with
  | tick =>
    rcases variant_step_tick h with ⟨q, -, rfl⟩ | rfl
    · obtain ⟨o, -, ho⟩ := List.mem_map.1 ha
      cases ho; rfl
    · cases ha
  | recv m =>
    rw [variant_step_recv h] at ha
    obtain ⟨o, -, ho⟩ := List.mem_map.1 ha
    cases ho; rfl
  | custom ev => exact ev.elim

/-! ## 2. `EnvFactsBy` -/

/-- **The environment's facts on the trace of a run of Goldilocks** (`EnvFactsBy`), at any deadline
function `deadline` of the trace at least the run's deadline function `dl` for the messages of the
class `ok`.

Why: field by field. The activity and clock fields are those of `GoldilocksVariant.Final.Instance`,
with `TickOncePerReadingG`, `ClockWithinSkew`, `ClockAdvancesWithin`, `TicksWithin`,
`ActsWithinSkewG` and the two bounds not negative; `other_sent` is `toTrace_other_sent`, with the
adversary's half of unforgeability on the run; `delivered` is `toTrace_delivered`, with the run's
delivery condition and the re-delivery condition `RedeliveredAfterReleaseFromDelivery` (Goldilocks
only broadcasts, `sendsToAll_variant`).

The variables:
- `F`: the model's facts; `π`: the run; `ΔClockAhead`, `ΔClockBehind`: the clock bounds; `dl`: the
  run's deadline function; `deadline`: the trace's; `release`: the release readings;
  `ΔRedeliver`: the re-delivery delay; `ok`: the class of messages; the conditions on the run, each
  named for the condition it is; `hdl`: the run's deadline is at most the trace's. -/
theorem envFactsBy_toTrace {M : GoldilocksModel V} {S : Setup V} (F : Facts M)
    (π : Exec (variantProtocolOf M S)) {ΔClockAhead ΔClockBehind : ℝ}
    {dl : (m : NamedObject V) → (tSend : ℝ) → ℝ}
    {deadline : (sm : SignedMsg V (NamedObject V)) → (a : ℝ) → Option ℝ}
    {release : (m : NamedObject V) → Option ℕ} {ΔRedeliver : ℕ} {ok : (m : NamedObject V) → Prop}
    (hAhead : 0 ≤ ΔClockAhead) (hBehind : 0 ≤ ΔClockBehind)
    (hOne : RStsVariant2.TickOncePerReadingG π)
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π)
    (hU : RStsVariant2.UnforgeableSends author carries π)
    (hD : RStsVariant2.DeliveredBeforeActingG RStsVariant2.TickStepG dl π)
    (hRe : RedeliveredAfterReleaseFromDelivery release (ΔRedeliver : ℝ) π)
    (hdl : ∀ (sm : SignedMsg V (NamedObject V)) (a d : ℝ), ok sm.msg →
      deadline sm a = some d → dl sm.msg a ≤ d) :
    EnvFactsBy (activityOf π) (toTrace (M.initial S.C) π) ΔClockAhead ΔClockBehind deadline
      release ΔRedeliver ok Vocab.goldilocks where
  time_div := toTrace_time_div (M.initial S.C) π
  corrupted_mono := activityOf_corrupted_mono π
  corrupted_keep := activityOf_corrupted_keep (M.initial S.C) π
  ahead_nonneg := hAhead
  behind_nonneg := hBehind
  tick_of_active :=
    toTrace_tick_of_active π (M.initial S.C) ΔClockAhead ΔClockBehind hAhead hBehind hSkew hAdv
      hTicks
  tick_active := toTrace_tick_active (M.initial S.C) π ΔClockAhead ΔClockBehind hSkew hActs
  tick_unique := toTrace_tick_unique (M.initial S.C) π hOne
  restart_crashed := activityOf_restart_crashed (M.initial S.C) π
  restart_time := toTrace_restart_time (M.initial S.C) π ΔClockAhead ΔClockBehind hSkew hActs
  clock_mono := toTrace_clock_mono (M.initial S.C) π
  restart_of_awake := activityOf_restart_of_awake (M.initial S.C) π
  deliver_active := activityOf_deliver_active (M.initial S.C) π
  other_sent := toTrace_other_sent F π hU
  delivered := toTrace_delivered (M.initial S.C) π hD hRe
    (fun i e he hs => recipients_of_sent_sub π (sendsToAll_variant M S) he hs) hdl

/-- `EnvFactsBy` at the trace's deadline `some (dl sm.msg a)`, the run's deadline itself.

The variables: as for `envFactsBy_toTrace`. -/
theorem envFactsBy_toTrace_some {M : GoldilocksModel V} {S : Setup V} (F : Facts M)
    (π : Exec (variantProtocolOf M S)) {ΔClockAhead ΔClockBehind : ℝ}
    {dl : (m : NamedObject V) → (tSend : ℝ) → ℝ}
    {release : (m : NamedObject V) → Option ℕ} {ΔRedeliver : ℕ} {ok : (m : NamedObject V) → Prop}
    (hAhead : 0 ≤ ΔClockAhead) (hBehind : 0 ≤ ΔClockBehind)
    (hOne : RStsVariant2.TickOncePerReadingG π)
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π)
    (hU : RStsVariant2.UnforgeableSends author carries π)
    (hD : RStsVariant2.DeliveredBeforeActingG RStsVariant2.TickStepG dl π)
    (hRe : RedeliveredAfterReleaseFromDelivery release (ΔRedeliver : ℝ) π) :
    EnvFactsBy (activityOf π) (toTrace (M.initial S.C) π) ΔClockAhead ΔClockBehind
      (fun sm a => some (dl sm.msg a)) release ΔRedeliver ok Vocab.goldilocks :=
  envFactsBy_toTrace F π hAhead hBehind hOne hSkew hAdv hTicks hActs hU hD hRe
    (fun _ _ _ _ h => le_of_eq (Option.some_injective _ h))

/-! ## 3. The two deadline shapes of the top statements -/

/-- **The synchronous delivery promise on the trace** (`EnvFactsDelivery`), at the trace's delay
`ΔNet` and time `GST`, from the run's synchronous deadline `syncDeadline tGST ΔDelay` with
`tGST ≤ GST` and `ΔDelay m ≤ ΔNet` for every message of the class `ok`.

The variables: as for `envFactsBy_toTrace`; `tGST`, `ΔDelay`: the run's deadline; `ΔNet`, `GST`:
the trace's; `htGST`, `hΔ`: the two relations. -/
theorem envFactsDelivery_toTrace {M : GoldilocksModel V} {S : Setup V} (F : Facts M)
    (π : Exec (variantProtocolOf M S)) {ΔClockAhead ΔClockBehind : ℝ} {tGST : ℝ}
    {ΔDelay : (m : NamedObject V) → ℝ} {ΔNet GST : ℕ}
    {release : (m : NamedObject V) → Option ℕ} {ΔRedeliver : ℕ} {ok : (m : NamedObject V) → Prop}
    (hAhead : 0 ≤ ΔClockAhead) (hBehind : 0 ≤ ΔClockBehind)
    (hOne : RStsVariant2.TickOncePerReadingG π)
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π)
    (hU : RStsVariant2.UnforgeableSends author carries π)
    (hD : RStsVariant2.DeliveredBeforeActingG RStsVariant2.TickStepG
      (RStsVariant2.syncDeadline tGST ΔDelay) π)
    (hRe : RedeliveredAfterReleaseFromDelivery release (ΔRedeliver : ℝ) π)
    (htGST : tGST ≤ GST) (hΔ : ∀ m : NamedObject V, ok m → ΔDelay m ≤ ΔNet) :
    EnvFactsDelivery (activityOf π) (toTrace (M.initial S.C) π) ΔClockAhead ΔClockBehind ΔNet
      ΔRedeliver GST release ok Vocab.goldilocks :=
  envFactsBy_toTrace F π hAhead hBehind hOne hSkew hAdv hTicks hActs hU hD hRe
    (syncDeadline_le_trace htGST hΔ)

/-- The run's deadline `deadlineOutside tGST ΔDelay tAsyncStart tAsyncEnd` is at most the trace's
`deadlineOutsideR ΔNet GST b₀ b₁` for every message of the class `ok`, when `tGST ≤ GST`,
`ΔDelay m ≤ ΔNet` for every such message, and the run's period `[tAsyncStart, tAsyncEnd)` lies
within the trace's `[b₀, b₁]`.

Why: a send whose ordinary run deadline is after the run's period start is due at the run's latest of
its time, `tAsyncEnd` and `tGST`, plus `ΔDelay m`, at most the trace's latest of its time, `b₁` and
`GST`, plus `ΔNet`, which is at least the trace's ordinary deadline; one whose ordinary run deadline
is at or before the start is due at it, at most the trace's ordinary deadline, which is at most
either case of the trace's. The trace's ordinary deadline is never at or before `b₀` when the run's
is after `tAsyncStart ≥ b₀`.

The variables:
- `tGST`, `ΔDelay`, `tAsyncStart`, `tAsyncEnd`: the run's deadline; `ΔNet`, `GST`, `b₀`, `b₁`:
  the trace's; `ok`: the class of messages; `htGST`, `hΔ`, `hb₀`, `hb₁`: the relations. -/
theorem deadlineOutside_le_trace {Msg : Type} {tGST tAsyncStart tAsyncEnd : ℝ}
    {ΔDelay : (m : Msg) → ℝ} {ΔNet GST b₀ b₁ : ℕ} {ok : (m : Msg) → Prop} (htGST : tGST ≤ GST)
    (hΔ : ∀ m : Msg, ok m → ΔDelay m ≤ ΔNet) (hb₀ : (b₀ : ℝ) ≤ tAsyncStart) (hb₁ : tAsyncEnd ≤ b₁) :
    ∀ (sm : SignedMsg V Msg) (a d : ℝ), ok sm.msg →
      (fun (_ : SignedMsg V Msg) (a : ℝ) => some (deadlineOutsideR ΔNet GST b₀ b₁ a)) sm a =
        some d →
      RStsVariant2.deadlineOutside tGST ΔDelay tAsyncStart tAsyncEnd sm.msg a ≤ d := by
  intro sm a d hok hd
  obtain rfl := Option.some_injective _ hd
  have hΔm := hΔ sm.msg hok
  have h1 : max a tGST ≤ max a (GST : ℝ) := max_le_max le_rfl htGST
  have h2 : max a (GST : ℝ) ≤ max a (max (b₁ : ℝ) GST) := max_le_max le_rfl (le_max_right _ _)
  have h3 : max a (max tAsyncEnd tGST) ≤ max a (max (b₁ : ℝ) GST) :=
    max_le_max le_rfl (max_le_max hb₁ htGST)
  unfold RStsVariant2.deadlineOutside deadlineOutsideR
  by_cases hr : max a tGST + ΔDelay sm.msg ≤ tAsyncStart
  · rw [if_pos hr]
    by_cases ht : max a (GST : ℝ) + ΔNet ≤ b₀
    · rw [if_pos ht]; linarith
    · rw [if_neg ht]; linarith
  · rw [if_neg hr]
    by_cases ht : max a (GST : ℝ) + ΔNet ≤ b₀
    · exact absurd (by linarith) hr
    · rw [if_neg ht]; linarith

/-- **The delivery promise suspended on an asynchronous period, on the trace**
(`EnvFactsDeliveryOutside`), at the trace's delay `ΔNet`, time `GST` and period `[b₀, b₁)`, from
the run's `deadlineOutside tGST ΔDelay tAsyncStart tAsyncEnd` with `tGST ≤ GST`, `ΔDelay m ≤ ΔNet`
for every message of the class `ok`, `b₀ ≤ tAsyncStart` and `tAsyncEnd ≤ b₁`.

The variables: as for `envFactsBy_toTrace`; `tGST`, `ΔDelay`, `tAsyncStart`, `tAsyncEnd`: the run's
deadline; `ΔNet`, `GST`, `b₀`, `b₁`: the trace's; `htGST`, `hΔ`, `hb₀`, `hb₁`: the relations. -/
theorem envFactsDeliveryOutside_toTrace {M : GoldilocksModel V} {S : Setup V} (F : Facts M)
    (π : Exec (variantProtocolOf M S)) {ΔClockAhead ΔClockBehind : ℝ}
    {tGST tAsyncStart tAsyncEnd : ℝ} {ΔDelay : (m : NamedObject V) → ℝ} {ΔNet GST b₀ b₁ : ℕ}
    {release : (m : NamedObject V) → Option ℕ} {ΔRedeliver : ℕ} {ok : (m : NamedObject V) → Prop}
    (hAhead : 0 ≤ ΔClockAhead) (hBehind : 0 ≤ ΔClockBehind)
    (hOne : RStsVariant2.TickOncePerReadingG π)
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π)
    (hU : RStsVariant2.UnforgeableSends author carries π)
    (hD : RStsVariant2.DeliveredBeforeActingG RStsVariant2.TickStepG
      (RStsVariant2.deadlineOutside tGST ΔDelay tAsyncStart tAsyncEnd) π)
    (hRe : RedeliveredAfterReleaseFromDelivery release (ΔRedeliver : ℝ) π)
    (htGST : tGST ≤ GST) (hΔ : ∀ m : NamedObject V, ok m → ΔDelay m ≤ ΔNet)
    (hb₀ : (b₀ : ℝ) ≤ tAsyncStart) (hb₁ : tAsyncEnd ≤ b₁) :
    EnvFactsDeliveryOutside (activityOf π) (toTrace (M.initial S.C) π) ΔClockAhead ΔClockBehind
      ΔNet ΔRedeliver GST release ok Vocab.goldilocks b₀ b₁ :=
  envFactsBy_toTrace F π hAhead hBehind hOne hSkew hAdv hTicks hActs hU hD hRe
    (deadlineOutside_le_trace htGST hΔ hb₀ hb₁)

/-! ## 4. The synchronous promises with the catch-up -/

/-- **The synchronous delivery promise and the catch-up after a restart, on the trace**
(`EnvFactsSync`), at the trace's delay `ΔNet`, catch-up delay `Δw` and time `GST`, from the run's
synchronous deadlines `syncDeadline tGST ΔDelay` from the sending and `syncDeadline tGST ΔCatchUp`
from the restart, with `tGST ≤ GST`, `ΔDelay m + ΔClockAhead ≤ ΔNet` and
`ΔCatchUp m + ΔClockAhead ≤ Δw` for every message of the class `ok`.

Why: `envFactsDelivery_toTrace`, and `caught_up` from `toTrace_caught_up` with the run's catch-up
condition (`syncDeadline_mono`, `syncCatchUp_ge_run`).

The variables: as for `envFactsBy_toTrace`; `tGST`, `ΔDelay`, `ΔCatchUp`: the run's deadlines;
`ΔNet`, `Δw`, `GST`: the trace's; `htGST`, `hΔ`, `hΔw`: the relations. -/
theorem envFactsSync_toTrace {M : GoldilocksModel V} {S : Setup V} (F : Facts M)
    (π : Exec (variantProtocolOf M S)) {ΔClockAhead ΔClockBehind : ℝ} {tGST : ℝ}
    {ΔDelay ΔCatchUp : (m : NamedObject V) → ℝ} {ΔNet Δw GST : ℕ}
    {release : (m : NamedObject V) → Option ℕ} {ΔRedeliver : ℕ} {ok : (m : NamedObject V) → Prop}
    (hAhead : 0 ≤ ΔClockAhead) (hBehind : 0 ≤ ΔClockBehind)
    (hOne : RStsVariant2.TickOncePerReadingG π)
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π)
    (hU : RStsVariant2.UnforgeableSends author carries π)
    (hD : RStsVariant2.DeliveredBeforeActingG RStsVariant2.TickStepG
      (RStsVariant2.syncDeadline tGST ΔDelay) π)
    (hC : RStsVariant2.CatchUpAfterRestartG RStsVariant2.TickStepG
      (RStsVariant2.syncDeadline tGST ΔDelay) (RStsVariant2.syncDeadline tGST ΔCatchUp) π)
    (hRe : RedeliveredAfterReleaseFromDelivery release (ΔRedeliver : ℝ) π)
    (htGST : tGST ≤ GST) (hΔ : ∀ m : NamedObject V, ok m → ΔDelay m + ΔClockAhead ≤ ΔNet)
    (hΔw : ∀ m : NamedObject V, ok m → ΔCatchUp m + ΔClockAhead ≤ Δw) :
    EnvFactsSync (activityOf π) (toTrace (M.initial S.C) π) ΔClockAhead ΔClockBehind ΔNet Δw
      ΔRedeliver GST release ok Vocab.goldilocks where
  toEnvFactsBy := envFactsDelivery_toTrace F π hAhead hBehind hOne hSkew hAdv hTicks hActs hU hD
    hRe htGST (fun m hm => by have := hΔ m hm; linarith)
  caught_up := toTrace_caught_up (M.initial S.C) π hC hRe
    (fun i e he hs => recipients_of_sent_sub π (sendsToAll_variant M S) he hs) hSkew
    (syncDeadline_mono tGST ΔCatchUp) (syncCatchUp_ge_run htGST hΔ hΔw)

/-! ## 5. No delivery promised, and the promises suspended on an asynchronous period -/

/-- **The environment's facts with no delivery promised, on the trace** (`EnvFactsBy` at the
deadline `fun _ _ => none`), for any release readings, re-delivery delay and class of messages: the
fields that read no delivery, from the conditions on the run that read no delivery. The field
`delivered` holds with nothing to deliver.

The variables: as for `envFactsBy_toTrace`. -/
theorem envFactsNoDelivery_toTrace {M : GoldilocksModel V} {S : Setup V} (F : Facts M)
    (π : Exec (variantProtocolOf M S)) {ΔClockAhead ΔClockBehind : ℝ}
    {release : (m : NamedObject V) → Option ℕ} {ΔRedeliver : ℕ} {ok : (m : NamedObject V) → Prop}
    (hAhead : 0 ≤ ΔClockAhead) (hBehind : 0 ≤ ΔClockBehind)
    (hOne : RStsVariant2.TickOncePerReadingG π)
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π)
    (hU : RStsVariant2.UnforgeableSends author carries π) :
    EnvFactsBy (activityOf π) (toTrace (M.initial S.C) π) ΔClockAhead ΔClockBehind
      (fun _ _ => none) release ΔRedeliver ok Vocab.goldilocks where
  time_div := toTrace_time_div (M.initial S.C) π
  corrupted_mono := activityOf_corrupted_mono π
  corrupted_keep := activityOf_corrupted_keep (M.initial S.C) π
  ahead_nonneg := hAhead
  behind_nonneg := hBehind
  tick_of_active :=
    toTrace_tick_of_active π (M.initial S.C) ΔClockAhead ΔClockBehind hAhead hBehind hSkew hAdv
      hTicks
  tick_active := toTrace_tick_active (M.initial S.C) π ΔClockAhead ΔClockBehind hSkew hActs
  tick_unique := toTrace_tick_unique (M.initial S.C) π hOne
  restart_crashed := activityOf_restart_crashed (M.initial S.C) π
  restart_time := toTrace_restart_time (M.initial S.C) π ΔClockAhead ΔClockBehind hSkew hActs
  clock_mono := toTrace_clock_mono (M.initial S.C) π
  restart_of_awake := activityOf_restart_of_awake (M.initial S.C) π
  deliver_active := activityOf_deliver_active (M.initial S.C) π
  other_sent := toTrace_other_sent F π hU
  delivered := by
    intro _ _ _ _ _ _ _ _ _ _ _ hd
    exact absurd hd (by simp)

/-- The run's deadline `deadlineOutside tGST ΔDelay tAsyncStart tAsyncEnd m a`, plus the clock-ahead
bound `ΔClockAhead`, is at most the trace's `deadlineOutsideR Δ GST b₀ b₁ a`, when
`ΔClockAhead ≥ 0`, `tGST ≤ GST`, `ΔDelay m + ΔClockAhead ≤ Δ`, and the run's period
`[tAsyncStart, tAsyncEnd)` lies within the trace's `[b₀, b₁]`.

Why: a send whose ordinary run deadline is at or before `tAsyncStart` is due at it, and the trace's
deadline is at least its ordinary deadline, at least that plus `ΔClockAhead`; any other send is due
at the run's latest of its time, `tAsyncEnd` and `tGST`, plus `ΔDelay m`, and the trace's ordinary
deadline is then after `b₀`, so the trace's deadline is its latest of the time, `b₁` and `GST`,
plus `Δ`.

The variables:
- `tGST`, `ΔDelay`, `tAsyncStart`, `tAsyncEnd`: the run's deadline; `Δ`, `GST`, `b₀`, `b₁`: the
  trace's; `ΔClockAhead`: the clock-ahead bound; `m`: the message; `a`: the real time counted from;
  `hAhead`, `htGST`, `hΔ`, `hb₀`, `hb₁`: the relations. -/
theorem deadlineOutside_add_le_trace {Msg : Type} {tGST tAsyncStart tAsyncEnd ΔClockAhead : ℝ}
    {ΔDelay : (m : Msg) → ℝ} {Δ GST b₀ b₁ : ℕ} {m : Msg} (a : ℝ) (hAhead : 0 ≤ ΔClockAhead)
    (htGST : tGST ≤ GST) (hΔ : ΔDelay m + ΔClockAhead ≤ Δ) (hb₀ : (b₀ : ℝ) ≤ tAsyncStart)
    (hb₁ : tAsyncEnd ≤ b₁) :
    RStsVariant2.deadlineOutside tGST ΔDelay tAsyncStart tAsyncEnd m a + ΔClockAhead ≤
      deadlineOutsideR Δ GST b₀ b₁ a := by
  have h1 : max a tGST ≤ max a (GST : ℝ) := max_le_max le_rfl htGST
  have h2 : max a (GST : ℝ) ≤ max a (max (b₁ : ℝ) GST) := max_le_max le_rfl (le_max_right _ _)
  have h3 : max a (max tAsyncEnd tGST) ≤ max a (max (b₁ : ℝ) GST) :=
    max_le_max le_rfl (max_le_max hb₁ htGST)
  unfold RStsVariant2.deadlineOutside deadlineOutsideR
  by_cases hr : max a tGST + ΔDelay m ≤ tAsyncStart
  · rw [if_pos hr]
    by_cases ht : max a (GST : ℝ) + Δ ≤ b₀
    · rw [if_pos ht]; linarith
    · rw [if_neg ht]; linarith
  · rw [if_neg hr]
    by_cases ht : max a (GST : ℝ) + Δ ≤ b₀
    · exact absurd (by linarith) hr
    · rw [if_neg ht]; linarith

/-- **The delivery promise and the catch-up after a restart, both suspended on an asynchronous
period, on the trace** (`EnvFactsOutside`), at the trace's delay `Δ`, catch-up delay `Δw`, time
`GST` and period `[b₀, b₁)`, from the run's `deadlineOutside tGST ΔDelay tAsyncStart tAsyncEnd`
from the sending and `deadlineOutside tGST ΔCatchUp tAsyncStart tAsyncEnd` from the restart, with
`tGST ≤ GST`, `ΔDelay m + ΔClockAhead ≤ Δ` and `ΔCatchUp m + ΔClockAhead ≤ Δw` for every message of
the class `ok`, `b₀ ≤ tAsyncStart` and `tAsyncEnd ≤ b₁`.

Why: `envFactsDeliveryOutside_toTrace`, and `caught_up` from `toTrace_caught_up` with the run's
catch-up condition (`deadlineOutside_mono`, `deadlineOutside_add_le_trace`).

The variables: as for `envFactsBy_toTrace`; `tGST`, `ΔDelay`, `ΔCatchUp`, `tAsyncStart`,
`tAsyncEnd`: the run's deadlines; `Δ`, `Δw`, `GST`, `b₀`, `b₁`: the trace's; `htGST`, `hΔ`, `hΔw`,
`hb₀`, `hb₁`: the relations. -/
theorem envFactsOutside_toTrace {M : GoldilocksModel V} {S : Setup V} (F : Facts M)
    (π : Exec (variantProtocolOf M S)) {ΔClockAhead ΔClockBehind : ℝ}
    {tGST tAsyncStart tAsyncEnd : ℝ} {ΔDelay ΔCatchUp : (m : NamedObject V) → ℝ}
    {Δ Δw GST b₀ b₁ : ℕ}
    {release : (m : NamedObject V) → Option ℕ} {ΔRedeliver : ℕ} {ok : (m : NamedObject V) → Prop}
    (hAhead : 0 ≤ ΔClockAhead) (hBehind : 0 ≤ ΔClockBehind)
    (hOne : RStsVariant2.TickOncePerReadingG π)
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π)
    (hU : RStsVariant2.UnforgeableSends author carries π)
    (hD : RStsVariant2.DeliveredBeforeActingG RStsVariant2.TickStepG
      (RStsVariant2.deadlineOutside tGST ΔDelay tAsyncStart tAsyncEnd) π)
    (hC : RStsVariant2.CatchUpAfterRestartG RStsVariant2.TickStepG
      (RStsVariant2.deadlineOutside tGST ΔDelay tAsyncStart tAsyncEnd)
      (RStsVariant2.deadlineOutside tGST ΔCatchUp tAsyncStart tAsyncEnd) π)
    (hRe : RedeliveredAfterReleaseFromDelivery release (ΔRedeliver : ℝ) π)
    (htGST : tGST ≤ GST) (hΔ : ∀ m : NamedObject V, ok m → ΔDelay m + ΔClockAhead ≤ Δ)
    (hΔw : ∀ m : NamedObject V, ok m → ΔCatchUp m + ΔClockAhead ≤ Δw)
    (hb₀ : (b₀ : ℝ) ≤ tAsyncStart) (hb₁ : tAsyncEnd ≤ b₁) :
    EnvFactsOutside (activityOf π) (toTrace (M.initial S.C) π) ΔClockAhead ΔClockBehind Δ Δw
      ΔRedeliver GST release ok Vocab.goldilocks b₀ b₁ where
  toEnvFactsBy := envFactsDeliveryOutside_toTrace F π hAhead hBehind hOne hSkew hAdv hTicks hActs
    hU hD hRe htGST (fun m hm => by have := hΔ m hm; linarith) hb₀ hb₁
  caught_up := toTrace_caught_up (M.initial S.C) π hC hRe
    (fun i e he hs => recipients_of_sent_sub π (sendsToAll_variant M S) he hs) hSkew
    (deadlineOutside_mono tGST ΔCatchUp tAsyncStart tAsyncEnd)
    (fun sm a t' c hok hc => by
      obtain rfl := Option.some_injective _ hc
      exact ⟨le_trans (deadlineOutside_add_le_trace a hAhead htGST (hΔ sm.msg hok) hb₀ hb₁)
          (le_max_left _ _),
        le_trans (deadlineOutside_add_le_trace t' hAhead htGST (hΔw sm.msg hok) hb₀ hb₁)
          (le_max_right _ _)⟩)

/-! ## 6. The release readings -/

/-- At the spec's model, the trace's release readings `releaseOf M S.C` are LARuns's
`goldilocksRelease S`, object by object: the start of the block's or the vote's slot, nothing for an
attestation.

The variables:
- `S`: the setup. -/
theorem releaseOf_goldilocks (S : Setup V) :
    GoldilocksCorrectness.Record.Statements.AbstractTrace.releaseOf
        (GoldilocksCorrectness.Record.Model.goldilocks (V := V)) S.C =
      LARuns.GoldilocksInstance.goldilocksRelease S := by
  funext o
  cases o <;> rfl

end GoldilocksVariant.Final
