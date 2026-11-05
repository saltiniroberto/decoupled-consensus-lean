import GoldilocksVariant.Final.EnvFacts
import GoldilocksVariant.Final.RunFacts
import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HeldRelayedAc
import GoldilocksCorrectness.Record.Restated.Statements.Executions.AsyncDeliveryStatements

/-!
# The sync fact on the projection of a run of Goldilocks

For a run `π` of `variantProtocolOf M S`, read as the trace `toTrace (M.initial S.C) π` with the
activity `activityOf π`, the sync fact at the minimal selection `servesMin M S.C`, for the blocks and
the Goldfish votes (`acObject`) and for the attestations (`fgObject`), at the two deadline shapes the
top statements take: synchronous from `GST` on (`SyncedWithin`) and suspended on one asynchronous
period `[b₀, b₁)` (`SyncedWithinOutside`). Each comes from the pushed catch-up on the trace
(`syncedWithin_servesMin_of_envFactsSync`, `syncedWithinOutside_of_envFactsOutside`), fed the trace's
`RunFacts` (`runFacts_toTrace`), its environment's facts (`envFactsSync_toTrace`,
`envFactsOutside_toTrace`) and the relay fact on the trace:

- `toTrace_relay_ac`, `toTrace_relay_fg`: an object of the class that an honest validator serves at
  its clock value after a step `k` was put on the wire by that validator, honest then, at a step
  `i < k` after which it already served it at its clock value then;
- `syncedWithin_toTrace`, `syncedWithin_F_toTrace`: the synchronous sync fact;
- `syncedWithinOutside_toTrace`, `syncedWithinOutside_F_toTrace`: the sync fact suspended on an
  asynchronous period.

Each takes the conditions on the run its pieces use and the relations between the run's delays and
the trace's.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GoldilocksVariant.Final

open RStsVariant2 (Exec)
open GoldilocksCorrectness.Statements.AbstractTrace (Trace Activity SyncedWithin SyncedWithinOutside)
open GoldilocksCorrectness.Record (GoldilocksModel Facts UniformSchedule)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin releaseOf)
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks author acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (carries)
open Goldilocks (NamedObject RootOrder)
open Goldilocks.Sts (Setup)
open LARuns.GoldilocksInstance (RedeliveredAfterReleaseFromDelivery)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## 1. The relay fact on the trace -/

/-- **What an honest validator serves of the blocks and Goldfish votes, it put on the wire itself,
on the trace of a run of Goldilocks.** A block or a Goldfish vote that `u`, outside the adversary set
at step `k` of the trace, serves by `servesMin M S.C` at its clock value after `k` steps was put on
the wire by `u`, honest then, at a step `i < k` after which `u` already served it at its clock value.

Why: `servesMin_relayed_ac` on the trace, with its `RunFacts` (`runFacts_toTrace`) and its
environment's facts with no delivery promised (`envFactsNoDelivery_toTrace`), gives the step `i`
and `u` serving the object at `k`'s clock value after `i`; `u`'s clock value after `i + 1` steps is
at most the one after `k` (`clockValue_mono`), and a node serves at a smaller clock value what it
serves at a larger one (`servesMin_of_le_clockValue`).

The variables:
- `F`: the model's facts; `U`: its slot layout is uniform; `π`: the run; the conditions on the run,
  each named for the condition it is. -/
theorem toTrace_relay_ac {M : GoldilocksModel V} {S : Setup V} (F : Facts M)
    (U : UniformSchedule M.toSlotLayout) (π : Exec (variantProtocolOf M S))
    {ΔClockAhead ΔClockBehind : ℝ}
    (hAhead : 0 ≤ ΔClockAhead) (hBehind : 0 ≤ ΔClockBehind)
    (hOne : RStsVariant2.TickOncePerReadingG π)
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π)
    (hU : RStsVariant2.UnforgeableSends author carries π) :
    ∀ (k : ℕ) (u : V) (o : NamedObject V), acObject o →
      u ∉ (activityOf π).corrupted k →
      servesMin M S.C ((toTrace (M.initial S.C) π).st k u)
        ((toTrace (M.initial S.C) π).clockValue k u) o →
      ∃ i : ℕ, i < k ∧ (toTrace (M.initial S.C) π).HonestSendAt (activityOf π) i ⟨u, o⟩ ∧
        servesMin M S.C ((toTrace (M.initial S.C) π).st (i + 1) u)
          ((toTrace (M.initial S.C) π).clockValue (i + 1) u) o := by
  intro k u o hok hu hh
  have R := runFacts_toTrace F π
  have E := envFactsNoDelivery_toTrace F π (release := fun _ => none) (ΔRedeliver := 0)
    (ok := acObject) hAhead hBehind hOne hSkew hAdv hTicks hActs hU
  obtain ⟨i, hik, hs, hin⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Executions.servesMin_relayed_ac M F U) _ R E k u o _ hok
      hu hh
  exact ⟨i, hik, hs,
    (GoldilocksCorrectness.Record.Proofs.Executions.servesMin_of_le_clockValue M F) S
      (E.clockValue_mono (Nat.succ_le_of_lt hik) hu) hin⟩

/-- **What an honest validator serves of the attestations, it put on the wire itself, on the trace
of a run of Goldilocks.** An attestation that `u`, outside the adversary set at step `k` of the
trace, serves by `servesMin M S.C` at its clock value after `k` steps was put on the wire by `u`,
honest then, at a step `i < k` after which `u` already served it at its clock value.

Why: `servesMin_relayed_fg` on the trace, with its `RunFacts` and its environment's facts with no
delivery promised; the minimal selection serves an attestation at every clock value once at one
(`servesMin_attest_clock`).

The variables: as for `toTrace_relay_ac`, without `U`. -/
theorem toTrace_relay_fg {M : GoldilocksModel V} {S : Setup V} (F : Facts M)
    (π : Exec (variantProtocolOf M S))
    {ΔClockAhead ΔClockBehind : ℝ}
    (hAhead : 0 ≤ ΔClockAhead) (hBehind : 0 ≤ ΔClockBehind)
    (hOne : RStsVariant2.TickOncePerReadingG π)
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π)
    (hU : RStsVariant2.UnforgeableSends author carries π) :
    ∀ (k : ℕ) (u : V) (o : NamedObject V), fgObject o →
      u ∉ (activityOf π).corrupted k →
      servesMin M S.C ((toTrace (M.initial S.C) π).st k u)
        ((toTrace (M.initial S.C) π).clockValue k u) o →
      ∃ i : ℕ, i < k ∧ (toTrace (M.initial S.C) π).HonestSendAt (activityOf π) i ⟨u, o⟩ ∧
        servesMin M S.C ((toTrace (M.initial S.C) π).st (i + 1) u)
          ((toTrace (M.initial S.C) π).clockValue (i + 1) u) o := by
  intro k u o hok hu hh
  have R := runFacts_toTrace F π
  have E := envFactsNoDelivery_toTrace F π (release := fun _ => none) (ΔRedeliver := 0)
    (ok := acObject) hAhead hBehind hOne hSkew hAdv hTicks hActs hU
  obtain ⟨i, hik, hs, hin⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Executions.servesMin_relayed_fg M F) _ R E k u o _ hok
      hu hh
  exact ⟨i, hik, hs,
    (GoldilocksCorrectness.Record.Proofs.Executions.servesMin_attest_clock M F) hok hin⟩

/-! ## 2. The synchronous sync fact -/

/-- **The sync fact for the blocks and Goldfish votes on the trace of a run of Goldilocks**
(`SyncedWithin` at `servesMin M S.C` and `acObject`, sync delay `Δs`, time `GST`), from the run's
synchronous deadlines `syncDeadline tGST ΔDelay` from the sending and `syncDeadline tGST ΔCatchUp`
from a restart, with `tGST ≤ GST`, `ΔDelay m + ΔClockAhead ≤ Δ` and
`ΔCatchUp m + ΔClockAhead ≤ Δw` for every block and Goldfish vote, `Δ + ΔClockAhead ≤ Δs` and
`max Δ Δw ≤ Δs`.

Why: `syncedWithin_servesMin_of_envFactsSync` with the trace's `RunFacts` (`runFacts_toTrace`), its
synchronous promises with the catch-up (`envFactsSync_toTrace`) and the relay fact
(`toTrace_relay_ac`).

The variables:
- `F`, `U`, `π`, the conditions on the run: as for `toTrace_relay_ac`; `hD`, `hC`, `hRe`:
  the run's delivery, catch-up and re-delivery conditions; `tGST`, `ΔDelay`, `ΔCatchUp`: the run's
  deadlines; `Δ`, `Δw`, `GST`: the trace's delay, catch-up delay and time; `Δs`: the sync delay;
  `ΔRedeliver`: the re-delivery delay; `htGST`, `hΔ`, `hΔw`, `hΔA`, `hΔs`: the relations. -/
theorem syncedWithin_toTrace {M : GoldilocksModel V} {S : Setup V} (F : Facts M)
    (U : UniformSchedule M.toSlotLayout) (π : Exec (variantProtocolOf M S))
    {ΔClockAhead ΔClockBehind : ℝ} {tGST : ℝ}
    {ΔDelay ΔCatchUp : (m : NamedObject V) → ℝ} {Δ Δw GST Δs ΔRedeliver : ℕ}
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
    (hRe : RedeliveredAfterReleaseFromDelivery (releaseOf M S.C) (ΔRedeliver : ℝ) π)
    (htGST : tGST ≤ GST)
    (hΔ : ∀ m : NamedObject V, acObject m → ΔDelay m + ΔClockAhead ≤ Δ)
    (hΔw : ∀ m : NamedObject V, acObject m → ΔCatchUp m + ΔClockAhead ≤ Δw)
    (hΔA : (Δ : ℝ) + ΔClockAhead ≤ Δs) (hΔs : max Δ Δw ≤ Δs) :
    SyncedWithin (activityOf π) (toTrace (M.initial S.C) π) (servesMin M S.C) acObject
      (releaseOf M S.C) ΔRedeliver Δs GST :=
  GoldilocksCorrectness.Record.Statements.Executions.syncedWithin_servesMin_of_envFactsSync
    (runFacts_toTrace F π)
    (envFactsSync_toTrace F π hAhead hBehind hOne hSkew hAdv hTicks hActs hU hD hC hRe htGST hΔ
      hΔw)
    hΔA hΔs
    (toTrace_relay_ac F U π hAhead hBehind hOne hSkew hAdv hTicks hActs hU)

/-- **The sync fact for the attestations on the trace of a run of Goldilocks** (`SyncedWithin` at
`servesMin M S.C` and `fgObject`, sync delay `Δs_F`, time `GST`), from the run's synchronous
deadlines, with `tGST ≤ GST`, `ΔDelay m + ΔClockAhead ≤ Δ_F` and
`ΔCatchUp m + ΔClockAhead ≤ Δw_F` for every attestation, `Δ_F + ΔClockAhead ≤ Δs_F` and
`max Δ_F Δw_F ≤ Δs_F`.

Why: `syncedWithin_servesMin_of_envFactsSync` with the trace's `RunFacts`, its synchronous promises
with the catch-up at `fgObject` and the relay fact (`toTrace_relay_fg`).

The variables: as for `syncedWithin_toTrace`, at the attestations' delays `Δ_F`, `Δw_F`, `Δs_F`,
without `U`. -/
theorem syncedWithin_F_toTrace {M : GoldilocksModel V} {S : Setup V} (F : Facts M)
    (π : Exec (variantProtocolOf M S))
    {ΔClockAhead ΔClockBehind : ℝ} {tGST : ℝ}
    {ΔDelay ΔCatchUp : (m : NamedObject V) → ℝ} {Δ_F Δw_F GST Δs_F ΔRedeliver : ℕ}
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
    (hRe : RedeliveredAfterReleaseFromDelivery (releaseOf M S.C) (ΔRedeliver : ℝ) π)
    (htGST : tGST ≤ GST)
    (hΔ : ∀ m : NamedObject V, fgObject m → ΔDelay m + ΔClockAhead ≤ Δ_F)
    (hΔw : ∀ m : NamedObject V, fgObject m → ΔCatchUp m + ΔClockAhead ≤ Δw_F)
    (hΔA : (Δ_F : ℝ) + ΔClockAhead ≤ Δs_F) (hΔs : max Δ_F Δw_F ≤ Δs_F) :
    SyncedWithin (activityOf π) (toTrace (M.initial S.C) π) (servesMin M S.C) fgObject
      (releaseOf M S.C) ΔRedeliver Δs_F GST :=
  GoldilocksCorrectness.Record.Statements.Executions.syncedWithin_servesMin_of_envFactsSync
    (runFacts_toTrace F π)
    (envFactsSync_toTrace F π hAhead hBehind hOne hSkew hAdv hTicks hActs hU hD hC hRe htGST hΔ
      hΔw)
    hΔA hΔs
    (toTrace_relay_fg F π hAhead hBehind hOne hSkew hAdv hTicks hActs hU)

/-! ## 3. The sync fact suspended on an asynchronous period -/

/-- **The sync fact for the blocks and Goldfish votes, suspended on an asynchronous period, on the
trace of a run of Goldilocks** (`SyncedWithinOutside` at `servesMin M S.C` and `acObject`, sync
delay `Δs`, time `GST`, period `[b₀, b₁)`), from the run's deadlines
`deadlineOutside tGST ΔDelay tAsyncStart tAsyncEnd` from the sending and
`deadlineOutside tGST ΔCatchUp tAsyncStart tAsyncEnd` from a restart, with `tGST ≤ GST`,
`ΔDelay m + ΔClockAhead ≤ Δ` and `ΔCatchUp m + ΔClockAhead ≤ Δw` for every block and Goldfish vote,
`b₀ ≤ tAsyncStart`, `tAsyncEnd ≤ b₁`, `Δ + ΔClockAhead ≤ Δs` and `max Δ Δw ≤ Δs`.

Why: `syncedWithinOutside_of_envFactsOutside` with the trace's `RunFacts`, its promises suspended on
`[b₀, b₁)` (`envFactsOutside_toTrace`) and the relay fact (`toTrace_relay_ac`).

The variables: as for `syncedWithin_toTrace`; `tAsyncStart`, `tAsyncEnd`: the run's asynchronous
period; `b₀`, `b₁`: the trace's; `hb₀`, `hb₁`: the relations. -/
theorem syncedWithinOutside_toTrace {M : GoldilocksModel V} {S : Setup V} (F : Facts M)
    (U : UniformSchedule M.toSlotLayout) (π : Exec (variantProtocolOf M S))
    {ΔClockAhead ΔClockBehind : ℝ} {tGST tAsyncStart tAsyncEnd : ℝ}
    {ΔDelay ΔCatchUp : (m : NamedObject V) → ℝ} {Δ Δw GST Δs ΔRedeliver b₀ b₁ : ℕ}
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
    (hRe : RedeliveredAfterReleaseFromDelivery (releaseOf M S.C) (ΔRedeliver : ℝ) π)
    (htGST : tGST ≤ GST)
    (hΔ : ∀ m : NamedObject V, acObject m → ΔDelay m + ΔClockAhead ≤ Δ)
    (hΔw : ∀ m : NamedObject V, acObject m → ΔCatchUp m + ΔClockAhead ≤ Δw)
    (hb₀ : (b₀ : ℝ) ≤ tAsyncStart) (hb₁ : tAsyncEnd ≤ b₁)
    (hΔA : (Δ : ℝ) + ΔClockAhead ≤ Δs) (hΔs : max Δ Δw ≤ Δs) :
    SyncedWithinOutside (activityOf π) (toTrace (M.initial S.C) π) (servesMin M S.C) acObject
      (releaseOf M S.C) ΔRedeliver Δs GST b₀ b₁ :=
  GoldilocksCorrectness.Record.Statements.Executions.syncedWithinOutside_of_envFactsOutside
    (runFacts_toTrace F π)
    (envFactsOutside_toTrace F π hAhead hBehind hOne hSkew hAdv hTicks hActs hU hD hC hRe htGST hΔ
      hΔw hb₀ hb₁)
    hΔA hΔs
    (toTrace_relay_ac F U π hAhead hBehind hOne hSkew hAdv hTicks hActs hU)

/-- **The sync fact for the attestations, suspended on an asynchronous period, on the trace of a
run of Goldilocks** (`SyncedWithinOutside` at `servesMin M S.C` and `fgObject`, sync delay `Δs_F`,
time `GST`, period `[b₀, b₁)`), from the run's suspended deadlines, with `tGST ≤ GST`,
`ΔDelay m + ΔClockAhead ≤ Δ_F` and `ΔCatchUp m + ΔClockAhead ≤ Δw_F` for every attestation,
`b₀ ≤ tAsyncStart`, `tAsyncEnd ≤ b₁`, `Δ_F + ΔClockAhead ≤ Δs_F` and `max Δ_F Δw_F ≤ Δs_F`.

Why: `syncedWithinOutside_of_envFactsOutside` with the trace's `RunFacts`, its promises suspended on
`[b₀, b₁)` at `fgObject` and the relay fact (`toTrace_relay_fg`).

The variables: as for `syncedWithinOutside_toTrace`, at the attestations' delays `Δ_F`, `Δw_F`,
`Δs_F`, without `U`. -/
theorem syncedWithinOutside_F_toTrace {M : GoldilocksModel V} {S : Setup V} (F : Facts M)
    (π : Exec (variantProtocolOf M S))
    {ΔClockAhead ΔClockBehind : ℝ} {tGST tAsyncStart tAsyncEnd : ℝ}
    {ΔDelay ΔCatchUp : (m : NamedObject V) → ℝ} {Δ_F Δw_F GST Δs_F ΔRedeliver b₀ b₁ : ℕ}
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
    (hRe : RedeliveredAfterReleaseFromDelivery (releaseOf M S.C) (ΔRedeliver : ℝ) π)
    (htGST : tGST ≤ GST)
    (hΔ : ∀ m : NamedObject V, fgObject m → ΔDelay m + ΔClockAhead ≤ Δ_F)
    (hΔw : ∀ m : NamedObject V, fgObject m → ΔCatchUp m + ΔClockAhead ≤ Δw_F)
    (hb₀ : (b₀ : ℝ) ≤ tAsyncStart) (hb₁ : tAsyncEnd ≤ b₁)
    (hΔA : (Δ_F : ℝ) + ΔClockAhead ≤ Δs_F) (hΔs : max Δ_F Δw_F ≤ Δs_F) :
    SyncedWithinOutside (activityOf π) (toTrace (M.initial S.C) π) (servesMin M S.C) fgObject
      (releaseOf M S.C) ΔRedeliver Δs_F GST b₀ b₁ :=
  GoldilocksCorrectness.Record.Statements.Executions.syncedWithinOutside_of_envFactsOutside
    (runFacts_toTrace F π)
    (envFactsOutside_toTrace F π hAhead hBehind hOne hSkew hAdv hTicks hActs hU hD hC hRe htGST hΔ
      hΔw hb₀ hb₁)
    hΔA hΔs
    (toTrace_relay_fg F π hAhead hBehind hOne hSkew hAdv hTicks hActs hU)

end GoldilocksVariant.Final
