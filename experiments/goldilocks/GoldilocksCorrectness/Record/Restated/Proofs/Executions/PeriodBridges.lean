module

public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# The asynchronous period's bridges, over a model

Five kit theorems over a model `M`, for the asynchrony induction: the trace premise `SynchronyFromWake` (or its bound up to `b`) beside the non-delivery facts of
any instance gives the delivery promise (or the one up to `b`); the delivery promise suspended on one
period gives the synchronous one from `max b₁ GST` on and the one up to `b₀`; and the sync fact
suspended on one period gives the sync fact from `max b₁ GST` on at the delay `max Δ Δs`. On its own
page so that the pages `AsyncDelivery.lean` imports are not rebuilt.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open GoldilocksCorrectness.Statements.Network

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Record.Statements.Executions

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)

section PeriodBridges

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy EnvFactsDelivery EnvFactsDeliveryUpTo
  EnvFactsDeliveryOutside SyncedWithin SyncedWithinOutside deadlineUpTo deadlineUpTo_eq_some
  deadlineOutside_le_after add_le_deadlineOutside)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} {Δ GST : ℕ}
  {ok : NamedObject V → Prop} {B : Type} {W : ViewVocab V B (NamedObject V)}

/-- The trace premise `SynchronyFromWake` at `Δ`, beside the non-delivery facts of any instance
`E`, gives the synchronous delivery promise, nothing promised to a validator that wakes.

Why: a delivery at a time less than the deadline `d` is before the receiver's tick to `d`, and the
receiver, active at `d`, ticks to it.

The variables:
- `M`: the model;
- `R`: the run's facts; `E`: the environment's facts, for their non-delivery fields; `hΔ`:
  `1 ≤ Δ`; `hs`: synchrony at `Δ` from `GST`.

Read aloud: the synchrony premise is the synchronous delivery promise. -/
theorem envFactsDelivery_of_trace (R : RunFacts M S x)
    {deadline : SignedMsg V (NamedObject V) → ℝ → Option ℝ}
    {ok' : NamedObject V → Prop}
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver ok' W) (hΔ : 1 ≤ Δ) (hs : x.SynchronyFromWake A Δ ΔRedeliver GST (releaseOf M S.C) ok) :
    EnvFactsDelivery A x ΔClockAhead ΔClockBehind Δ ΔRedeliver GST (releaseOf M S.C) ok W := by
  exact (envFactsBy_of_synchronyFromWakeBy M) x E hs

/-- The trace premise `SynchronyFromWakeUpTo` at `Δ` up to `b`, beside the non-delivery facts of
any instance `E`, gives the delivery promise up to `b`.

Why: as `envFactsDelivery_of_trace`, for the sends whose ordinary deadline is at most `b`.

The variables:
- `M`: the model;
- `R`: the run's facts; `E`: the environment's facts, for their non-delivery fields; `hΔ`:
  `1 ≤ Δ`; `hs`: synchrony at `Δ` from `GST` up to `b`.

Read aloud: the bounded synchrony premise is the bounded delivery promise. -/
theorem envFactsDeliveryUpTo_of_trace (R : RunFacts M S x)
    {deadline : SignedMsg V (NamedObject V) → ℝ → Option ℝ}
    {ok' : NamedObject V → Prop}
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver ok' W) (hΔ : 1 ≤ Δ) {b : ℕ}
    (hs : SynchronyFromWakeUpTo M A x Δ ΔRedeliver GST (releaseOf M S.C) ok b) :
    EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind Δ ΔRedeliver GST (releaseOf M S.C) ok W b := by
  exact (envFactsBy_of_synchronyFromWakeUpTo M) x E hs

/-- After the period `[b₀, b₁)`, the suspended delivery promise is the synchronous one from
`max b₁ GST` on.

The variables:
- `E`: the delivery promise suspended on `[b₀, b₁)`; `htime`: the time is monotone in the step.

Read aloud: once the period is over, the delivery promise is the one whose `GST` is `b₁`. -/
theorem envFactsDelivery_of_outside_after {b₀ b₁ : ℕ}
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsDeliveryOutside A x ΔClockAhead ΔClockBehind Δ ΔRedeliver GST release ok W b₀ b₁) (htime : Monotone x.time) :
    EnvFactsDelivery A x ΔClockAhead ΔClockBehind Δ ΔRedeliver (max b₁ GST) release ok W := by
  exact EnvFactsBy.of_le E fun _ a d' h => ⟨_, rfl, by
    have h' : max a (((max b₁ GST : ℕ)) : ℝ) + (Δ : ℝ) = d' := Option.some.inj h
    rw [← h', Nat.cast_max]
    exact GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR_le_after Δ GST b₀ b₁ a⟩

/-- Before the period `[b₀, b₁)`, the suspended delivery promise is the promise up to `b₀`.

The variables:
- `E`: the delivery promise suspended on `[b₀, b₁)`.

Read aloud: a send due by `b₀` is served as in the synchronous network. -/
theorem envFactsDeliveryUpTo_of_outside {b₀ b₁ : ℕ}
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsDeliveryOutside A x ΔClockAhead ΔClockBehind Δ ΔRedeliver GST release ok W b₀ b₁) :
    EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind Δ ΔRedeliver GST release ok W b₀ := by
  exact EnvFactsBy.restrict E fun _ _ _ h => by
    obtain ⟨h1, rfl⟩ := deadlineUpTo_eq_some.1 h
    rw [GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR_of_le h1]

end PeriodBridges

end GoldilocksCorrectness.Record.Proofs.Executions
