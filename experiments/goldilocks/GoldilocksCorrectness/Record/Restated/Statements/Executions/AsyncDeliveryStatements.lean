module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# AsyncDeliveryStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/AsyncDeliveryStatements.lean` over a
model `M`, for an execution `x` of `protocolOf M S`, proved in
`Record/Restated/Proofs/Executions/AsyncDelivery.lean`, and the environment's promises up to a bound
and suspended on one period giving the delivery premises (in the namespaces of `EnvFactsUpTo` and
`EnvFactsOutside`); and the pushed catch-up giving the sync fact at `max Δ Δw`, for any selection
whose objects every honest holder put on the wire itself once it served them
(`syncedWithin_of_envFactsSync`, its bounded and suspended forms, and its form at the minimal
selection `servesMin`). `deadlineOutside_le` names no
member and reads no execution; the twins read the landed one.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

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

/-- **`SynchronyFromWake` is the deadline form at the ordinary deadline.** `SynchronyFromWake` is
`SynchronyFromWakeBy` at the deadline `max t GST + Δ`.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Δ`: the delay; `GST`: the time
  from which the network is synchronous; `ok`: the object class.

Read aloud: synchrony is the deadline form at the ordinary deadline. -/
theorem synchronyFromWake_iff_by (Δ GST : ℕ) (ok : NamedObject V → Prop) {release ΔRedeliver} :
    x.SynchronyFromWake A Δ ΔRedeliver GST release ok ↔
      x.SynchronyFromWakeBy A (fun t => max t GST + Δ) release ΔRedeliver ok :=
  (GoldilocksCorrectness.Record.Proofs.Executions.synchronyFromWake_iff_by M) A x Δ GST ok

/-- **`CatchUpOnWake` is the deadline form at the ordinary deadline.** `CatchUpOnWake` is
`CatchUpOnWakeBy` at the deadline `max t GST + Δ`.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Δ`: the delay; `GST`: the time
  from which the network is synchronous; `ok`: the object class; `release`, `ΔRedeliver`: the
  release clock value of an object and the re-delivery delay.

Read aloud: catch-up on wake is the deadline form at the ordinary deadline. -/
theorem catchUpOnWake_iff_by (Δ GST : ℕ) (ok : NamedObject V → Prop) {release ΔRedeliver} :
    x.CatchUpOnWake A Δ ΔRedeliver GST release ok ↔
      x.CatchUpOnWakeBy A (fun t => max t GST + Δ) release ΔRedeliver ok :=
  (GoldilocksCorrectness.Record.Proofs.Executions.catchUpOnWake_iff_by M) A x Δ GST ok

end Delivery

section DeliveryFacts

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} {Δ GST : ℕ}
  {ok : NamedObject V → Prop}

/-- **A bound on the deadlines can be lowered.** Synchrony up to `b'` gives synchrony up to every
`b ≤ b'`.

The variables:
- `M`: the model;
- `b`, `b'`: the two bounds; `hle`: `b ≤ b'`; `h`: synchrony up to `b'`.

Read aloud: whatever is delivered for the sends due by `b'` is delivered for those due by `b`. -/
theorem SynchronyFromWakeUpTo.mono {b b' : ℕ} (hle : b ≤ b')
    {release ΔRedeliver} (h : SynchronyFromWakeUpTo M A x Δ ΔRedeliver GST release ok b') : SynchronyFromWakeUpTo M A x Δ ΔRedeliver GST release ok b :=
  (GoldilocksCorrectness.Record.Proofs.Executions.SynchronyFromWakeUpTo.mono M) hle h

/-- **A bound on the deadlines can be lowered.** Catch-up on wake up to `b'` gives catch-up on
wake up to every `b ≤ b'`.

The variables:
- `M`: the model;
- `b`, `b'`: the two bounds; `hle`: `b ≤ b'`; `h`: catch-up on wake up to `b'`.

Read aloud: a wake that catches up when due by `b'` catches up when due by `b`. -/
theorem CatchUpOnWakeUpTo.mono {Δw b b' : ℕ} (hle : b ≤ b') {release ΔRedeliver}
    (h : CatchUpOnWakeUpTo M A x Δ Δw ΔRedeliver GST release ok b') :
    CatchUpOnWakeUpTo M A x Δ Δw ΔRedeliver GST release ok b :=
  (GoldilocksCorrectness.Record.Proofs.Executions.CatchUpOnWakeUpTo.mono M) hle h

/-- **Synchrony gives every bounded synchrony.** `SynchronyFromWake` gives
`SynchronyFromWakeUpTo` at every bound `b`.

The variables:
- `M`: the model;
- `b`: the bound; `h`: synchrony.

Read aloud: the premise gives every bounded one. -/
theorem synchronyFromWakeUpTo_of_synchronyFromWake (b : ℕ)
    {release ΔRedeliver} (h : x.SynchronyFromWake A Δ ΔRedeliver GST release ok) : SynchronyFromWakeUpTo M A x Δ ΔRedeliver GST release ok b :=
  (GoldilocksCorrectness.Record.Proofs.Executions.synchronyFromWakeUpTo_of_synchronyFromWake M) b h

/-- **Before the period, the suspended synchrony is the bounded one.** Synchrony suspended on
`[b₀, b₁)` gives synchrony up to `b₀`.

Why: a send due by `b₀` has `deadlineOutside Δ GST b₀ b₁` equal to its ordinary deadline.

The variables:
- `M`: the model;
- `b₀`, `b₁`: the start and the end of the period; `h`: synchrony suspended on `[b₀, b₁)`.

Read aloud: a send due by `b₀` is delivered as in the synchronous network. -/
theorem synchronyFromWakeUpTo_of_outside {b₀ b₁ : ℕ}
    {release ΔRedeliver} (h : x.SynchronyFromWakeOutside A Δ ΔRedeliver GST release ok b₀ b₁) :
    SynchronyFromWakeUpTo M A x Δ ΔRedeliver GST release ok b₀ :=
  (GoldilocksCorrectness.Record.Proofs.Executions.synchronyFromWakeUpTo_of_outside M) h

/-- **After the period, synchrony holds with `GST` moved to `max b₁ GST`.** Synchrony suspended
on `[b₀, b₁)` gives `SynchronyFromWake` at `max b₁ GST`: every send is delivered within `Δ` of
the latest of its time, `b₁` and `GST`. No hypothesis `b₀ ≤ b₁` is needed.

Why: `deadlineOutside Δ GST b₀ b₁ t ≤ max t (max b₁ GST) + Δ`, so a receiver awake and honest
through the later deadline is so through the earlier one.

The variables:
- `M`: the model;
- `b₀`, `b₁`: the start and the end of the period; `h`: synchrony suspended on `[b₀, b₁)`.

Read aloud: once the period is over, the network is the ordinary synchronous network whose `GST`
is `b₁`. -/
theorem synchronyFromWake_of_outside_after {b₀ b₁ : ℕ}
    {release ΔRedeliver} (h : x.SynchronyFromWakeOutside A Δ ΔRedeliver GST release ok b₀ b₁) :
    x.SynchronyFromWake A Δ ΔRedeliver (max b₁ GST) release ok :=
  (GoldilocksCorrectness.Record.Proofs.Executions.synchronyFromWake_of_outside_after M) h

/-- **After the period, catch-up on wake holds with `GST` moved to `max b₁ GST`.** Catch-up on
wake suspended on `[b₀, b₁)` gives `CatchUpOnWake` at `max b₁ GST`.

Why: as for synchrony, from `deadlineOutside_le`.

The variables:
- `M`: the model;
- `b₀`, `b₁`: the start and the end of the period; `h`: catch-up on wake suspended on `[b₀, b₁)`.

Read aloud: once the period is over, a waking validator catches up as in the ordinary synchronous
network whose `GST` is `b₁`. -/
theorem catchUpOnWake_of_outside_after {b₀ b₁ : ℕ} {release ΔRedeliver}
    (h : x.CatchUpOnWakeOutside A Δ ΔRedeliver GST release ok b₀ b₁) :
    x.CatchUpOnWake A Δ ΔRedeliver (max b₁ GST) release ok :=
  (GoldilocksCorrectness.Record.Proofs.Executions.catchUpOnWake_of_outside_after M) h

end DeliveryFacts

end GoldilocksCorrectness.Record.Statements.Executions

/-! ## The environment's promises give the delivery premises

Stated in the namespaces of `EnvFactsUpTo` and `EnvFactsOutside`, so that a statement holding
`E : EnvFactsUpTo …` writes `E.synchronyFromWakeUpTo hΔ R`. -/

namespace GoldilocksCorrectness.Statements.AbstractTrace
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Record (GoldilocksModel)
open GoldilocksCorrectness.Record.Statements.Executions (SynchronyFromWakeUpTo CatchUpOnWakeUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Network (ViewVocab)
open Framework.StsMultisetLog (SignedMsg)
open Goldilocks (NamedObject RootOrder)
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder] {M : GoldilocksModel V}
  {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} {Δ Δw GST : ℕ}
  {ok : NamedObject V → Prop} {B : Type} {W : ViewVocab V B (NamedObject V)}

/-- **The delivery promise up to `b` gives the bounded synchrony premise.** On a wake-shaped trace,
for a delay `Δ ≥ 1`, the delivery promise at the deadline `deadlineUpTo Δ GST b`, with any catch-up
promise (`EnvFactsUpTo … b`, `EnvFactsDeliveryUpTo … b`), gives
`SynchronyFromWakeUpTo M A x Δ GST ok b`.

Why: the step bound of `EnvFactsBy.delivered` gives back the time bound, since the receiver is
awake one time before the deadline and so does not wake at it.

The variables:
- `hΔ`: `1 ≤ Δ`; `R`: the run's facts; `E`: the promises up to
  `b`.

Read aloud: the bounded promises give the bounded synchrony premise. -/
theorem EnvFactsUpTo.synchronyFromWakeUpTo (hΔ : 1 ≤ Δ)
    (R : RunFacts M S x) {b : ℕ}
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind (fun _ a => deadlineUpTo Δ GST b a) (releaseOf M S.C) ΔRedeliver ok W) :
    SynchronyFromWakeUpTo M A x Δ ΔRedeliver GST (releaseOf M S.C) ok b :=
  (GoldilocksCorrectness.Record.Proofs.Executions.envFactsUpTo_synchronyFromWakeUpTo M) R hΔ E

/-- **The suspended delivery promise gives the suspended synchrony premise.** On a wake-shaped
trace, for a delay `Δ ≥ 1`, the delivery promise suspended on `[b₀, b₁)`, with any catch-up promise
(`EnvFactsOutside … b₀ b₁`, `EnvFactsDeliveryOutside … b₀ b₁`), gives
`x.SynchronyFromWakeOutside A Δ GST ok b₀ b₁`.

The variables:
- `hΔ`: `1 ≤ Δ`; `R`: the run's facts; `E`: the promises
  suspended on `[b₀, b₁)`.

Read aloud: the suspended promises give the suspended synchrony premise. -/
theorem EnvFactsOutside.synchronyFromWakeOutside (hΔ : 1 ≤ Δ)
    (R : RunFacts M S x) {b₀ b₁ : ℕ}
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind (fun _ a => some (GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR Δ GST b₀ b₁ a)) (releaseOf M S.C) ΔRedeliver ok W) :
    x.SynchronyFromWakeOutside A Δ ΔRedeliver GST (releaseOf M S.C) ok b₀ b₁ :=
  (GoldilocksCorrectness.Record.Proofs.Executions.envFactsOutside_synchronyFromWakeOutside M)
    R hΔ E

/-- **The suspended promises give the suspended catch-up premise, at the larger delay.** On a
wake-shaped trace, for a delay `Δ ≥ 1`, `EnvFactsOutside … b₀ b₁` gives
`x.CatchUpOnWakeOutside A (max Δ Δw) ΔRedeliver GST (releaseOf M S.C) ok b₀ b₁`.

Why: a validator entering the active set at `t` wakes at a step at `t`, and its catch-up deadline,
the later of the message's and the wake's, is at most `deadlineOutside (max Δ Δw) GST b₀ b₁ t`.

The variables:
- `hΔ`: `1 ≤ Δ`; `R`: the run's facts; `E`: the promises
  suspended on `[b₀, b₁)`.

Read aloud: the suspended promises give the suspended catch-up premise, at the larger of the delay
and the catch-up delay. -/
theorem EnvFactsOutside.catchUpOnWakeOutside (hΔ : 1 ≤ Δ)
    (R : RunFacts M S x) {b₀ b₁ : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsOutside A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver GST (releaseOf M S.C) ok W b₀ b₁) :
    x.CatchUpOnWakeOutside A (max Δ Δw) ΔRedeliver GST (releaseOf M S.C) ok b₀ b₁ :=
  (GoldilocksCorrectness.Record.Proofs.Executions.envFactsOutside_catchUpOnWakeOutside M)
    R hΔ E

end GoldilocksCorrectness.Statements.AbstractTrace

/-! ## The pushed catch-up gives the sync fact -/

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFactsSync EnvFactsUpTo
  EnvFactsOutside SyncedWithin SyncedWithinUpTo SyncedWithinOutside)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts servesMin)
open Framework.StsMultisetLog (SignedMsg)
open Goldilocks (NamedObject RootOrder)
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder] {M : GoldilocksModel V}
  {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} {Δ Δw GST : ℕ}
  {ok : NamedObject V → Prop}

/-- **The pushed catch-up gives the sync fact.** On a wake-shaped trace, for a delay `Δ ≥ 1`,
`EnvFactsSync A x ΔClockAhead ΔClockBehind Δ Δw GST ok W` gives `SyncedWithin A x serves ok Δs GST` for every
selection `serves` whose objects every honest holder put on the wire itself at a step after which
it already served them (`hrelay`).

Why: an object `u` serves at `t` from its state after a step `k` at a time less than `t` was put on
the wire by `u` at a step `i < k` after which `u` already serves it; the pushed kit lemma delivers
that send, at a step after `i`, to every validator active from `t` through `max t GST + max Δ Δw`,
by synchrony if that validator was active since the send, by the catch-up otherwise; the serving
step the sync fact names is `i + 1`.

The variables:
- `R`: the run's facts; `E`: the synchronous
  promises; `serves`: the selection; `Δs`, `hΔA`, `hΔw`: the sync delay, at least the delay plus
  the clock-ahead bound and at least the catch-up delay (T-S2); `hrelay`: an object of the class `ok` an
  honest validator
  serves at its clock value after a step `k` was put on the wire by it, honest then, at a step
  `i < k` after which it already serves it at its clock value then (T-S1).

Read aloud: a network that pushes the backlog within `Δw` of a wake is one in which what honest
active validators would serve spreads within `max Δ Δw`, whatever the selection, provided an
honest validator put on the wire itself, once it served it, everything it serves. -/
theorem syncedWithin_of_envFactsSync (R : RunFacts M S x)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsSync A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver GST (releaseOf M S.C) ok GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {serves : M.N → ℕ → NamedObject V → Prop}
    {Δs : ℕ} (hΔA : (Δ : ℝ) + ΔClockAhead ≤ Δs) (hΔw : max Δ Δw ≤ Δs)
    (hrelay : ∀ (k : ℕ) (u : V) (o : NamedObject V), ok o →
      u ∉ A.corrupted k → serves (x.st k u) (x.clockValue k u) o →
      ∃ i : ℕ, i < k ∧ x.HonestSendAt A i ⟨u, o⟩ ∧ serves (x.st (i + 1) u) (x.clockValue (i + 1) u) o) :
    SyncedWithin A x serves ok (releaseOf M S.C) ΔRedeliver Δs GST :=
  (GoldilocksCorrectness.Record.Proofs.Executions.syncedWithin_of_envFactsSync M) R E hΔA hΔw
    hrelay

/-- **The pushed catch-up gives the sync fact over the minimal selection.** On a wake-shaped
trace, for a delay `Δ ≥ 1`, `EnvFactsSync A x ΔClockAhead ΔClockBehind Δ Δw GST ok W` gives
`SyncedWithin A x (servesMin M S.C) ok Δs GST` when every object of the class `ok` an
honest validator serves by `servesMin M S.C` was put on the wire by it at a step after which it
already served it (`hrelay`).

The variables:
- `R`: the run's facts; `E`: the synchronous
  promises; `Δs`, `hΔA`, `hΔw`: the sync delay, at least the delay plus
  the clock-ahead bound and at least the catch-up delay (T-S2); `hrelay`: an object of the class `ok` an
  honest validator serves at `t` by the minimal
  selection after a step `k` was put on the wire by it, honest then, at a step `i < k` after which
  it already serves it at `t`.

Read aloud: the pushed catch-up gives the sync fact over the minimal selection. -/
theorem syncedWithin_servesMin_of_envFactsSync (R : RunFacts M S x)

    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsSync A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver GST (releaseOf M S.C) ok GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {Δs : ℕ} (hΔA : (Δ : ℝ) + ΔClockAhead ≤ Δs) (hΔw : max Δ Δw ≤ Δs)
    (hrelay : ∀ (k : ℕ) (u : V) (o : NamedObject V), ok o →
      u ∉ A.corrupted k → servesMin M S.C (x.st k u) (x.clockValue k u) o →
      ∃ i : ℕ, i < k ∧ x.HonestSendAt A i ⟨u, o⟩ ∧
        servesMin M S.C (x.st (i + 1) u) (x.clockValue (i + 1) u) o) :
    SyncedWithin A x (servesMin M S.C) ok (releaseOf M S.C) ΔRedeliver Δs GST :=
  (GoldilocksCorrectness.Record.Proofs.Executions.syncedWithin_servesMin_of_envFactsSync M) R
    E hΔA hΔw hrelay

/-- **The pushed catch-up up to a bound gives the sync fact up to it.** On a wake-shaped trace,
for a delay `Δ ≥ 1`, `EnvFactsUpTo A x ΔClockAhead ΔClockBehind Δ Δw GST ok W b` gives
`SyncedWithinUpTo A x serves ok Δs GST b` for every selection whose objects every honest
holder put on the wire itself at a step after which it already served them.

The variables:
- `R`: the run's facts; `b`: the bound; `E`: the
  promises up to `b`; `serves`: the selection; `hrelay`: an object of the class `ok` an honest
  validator serves at `t` after a step `k` was put on the wire by it, honest then, at a step
  `i < k` after which it already serves it at `t`.

Read aloud: the bounded pushed catch-up gives the bounded sync fact. -/
theorem syncedWithinUpTo_of_envFactsUpTo (R : RunFacts M S x)
    {b : ℕ}
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsUpTo A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver GST (releaseOf M S.C) ok
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b)
    {serves : M.N → ℕ → NamedObject V → Prop}
    {Δs : ℕ} (hΔA : (Δ : ℝ) + ΔClockAhead ≤ Δs) (hΔw : max Δ Δw ≤ Δs)
    (hrelay : ∀ (k : ℕ) (u : V) (o : NamedObject V), ok o →
      u ∉ A.corrupted k → serves (x.st k u) (x.clockValue k u) o →
      ∃ i : ℕ, i < k ∧ x.HonestSendAt A i ⟨u, o⟩ ∧ serves (x.st (i + 1) u) (x.clockValue (i + 1) u) o) :
    SyncedWithinUpTo A x serves ok (releaseOf M S.C) ΔRedeliver Δs GST b :=
  (GoldilocksCorrectness.Record.Proofs.Executions.syncedWithinUpTo_of_envFactsUpTo M) R E hΔA hΔw
    hrelay

/-- **The suspended pushed catch-up gives the suspended sync fact.** On a wake-shaped trace, for a
delay `Δ ≥ 1`, `EnvFactsOutside A x ΔClockAhead ΔClockBehind Δ Δw GST ok W b₀ b₁` gives
`SyncedWithinOutside A x serves ok Δs GST b₀ b₁` for every selection whose objects every
honest holder put on the wire itself at a step after which it already served them.

Why: a time whose sync deadline is at or before `b₀` is served by the promises up to `b₀`, any
other by the synchronous promises from `max b₁ GST` on.

The variables:
- `R`: the run's facts; `b₀`, `b₁`: the start and
  the end of the period; `E`: the promises suspended on `[b₀, b₁)`; `serves`: the selection;
  `Δs`, `hΔA`, `hΔw`: the sync delay, at least the delay plus
  the clock-ahead bound and at least the catch-up delay (T-S2); `hrelay`: an object of the class `ok` an
  honest validator serves at `t` after a step `k` was put
  on the wire by it, honest then, at a step `i < k` after which it already serves it at `t`.

Read aloud: the suspended pushed catch-up gives the suspended sync fact. -/
theorem syncedWithinOutside_of_envFactsOutside (R : RunFacts M S x)
 {b₀ b₁ : ℕ}
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsOutside A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver GST (releaseOf M S.C) ok
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b₀ b₁)
    {serves : M.N → ℕ → NamedObject V → Prop}
    {Δs : ℕ} (hΔA : (Δ : ℝ) + ΔClockAhead ≤ Δs) (hΔw : max Δ Δw ≤ Δs)
    (hrelay : ∀ (k : ℕ) (u : V) (o : NamedObject V), ok o →
      u ∉ A.corrupted k → serves (x.st k u) (x.clockValue k u) o →
      ∃ i : ℕ, i < k ∧ x.HonestSendAt A i ⟨u, o⟩ ∧ serves (x.st (i + 1) u) (x.clockValue (i + 1) u) o) :
    SyncedWithinOutside A x serves ok (releaseOf M S.C) ΔRedeliver Δs GST b₀ b₁ :=
  (GoldilocksCorrectness.Record.Proofs.Executions.syncedWithinOutside_of_envFactsOutside M) R
    E hΔA hΔw hrelay

end GoldilocksCorrectness.Record.Statements.Executions
