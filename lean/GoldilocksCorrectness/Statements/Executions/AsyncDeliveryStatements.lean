module
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery

@[expose] public section

/-!
# The delivery premises around one asynchronous period, and up to a bound

The audited statements relating the delivery premises suspended on one asynchronous period
`[b₀, b₁)` to `SynchronyFromWake` and `CatchUpOnWake`, each proved in
`GoldilocksCorrectness/Proofs/Executions/AsyncDelivery.lean`. Before the period, the suspended
premise is the premise restricted to the sends due by `b₀` (`synchronyFromWakeUpTo_of_outside`);
from the period's end, it is the premise with `GST` moved to `max b₁ GST`
(`synchronyFromWake_of_outside_after`); the same for catch-up on wake.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

section Delivery

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

/-- **`SynchronyFromWake` is the deadline form at the ordinary deadline.** `SynchronyFromWake` is
`SynchronyFromWakeBy` at the deadline `max t GST + Δ`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Δ`: the delay; `GST`: the time
  from which the network is synchronous; `ok`: the object class.

Read aloud: synchrony is the deadline form at the ordinary deadline. -/
theorem synchronyFromWake_iff_by (Δ GST : ℕ) (ok : NamedObject V → Prop) :
    SynchronyFromWake Sched x.toTrace Δ GST ok ↔
      SynchronyFromWakeBy Sched x.toTrace (fun t => max t GST + Δ) ok :=
  GoldilocksCorrectness.Proofs.Executions.synchronyFromWake_iff_by S Sched x Δ GST ok

/-- **`CatchUpOnWake` is the deadline form at the ordinary deadline.** `CatchUpOnWake` is
`CatchUpOnWakeBy` at the deadline `max t GST + Δ`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Δ`: the delay; `GST`: the time
  from which the network is synchronous; `ok`: the object class.

Read aloud: catch-up on wake is the deadline form at the ordinary deadline. -/
theorem catchUpOnWake_iff_by (Δ GST : ℕ) (ok : NamedObject V → Prop) :
    CatchUpOnWake Sched x.toTrace Δ GST ok ↔
      CatchUpOnWakeBy Sched x.toTrace (fun t => max t GST + Δ) ok :=
  GoldilocksCorrectness.Proofs.Executions.catchUpOnWake_iff_by S Sched x Δ GST ok

end Delivery

section DeliveryFacts

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched} {Δ GST : ℕ}
  {ok : NamedObject V → Prop}

/-- **A bound on the deadlines can be lowered.** Synchrony up to `b'` gives synchrony up to every
`b ≤ b'`.

The variables:
- `b`, `b'`: the two bounds; `hle`: `b ≤ b'`; `h`: synchrony up to `b'`.

Read aloud: whatever is delivered for the sends due by `b'` is delivered for those due by `b`. -/
theorem SynchronyFromWakeUpTo.mono {b b' : ℕ} (hle : b ≤ b')
    (h : SynchronyFromWakeUpTo S Sched x Δ GST ok b') : SynchronyFromWakeUpTo S Sched x Δ GST ok b :=
  GoldilocksCorrectness.Proofs.Executions.SynchronyFromWakeUpTo.mono hle h

/-- **A bound on the deadlines can be lowered.** Catch-up on wake up to `b'` gives catch-up on
wake up to every `b ≤ b'`.

The variables:
- `b`, `b'`: the two bounds; `hle`: `b ≤ b'`; `h`: catch-up on wake up to `b'`.

Read aloud: a wake that catches up when due by `b'` catches up when due by `b`. -/
theorem CatchUpOnWakeUpTo.mono {b b' : ℕ} (hle : b ≤ b')
    (h : CatchUpOnWakeUpTo S Sched x Δ GST ok b') : CatchUpOnWakeUpTo S Sched x Δ GST ok b :=
  GoldilocksCorrectness.Proofs.Executions.CatchUpOnWakeUpTo.mono hle h

/-- **Synchrony gives every bounded synchrony.** `SynchronyFromWake` gives
`SynchronyFromWakeUpTo` at every bound `b`.

The variables:
- `b`: the bound; `h`: synchrony.

Read aloud: the premise gives every bounded one. -/
theorem synchronyFromWakeUpTo_of_synchronyFromWake (b : ℕ)
    (h : SynchronyFromWake Sched x.toTrace Δ GST ok) : SynchronyFromWakeUpTo S Sched x Δ GST ok b :=
  GoldilocksCorrectness.Proofs.Executions.synchronyFromWakeUpTo_of_synchronyFromWake b h

/-- **Catch-up on wake gives every bounded catch-up.** `CatchUpOnWake` gives `CatchUpOnWakeUpTo`
at every bound `b`.

The variables:
- `b`: the bound; `h`: catch-up on wake.

Read aloud: the premise gives every bounded one. -/
theorem catchUpOnWakeUpTo_of_catchUpOnWake (b : ℕ)
    (h : CatchUpOnWake Sched x.toTrace Δ GST ok) : CatchUpOnWakeUpTo S Sched x Δ GST ok b :=
  GoldilocksCorrectness.Proofs.Executions.catchUpOnWakeUpTo_of_catchUpOnWake b h

/-- **Before the period, the suspended synchrony is the bounded one.** Synchrony suspended on
`[b₀, b₁)` gives synchrony up to `b₀`.

Why: a send due by `b₀` has `deadlineOutside Δ GST b₀ b₁` equal to its ordinary deadline.

The variables:
- `b₀`, `b₁`: the start and the end of the period; `h`: synchrony suspended on `[b₀, b₁)`.

Read aloud: a send due by `b₀` is delivered as in the synchronous network. -/
theorem synchronyFromWakeUpTo_of_outside {b₀ b₁ : ℕ}
    (h : SynchronyFromWakeOutside Sched x.toTrace Δ GST ok b₀ b₁) :
    SynchronyFromWakeUpTo S Sched x Δ GST ok b₀ :=
  GoldilocksCorrectness.Proofs.Executions.synchronyFromWakeUpTo_of_outside h

/-- **Before the period, the suspended catch-up is the bounded one.** Catch-up on wake suspended
on `[b₀, b₁)` gives catch-up on wake up to `b₀`.

Why: a wake whose ordinary deadline is at most `b₀` has `deadlineOutside Δ GST b₀ b₁` equal to
that deadline.

The variables:
- `b₀`, `b₁`: the start and the end of the period; `h`: catch-up on wake suspended on `[b₀, b₁)`.

Read aloud: a wake due by `b₀` catches up as in the synchronous network. -/
theorem catchUpOnWakeUpTo_of_outside {b₀ b₁ : ℕ}
    (h : CatchUpOnWakeOutside Sched x.toTrace Δ GST ok b₀ b₁) :
    CatchUpOnWakeUpTo S Sched x Δ GST ok b₀ :=
  GoldilocksCorrectness.Proofs.Executions.catchUpOnWakeUpTo_of_outside h

omit [RootOrder] in
/-- **The deadline around the period is at most the shifted ordinary deadline.**
`deadlineOutside Δ GST b₀ b₁ t` is at most the ordinary deadline with `GST` moved to
`max b₁ GST`.

The variables:
- `b₀`, `b₁`: the start and the end of the period; `t`: the time of the send.

Read aloud: `deadlineOutside Δ GST b₀ b₁ t ≤ max t (max b₁ GST) + Δ`. -/
theorem deadlineOutside_le {b₀ b₁ t : ℕ} :
    deadlineOutside Δ GST b₀ b₁ t ≤ max t (max b₁ GST) + Δ :=
  GoldilocksCorrectness.Proofs.Executions.deadlineOutside_le

/-- **After the period, synchrony holds with `GST` moved to `max b₁ GST`.** Synchrony suspended
on `[b₀, b₁)` gives `SynchronyFromWake` at `max b₁ GST`: every send is delivered within `Δ` of
the latest of its time, `b₁` and `GST`. No hypothesis `b₀ ≤ b₁` is needed.

Why: `deadlineOutside Δ GST b₀ b₁ t ≤ max t (max b₁ GST) + Δ`, so a receiver awake and honest
through the later deadline is so through the earlier one.

The variables:
- `b₀`, `b₁`: the start and the end of the period; `h`: synchrony suspended on `[b₀, b₁)`.

Read aloud: once the period is over, the network is the ordinary synchronous network whose `GST`
is `b₁`. -/
theorem synchronyFromWake_of_outside_after {b₀ b₁ : ℕ}
    (h : SynchronyFromWakeOutside Sched x.toTrace Δ GST ok b₀ b₁) :
    SynchronyFromWake Sched x.toTrace Δ (max b₁ GST) ok :=
  GoldilocksCorrectness.Proofs.Executions.synchronyFromWake_of_outside_after h

/-- **After the period, catch-up on wake holds with `GST` moved to `max b₁ GST`.** Catch-up on
wake suspended on `[b₀, b₁)` gives `CatchUpOnWake` at `max b₁ GST`.

Why: as for synchrony, from `deadlineOutside_le`.

The variables:
- `b₀`, `b₁`: the start and the end of the period; `h`: catch-up on wake suspended on `[b₀, b₁)`.

Read aloud: once the period is over, a waking validator catches up as in the ordinary synchronous
network whose `GST` is `b₁`. -/
theorem catchUpOnWake_of_outside_after {b₀ b₁ : ℕ}
    (h : CatchUpOnWakeOutside Sched x.toTrace Δ GST ok b₀ b₁) :
    CatchUpOnWake Sched x.toTrace Δ (max b₁ GST) ok :=
  GoldilocksCorrectness.Proofs.Executions.catchUpOnWake_of_outside_after h

end DeliveryFacts

section Kit

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

end Kit

end GoldilocksCorrectness.Statements.Executions
