module
public import GoldilocksCorrectness.Proofs.Executions.Network
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery

@[expose] public section

/-!
# `Network.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Network.lean` that name a delivery
premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the deadlines
. The bound of each twin is the latest ordinary deadline `max t GST + Δ` of a send its
proof reads, written in the twin's own parameters.

* `delivered_before_stepBefore_of_honest_send`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open GoldilocksCorrectness.Statements.Routines (Δ)

namespace GoldilocksCorrectness.Proofs.Executions

open GoldilocksCorrectness.Statements.Executions
open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks (NamedObject RootOrder)
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
variable {V : Type} [DecidableEq V] [Fintype V]
variable [RootOrder] {S : Setup V} {Sched : Schedule V} (x : AtomicExec (protocol S) Sched)

/-- The delivery of `delivered_before_of_honest_send` comes strictly before
`stepBefore x (t + Δ)`, so the node state it produces is at or before the one
`stateBefore x (t + Δ) v` reads.

The variables:
- `x`: the execution; `Δ`: the delay bound; `GST`: the time from which the network is
  synchronous; `ok`: the class of objects the network assumptions promise about;
- `i`: the step of the send; `t`: the time; `v`: the receiver; `sm`: the signed message;
- `j`: the step of the delivery.

Read aloud: after `GST`, a validator awake and honest for a delay from `t` has, in its node state
before `t + Δ`, the delivery of every message of the class `ok` an honest validator put on the
wire by `t`.

Restated with the delivery premises up to `t + Δ`: the delivery is `delivered_before_of_honest_send_upTo`'s. -/
theorem delivered_before_stepBefore_of_honest_send_upTo (hdiv : TimeDiverges x.toTrace) {Δ GST : ℕ}
    {ok : NamedObject V → Prop} {t : ℕ}
    (hsync : SynchronyFromWakeUpTo S Sched x Δ GST ok (t + Δ))
    (hcatch : CatchUpOnWakeUpTo S Sched x Δ GST ok (t + Δ))
    (hmono : Sched.MonotoneCorruption)
    {i : ℕ} {v : V} {sm : SignedMsg V (NamedObject V)}
    (hsend : HonestSendAt Sched x.toTrace i sm)
    -- the object of `sm` is in the class `ok`
    (hok : ok sm.msg)
    -- the message is on the wire at or before `t`
    (hit : x[i + 1].time ≤ t)
    -- the network is synchronous from `t` on
    (hGST : GST ≤ t)
    -- `v` is awake and outside the adversary set at every time from `t` to `t + Δ`
    (hwin : ∀ t', t ≤ t' → t' ≤ t + Δ → v ∈ Sched.awake (t' : Int) ∧ v ∉ Sched.adv (t' : Int)) :
    ∃ j, i < j ∧ x.lbl j = AtomicAction.deliver v sm ∧ j < stepBefore x (t + Δ) := by
  obtain ⟨j, hij, hl, hj⟩ :=
    delivered_before_of_honest_send_upTo x hsync hcatch hmono hsend hok hit hGST hwin
  exact ⟨j, hij, hl, deliver_before_of_time x hdiv hl hj⟩

end GoldilocksCorrectness.Proofs.Executions

