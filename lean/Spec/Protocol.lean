import StsMultisetLog.Spec.Protocol
import Spec.Receive

/-!
# The node protocol, in the framework

This file renders no figure. It is the `Framework.StsMultisetLog.Protocol` instance for
one node of this protocol: the execution layer's entry point, where the framework's
events meet the store.

What the framework supplies, and what this file owes it (from
`StsMultisetLog/Spec/Protocol.lean`, read 2026-08-16): a protocol reacts to events and to
nothing else — `tick` (its own clock advanced), `recv m` (a message delivered, already in
the view), `wake`, and `custom` events of its own choosing. The instance owes four fields:
`init`, a relational `step`, `total` (a reaction always exists — Event-B's FIS), and
`enabled` for the custom events. Delivery is the framework's `deliver` action, which files
the message into the view and then runs the reaction on `Event.recv` — so `receive` here
is called exactly when a message is received, which is the wiring
`Spec/Receive.lean` exists for.

## What the node does today: receipt, and nothing else

* `init` — every node starts at the genesis store, `Store.gen`.
* `recv m` — fold the message into the store: `receive S m.msg`. The sender is ignored;
  a block speaks through its own proposer field, and the store's checks do not read the
  envelope.
* `tick`, `wake` — no reaction. Proposing and voting are behaviour at scheduled times,
  and neither the honest voting rule nor block production is encoded yet; until they are,
  a clock tick changes nothing.
* `Ev := Empty` — no protocol-specific events. The voting-round timers will be the first
  occupants, when the voting rule lands.
* `send := ∅` everywhere. An honest node currently sends nothing, so every message in
  flight originates from the framework's `adversarial` action. That is enough for safety
  statements about what stores accept; liveness needs honest production, which is exactly
  what is not yet here.

The `step` is the deterministic lift the framework documents — `res = reaction S e` —
which keeps it computable and makes `total` a `rfl`.
-/

set_option autoImplicit false

namespace Decoupled

open Framework.StsMultisetLog

variable {Node Root : Type}

section
variable [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root]

/-- One node's reaction to one event: a delivered message is folded into the store, and
    every other event — `tick`, `wake`, and the uninhabited `custom` — changes nothing.
    See the module header for why. -/
def reaction (S : Store Node Root)
    (e : Event Node (StoreMsg Node Root) Empty) :
    NodeStepResult (Store Node Root) (StoreMsg Node Root) :=
  if let .recv m := e then { state := receive S m.msg, send := ∅ }
  else { state := S, send := ∅ }

/-- The node protocol: state is the store, behaviour is `reaction`, lifted into the
    framework's relational `step` as its documentation prescribes for a deterministic
    protocol. -/
def protocol : Protocol Node (StoreMsg Node Root) (Store Node Root) Empty where
  init _ := Store.gen
  step _ _ _ S e res := res = reaction S e
  total _ _ _ S e := ⟨reaction S e, rfl⟩
  enabled _ _ ev := ev.elim

end

end Decoupled
