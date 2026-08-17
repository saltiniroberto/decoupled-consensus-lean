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

## What the node does: receipt, and voting at the scheduled times

* The node state is `ValidatorState`: the store, plus Definition 12's durable signing
  history — the two things a validator keeps.
* `init` — every node starts at the genesis store with an empty history.
* `recv m` — fold the message into the store: `receive S m.msg`. The sender is ignored;
  a block speaks through its own proposer field, and the store's checks do not read the
  envelope. Attestations and Goldfish votes leave the store unchanged and are retained
  by the framework's log and views.
* `tick` — **the votes fire here**, read off the validator's own clock against the round
  schedule of Definition 28 (`def:recovery-timing`), the `Rounds` class:
  at a slot's `+Δ` phase the raw Goldfish vote of Definition 45 is broadcast, and at the
  round's action time `a_r` the combined FG attestation of Definition 50 is signed via
  `ordinaryVote`, the history updated before the send, per Definition 12. Whether ticks
  reach those readings is the execution layer's business (`Diligent`,
  `SynchronizedClocks`); the protocol just reacts to the reading it is handed.
* `wake` — no reaction. `Ev := Empty` — no protocol-specific events.
* **Three vote inputs are placeholders, flagged here and where they are passed**: the SG
  head is `⊥` (always honest by Definition 34, never live — head production needs the
  unrendered stable-root machinery); the Goldfish vote walks an empty candidate tree, so
  it votes the store's walk-from block; and `ordinaryVote` gets `h_F = 0` with
  `hasJC = false`, so the finality pair stays empty until those two open decisions are
  made. The *schedule* and the current-height pair are the real content; block
  production is still absent.

The `step` is the deterministic lift the framework documents — `res = reaction S e` —
which keeps it computable and makes `total` a `rfl`.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

variable {Node Root : Type}

/-- What one validator keeps: its store, and Definition 12's durable signing history. -/
structure ValidatorState (Node Root : Type) where
  /-- The fork-choice store. -/
  store : Store Node Root
  /-- The durable signing history `H_i` (Definition 12, `def:signing-history`). -/
  hist : SigningHistory Node Root

section
variable [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root] [Omega Node Root] [Rounds]

/-- One node's reaction to one event. A delivered message is folded into the store; a
    clock tick fires the scheduled vote for that reading, if the reading is one — see
    the module header, including the three flagged placeholder inputs; everything else
    changes nothing. -/
def reaction (i : Node) (t : Time) (st : ValidatorState Node Root)
    (e : Event Node (StoreMsg Node Root) Empty) :
    NodeStepResult (ValidatorState Node Root) (StoreMsg Node Root) :=
  match e with
  | .recv m => { state := { st with store := receive st.store m.msg }, send := ∅ }
  | .tick =>
      match Rounds.roundAt t with
      | some r =>
          if t = Rounds.actionTime r then
            -- the round's SG/FG action (Definition 28, lines 186–191): sign the one
            -- combined attestation, history updated before the send
            let (a, H') := ordinaryVote st.store t i r ⊥ 0 false st.hist
            { state := { st with hist := H' }, send := {.attestation a} }
          else if Rounds.isVoteTime r t then
            -- a slot's +Δ phase: the raw Goldfish vote (Definition 45); empty vote view
            -- and candidate tree pending the stable-root machinery, so the walk returns
            -- the store's walk-from block
            { state := st, send := {.gVote (goldfishVote i t ∅ [] st.store.R)} }
          else { state := st, send := ∅ }
      | none => { state := st, send := ∅ }
  | .wake => { state := st, send := ∅ }
  | .custom ev => ev.elim

/-- The node protocol: state is `ValidatorState`, behaviour is `reaction`, lifted into
    the framework's relational `step` as its documentation prescribes for a deterministic
    protocol. The reaction now reads the validator's identity and clock, which is what
    ties the votes to the framework's time advance. -/
def protocol : Protocol Node (StoreMsg Node Root) (ValidatorState Node Root) Empty where
  init _ := { store := Store.gen, hist := .gen }
  step i t _ st e res := res = reaction i t st e
  total i t _ st e := ⟨reaction i t st e, rfl⟩
  enabled _ _ ev := ev.elim

end

end Decoupled
