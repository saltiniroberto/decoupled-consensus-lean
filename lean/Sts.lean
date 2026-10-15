import Spec
import StsMultisetLog

/-!
# `Spec`'s node as a transition system

The boundary between `Spec` (the library of the same name, whose node is the routines
`Spec.initial`, `Spec.tick`, `Spec.receive_block`,
`Spec.receive_goldfish_vote` and `Spec.receive_attestation`) and the sts
framework (`deps/lean-sts`, the
`StsMultisetLog` flavour). Nothing here is protocol content: `Spec` says what a validator
does, and this file says when it does it, in the shape the framework's
`Framework.StsMultisetLog.Protocol` wants: an `init`, and a step relation over the framework's
events.

Nothing in `Spec` imports this file, and nothing here changes a definition there.

## The objects a validator re-sends

`relayedObjects`, declared here, is the multiset of objects a validator re-sends when it is
delivered one: the object itself and, for a block, the Goldfish votes and the attestations the
block includes. The objects are values of the type `NamedObject`
(`lean/Spec/Objects.lean`).

## The setup

`Setup V` is what the wiring is given: the node's parameters `C : Config`
(`lean/Spec/Config.lean`), the values `P : Provisional V` that the node is given for now
(the proposer of each slot, the committees, the weights), and the values `X : External V` that
another piece of software supplies (the root of each new block). The node state carries its
validator `v`. The setup holds no instant after which delivery is bounded: neither the node's
routines nor this file read one.

## The node state and `init`

The state the framework keeps per validator is `Spec.NodeState V`: the validator, the
store, the signing history and `awakeSince`, the instant since which the node has been awake without
interruption. `init p` is `initial S.C p`, the node state of the validator `p`. Its
`awakeSince` is one delay before the first cutoff of round `0`'s grade-2 result, so a validator
awake from the start passes every duty's wake test.

## The three events, and what runs on each

`tick` runs `Spec.tick` at every reading. The node's `tick` takes the parameters `C` and
the values `P` and `X`; the reaction passes `S.C`, `S.P` and `S.X`, and the node state carries its
validator. The tick runs in the monad `DREB` of `lean/Spec/Broadcast.lean`: its duties
broadcast what they send. The reaction runs it with nothing sent (`.run []`), which gives either an
answer (a new node state paired with the list of objects the tick broadcast, in the order broadcast)
or the failure. When it answers, the step's new state and its `send` are that node state and that
list. When it fails, the failure is not a step: the state is unchanged and nothing is sent, a
fallback that exists only so that the protocol is never stuck.

`recv m` runs `receive` with `S.C` and `S.P` on `m.msg`: this file's one dispatch, which maps
each kind of object to the node's routine for it (`receive_block`,
`receive_goldfish_vote`, `receive_attestation`). The step's `send` is
`relayedObjects m.msg`: the delivered payload and, when it is a block, every Goldfish vote and
every attestation the block includes, whether or not the block is admitted. The framework signs
each re-sent object with the receiver's name.

`wake` runs `Spec.wake` (`lean/Spec/NodeState.lean`), which sets `awakeSince` to
`none` and keeps the store and the signing history. Nothing is sent. The next `tick` the
validator runs writes its own instant into `awakeSince`, and every duty is tested against that
value.

## The clock

The framework hands a reaction `r`, the validator's own clock reading, a `Nat`. `Spec`'s
time is `Spec.Time`, which is `Int`. So a reading `r` is the
instant `(r : Int)`: one framework instant per unit of the node's time.

A framework tick at the reading `r` runs the node's `tick` at `(r : Int)`, at every reading.
The store's own clock is advanced by the node's tick and by nothing else, so an object delivered
at a reading is stamped with the reading of the validator's latest tick that did not fail.
Deliveries and wakes are not restricted: a `recv m` or a `wake` step may sit at any reading.

## Awakeness

The framework has its own notion of sleep, in its `Schedule`: a sleeping validator takes no tick
and receives nothing. `Spec`'s wake rule reads `awakeSince`, which this file's `wake` event
sets to `none`. Sleep is those two alone.

## Nothing is stated here

This file defines the `Framework.StsMultisetLog.Protocol` value and nothing else. Its one proof
is the `total` field, which the `Protocol` structure cannot exist without.
-/

set_option autoImplicit false

namespace Spec.Sts

open Framework.StsMultisetLog
open Spec (NamedObject)
open Spec (NodeState Config Provisional External wake initial tick
  receive_block receive_goldfish_vote receive_attestation)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- What the wiring is given: the node's parameters `C`, the values `P` given to the node for now
(the proposer of each slot, the committees, the weights), and the values `X` another piece of
software supplies (the root of each new block).

Read aloud: a setup is a choice of parameters, of the values given for now, and of the values
supplied from outside. -/
structure Setup (V : Type) [DecidableEq V] [Fintype V] where
  /-- The node's parameters. -/
  C : Config
  /-- The values given to the node for now. -/
  P : Provisional V
  /-- The values another piece of software supplies to the node. -/
  X : External V

/-- What the node state `n` becomes when the object `o` is delivered to it: a block goes to
`receive_block`, a Goldfish vote to `receive_goldfish_vote`, an
attestation to `receive_attestation`, each with the parameters `C` and the values `P`
it reads. This is the wiring's map from each wire object to the routine that receives it.

Read aloud: the node receives the object with the routine of its kind. -/
def receive (C : Config) (P : Provisional V) (n : NodeState V) (o : NamedObject V) :
    NodeState V :=
  match o with
  | .block B => receive_block C P n B
  | .gfVote vote => receive_goldfish_vote P n vote
  | .attest a => receive_attestation C n a

/-- The objects a validator re-sends when the object `o` is delivered to it: `o` itself and, when
`o` is a block `B`, every Goldfish vote `B` includes and every attestation `B` includes, each as
an object of its own.

Read aloud: the re-sent objects of a block are the block, its Goldfish votes and its
attestations; of any other object, the object alone. -/
def relayedObjects (o : NamedObject V) : Multiset (NamedObject V) :=
  match o with
  | .block B => {NamedObject.block B}
      + (B.gf_votes.map NamedObject.gfVote : Multiset _)
      + (B.attestations.map NamedObject.attest : Multiset _)
  | o => {o}

/-- The reaction of a validator holding the node state `n` to the event `e` at the clock
    reading `t`.

    A function, not a relation: each of the three events has exactly one reaction.

    - `tick`: the node's `tick` at `t`, at every reading, applied to the setup's
      parameters `S.C` and its values `S.P` and `S.X`, and run with nothing sent
      (`.run []`). If it answers with a node
      state and the list of objects it broadcast, the reaction's state is that node state and its
      `send` is that list. If it fails, the reaction keeps `n` and sends nothing; the failure is
      not a step, and this branch exists only so that the protocol is never stuck.
    - `recv m`: `receive` with `S.C` and `S.P` on the delivered object `m.msg`, at any
      reading;
      the reaction re-sends `relayedObjects m.msg`.
    - `wake`: `wake` of `lean/Spec/NodeState.lean`, which sets `awakeSince` to `none`;
      nothing is sent.

    Read aloud: at a tick, the node ticks and, when the tick succeeds, the validator takes the
    tick's state and sends what it broadcast, and when it fails, stays where it was and sends
    nothing; on a delivery it processes the object and re-sends it, with a block's Goldfish
    votes and attestations; on a wake it forgets the instant it had been awake since and sends
    nothing. -/
def reaction (S : Setup V) (n : NodeState V) (t : Int)
    (e : Event V (NamedObject V) Empty) :
    NodeStepResult (NodeState V) (NamedObject V) :=
  match e with
  | .tick =>
      match (tick S.C S.P S.X n t).run [] with
      | Except.ok (n', sent) => { state := n', send := (sent : Multiset (NamedObject V)) }
      | Except.error _ => { state := n, send := 0 }
  | .recv m => { state := receive S.C S.P n m.msg,
                 send := relayedObjects m.msg }
  | .wake => { state := wake n, send := 0 }
  | .custom ev => ev.elim

/-- `Spec`'s node, in the framework's shape.

    Parametrised by the `Setup`, because the node's routines read `S.C`, `S.P` and `S.X`: the
    parameters, the values given for now and the values supplied from outside.

    `init p` is `initial S.C p`: the validator `p`, the initial store, the initial
    signing history, and `awakeSince` one delay before the first cutoff of round `0`'s grade-2
    result.

    The step relation is the graph of `reaction`, so `total` is the function itself. `Ev :=
    Empty`: every instant this protocol acts at is a time, so the framework's own `tick` carries
    them all and there is no protocol-specific event to enable.

    Read aloud: every validator starts from `Spec`'s initial node state, and a step of
    validator `p` at reading `r` on event `e` is exactly `reaction S n r e`: the node state
    carries the validator, so the reaction does not take `p`. -/
def protocol (S : Setup V) :
    Framework.StsMultisetLog.Protocol V (NamedObject V) (NodeState V) Empty where
  init p := initial S.C p
  step _ r _view n e res := res = reaction S n (r : Int) e
  total := by
    intro _ r _view n e
    exact ⟨reaction S n (r : Int) e, rfl⟩
  enabled _ _ ev := ev.elim

end Spec.Sts
