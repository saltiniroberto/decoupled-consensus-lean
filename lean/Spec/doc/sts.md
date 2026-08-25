# The sts boundary

"sts" is short for *state transition system*, and it is the form this spec is shaped to
be consumed in. A protocol, formally, is a transition system: a set of states, and a
relation saying which states one step can reach from which. Here a state is a `Store` —
one node's view — and a step is one of two things: a node runs a duty, or the network
delivers a message. The spec defines the duties and the handlers; everything around
them — delivery, timing, the adversary, who runs what and when — belongs to a wiring
layer that does not exist yet.

## The framework

`deps/lean-sts` is a git submodule: a separate Lean framework for state transition
systems and proofs about them. This project will use its `StsMultisetLog` flavour, where
the network is a multiset log of messages. **Nothing imports it yet.** The wiring is
future work; what exists today is the boundary the spec holds ready for it.

## The boundary, in the code today

Four designs look the way they do because of this destination:

- **A duty is consumed as a relation.** A step relation is a membership statement, so a
  duty's overall effect is the set `NDREB.outcomes` (`Nondet.lean`), and the wiring will
  read it as `res ∈ (S.onTick t p).outcomes`. There is deliberately no function
  producing a single outcome — [nondeterminism.md](nondeterminism.md) says why.
- **`DutyResult` is the step-result shape.** A store and a send set (`Store.lean`) — the
  field names of the framework's `NodeStepResult` — built only by `NDREB.outcomes`;
  no duty returns one.
- **Duties are store-in, store-out.** A step's pre-state and post-state are the duty's
  input and output, as plain values; the broadcasts ride the monad's outbox.
- **`Message` is one type.** The framework wants one message type per protocol, so the
  wire objects are one sum (`Model.lean`), and `broadcast` takes exactly that.

`Analysis/` statements quantify over the same sets: "the failure never fires on a
coherent store" and "the walk does not depend on its picks" are statements about
`(…).run` and `(…).outcomes`, stated without any wiring.

## What the wiring will own, and the spec does not

Delivery and its timing — `Δ` is a constant here, and that objects arrive within it is a
fact about executions; the adversary; proposer assignment (`on_tick` takes the test as a
parameter); and relay — "an honest node relays every object it processes" is network
behaviour, so the handlers have no broadcast line.
