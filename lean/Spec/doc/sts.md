# The sts boundary

"sts" is short for *state transition system*, and it is the form this spec is consumed in.
A protocol, formally, is a transition system: a set of states, and a relation saying which
states one step can reach from which. Here a state is a `Store` — one node's view — and a
step is a node reacting to something: its clock advancing, or a message arriving. The spec
says what a validator does; the wiring says when.

## The framework

`deps/lean-sts` is a git submodule: a separate Lean framework for state transition systems
and proofs about them. This project uses its `StsMultisetLog` flavour, where the network is
a multiset log of messages.

## The wiring, `lean/Sts.lean`

Its own `lean_lib`. It imports `Spec` and the framework; **nothing in `Spec/` imports it**,
and the extractor does not read it, so no line of it reaches the document.

Three definitions:

- **`Store.receive`** sends each wire object to its handler — a block to `process_block`, a
  Goldfish vote to `process_goldfish_vote`, an SG vote to `process_sg_vote`. This is what
  makes the handlers handlers: each is reached here and nowhere else, and no duty calls one.
- **`reactions`** is the set of results available on an event. A `tick` runs `on_tick`,
  whose outcomes may differ because a walk picks, so it is a set; the other events are
  deterministic.
- **`protocol`** is the framework's `Protocol`, with `init i = Σ.gen i` and `Ev := Empty`.

## Four decisions the wiring had to take

- **An arriving attestation runs `process_sg_vote`** on the vote it carries. The round's
  head travels only inside an attestation, `sg_vote` having stopped broadcasting, so a
  receiver that ignored attestations would never learn a head. A bare `Message.sgVote` runs
  the same handler and nothing honest sends one.
- **One tick per unit of the spec's clock**: a tick reading `r` is the instant `r`, and
  `Σ.t = -1` until the first. Ticks on a `Δ` grid would be a stronger model, and would miss
  `sgfg_voting i r`, which `SGSchedule` bounds but does not place.
- **A raise is not a step.** Only successful outcomes are reactions. Since the framework
  forbids a stuck protocol, the relation admits one fallback where nothing succeeds — the
  store unchanged, nothing sent — and that is what discharges `total`.
- **`wake` does nothing.** A slept validator's clock is behind, and the next tick moves it.

## What the boundary bought, in the spec's own shape

Four designs in `Spec/` look the way they do because of this destination:

- **A duty is consumed as a relation.** A step relation is a membership statement, so a
  duty's overall effect is the set `NDREB.outcomes` (`Nondet.lean`), read as
  `res ∈ (S.onTick t p).outcomes`. There is deliberately no function producing a single
  outcome — [nondeterminism.md](nondeterminism.md) says why.
- **`DutyResult` is the step-result shape.** A store and a send set (`Store.lean`) — the
  field names of the framework's `NodeStepResult` — built only by `NDREB.outcomes`; no duty
  returns one.
- **Duties are store-in, store-out.** A step's pre-state and post-state are the duty's input
  and output, as plain values; the broadcasts ride the monad's outbox.
- **`Message` is one type.** The framework wants one message type per protocol, so the wire
  objects are one sum (`Model.lean`), and `broadcast` takes exactly that.

`Analysis/` statements quantify over the same sets: "the failure never fires on a coherent
store" and "the walk does not depend on its picks" are statements about `(…).run` and
`(…).outcomes`, stated without any wiring.

## What the wiring does not own yet

**No model.** Which network and adversary assumptions this protocol is stated under — who is
corrupted, who is awake, what synchrony holds after GST — is a separate decision and a
separate file. The framework's `Examples/Models` shows the shape and is explicitly not
authoritative for anyone else's paper.

**No framework-layer audit.** The framework's own `Execution.lean` and `Schedule.lean` have
not been read against what this protocol needs.

And what belongs to a model rather than to the spec, whenever one lands: delivery and its
timing — `Δ` is a constant here, and that objects arrive within it is a fact about
executions; the adversary; proposer assignment (`on_tick` takes the test as a parameter);
and relay — "an honest node relays every object it processes" is network behaviour, so the
handlers have no broadcast line.
