import Spec.Defs.Voting

/-!
# Message receipt — the store's entry point

This file renders no figure. It is the wiring Roberto asked for (2026-08-16): `on_block`
is called by the receive function when a block message is received. Neither paper names
that function; `receive` is its name here.

`StoreMsg` is the vocabulary of messages the store reacts to. It has one case today,
because Figure 2 (`hft:alg:store`) reacts to exactly one kind of arrival — votes reach the
store inside blocks, through `stateTransition`. Further cases land with the sections that
introduce them (the companion paper's healing section adds a vote pool fed by view-merge,
for one), each as its own constructor with its own `receive` arm.

When the execution layer lands, the framework's `deliver` action files a message into the
validator's view and hands the protocol an `Event.recv`; the protocol's reaction to a
block-carrying message is where `receive` gets called. That instance does not exist yet,
and nothing here anticipates its shape beyond taking the message as a value.
-/

set_option autoImplicit false

namespace Decoupled

variable {Node Root : Type}

/-- A message a validator broadcasts or receives. Decidable equality because the
    framework's step relation compares messages (its log is a multiset and views are
    `Finset`s). Three kinds: blocks, which the store consumes; the combined FG
    attestations of Definition 8 (`def:fg-message`), which reach chain state only when a
    block includes them, so receipt leaves the store alone — the framework's log and
    views are where a raw attestation is retained as evidence, which is the healing
    store's `objects` discipline (Definition 22, `def:stored-data`) played by the
    framework; and raw Goldfish votes (Assumption 3, `ass:goldfish-committees`),
    retained the same way. -/
inductive StoreMsg (Node Root : Type) where
  /-- A block message. -/
  | block (B : Blk Node Root)
  /-- A combined FG attestation, broadcast at an action time. -/
  | attestation (a : Attestation Node Root)
  /-- A raw Goldfish vote, broadcast at a slot's vote phase. -/
  | gVote (v : GoldfishVote Node Root)
  deriving DecidableEq

section
variable [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root]

/-- The receive function: a block message is passed to `on_block`; an attestation or a
    raw Goldfish vote changes no store field — see `StoreMsg`'s docstring for why that is
    the intended retention discipline, not a loss. -/
def receive (S : Store Node Root) (m : StoreMsg Node Root) : Store Node Root :=
  match m with
  | .block B => onBlock S B
  | .attestation _ => S
  | .gVote _ => S

end

end Decoupled
