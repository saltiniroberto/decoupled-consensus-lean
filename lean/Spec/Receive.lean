import Spec.HftFig2Store

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

/-- A message the store reacts to. One case today — see the module header. -/
inductive StoreMsg (Node Root : Type) where
  /-- A block message. -/
  | block (B : Blk Node Root)

section
variable [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root]

/-- The receive function: a block message is passed to `on_block`. See the module header
    for where this sits once the execution layer exists. -/
def receive (S : Store Node Root) (m : StoreMsg Node Root) : Store Node Root :=
  match m with
  | .block B => onBlock S B

end

end Decoupled
