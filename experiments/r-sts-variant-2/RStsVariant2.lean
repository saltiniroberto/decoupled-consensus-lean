module
public import RStsVariant2.Spec.Message
public import RStsVariant2.Spec.Protocol
public import RStsVariant2.Spec.Execution
public import RStsVariant2.Spec.ValidatorSets
public import RStsVariant2.Spec.Conditions

@[expose] public section

/-!
# The sts variant in real time, its clock advanced by a step of its own — the root module

A copy of `RStsVariant`'s specification pages into the namespace `RStsVariant2`, changed so that a node's clock
advances by an environment step of its own, `setClock`, which runs no protocol code and is taken
whether the node is up or crashed. Every other node event runs the protocol at the stored reading, and a
restart leaves the clock as it is. a restart needs the clock, so a validator's clock starts
before it first comes online; and a corruption empties the validator's clock as well as its local
state, and no `setClock` is taken at a corrupted validator. `RStsVariant` is not edited.
-/
