import Spec.Store
import Spec.Protocol.ValidatorClient
import Spec.Defs.Raise

/-!
# The node state

A validator's node keeps three things: its store (`Store V` of `lean/Spec/Store.lean`, the
saved grades included), its signing history (`SigningHistory` of
`lean/Spec/Protocol/ValidatorClient.lean`), and `awakeSince`, the instant since which the
node has been awake without interruption.

`awakeSince` serves the wake rule: a validator performs a duty of round `ρ` only if it has been
awake, without interruption, since one delay before the first cutoff of the grade results that
duty reads. The proposal and the Goldfish vote read round `ρ`'s grade-1 result, whose first cutoff
is `C.opening ρ − 4 * C.Δ`; the confirmation reads the grade-1 and grade-2 results, and the
attestation the grade-0, grade-1 and grade-2 results, and the grade-2 result's first cutoff is
`C.opening ρ − 5 * C.Δ`. Here `C` is the node's parameters (`Config`, in
`lean/Spec/Config.lean`), `C.opening ρ` is the instant round `ρ`'s first slot opens, and `C.Δ`
is the delay bound.

This file declares, in the namespace `Spec`:

- `NodeState V`: the node state, with the fields `v`, `st`, `signingHistory` and `awakeSince`;
- `wake`: what the node's state becomes when the node wakes (`awakeSince` set to `none`);
- `record_awake`: what the first tick after a wake writes (`awakeSince` set to the tick's instant);
- `grade1_window_start` and `grade2_window_start`: the two instants a duty's test compares
  `awakeSince` with;
- `NodeState.awake_since`: the test itself, read on a node state, `n.awake_since t₀`.

The five routines of the wake rule are declared here, beside the field they read and write; the
test needs `Option.value`, which is why this file imports `Spec.Defs.Raise`, and the notation of
`Objects.lean` by which the test `if n.awakeSince ≠ none then` hands its fact to the read
`n.awakeSince.value` under it.

This file holds definitions only.
-/

open scoped DC

namespace Spec

/-- The state of a validator's node: the validator `v` it runs as, its store `st`, its signing
history `signingHistory`, and `awakeSince`, the instant since which the node has been awake
without interruption.
`awakeSince` is `none` between a wake and the first tick the node runs after it, and `some a`
afterwards, `a` being that tick's instant. -/
structure NodeState (V : Type) where
  /-- The validator this node runs as. -/
  v : V
  st : Store V
  signingHistory : SigningHistory
  awakeSince : Option Time

variable {V : Type} [DecidableEq V] [Fintype V]
variable (C : Config)

/-- The node's state when the node wakes: the state `n` with `awakeSince` set to `none`. The store
and the signing history are kept. -/
def wake (n : NodeState V) : NodeState V := Id.run do
  let mut n := n
  n.awakeSince ← none
  return n

/-- What a tick at the instant `t` first writes into the node's state `n`: if `awakeSince` is
`none` (the node has woken and run no tick since), it becomes `some t`; otherwise `n` is
unchanged. -/
def record_awake (n : NodeState V) (t : Time) : NodeState V := Id.run do
  let mut n := n
  if n.awakeSince = none then
    n.awakeSince ← t
  return n

/-- The instant from which a validator must have been awake to perform round `ρ`'s proposal and
Goldfish vote: one delay `C.Δ` before the first cutoff `C.early ρ .g1` of round `ρ`'s
grade-1 result. Its value is `C.opening ρ − 5 * C.Δ`, with `C.opening ρ` the instant round
`ρ`'s first slot opens. -/
def grade1_window_start (ρ : Round) : Time :=
  C.early ρ .g1 - C.Δ

/-- The instant from which a validator must have been awake to perform round `ρ`'s confirmation and
attestation: one delay `C.Δ` before the first cutoff `C.early ρ .g2` of round `ρ`'s
grade-2 result. Its value is `C.opening ρ − 6 * C.Δ`, with `C.opening ρ` the instant round
`ρ`'s first slot opens. -/
def grade2_window_start (ρ : Round) : Time :=
  C.early ρ .g2 - C.Δ

/-- The test of the wake rule: whether the node whose state is `n` has been awake, without
interruption, since the instant `t₀` or earlier. It is true when `n.awakeSince` is `some a` with
`a ≤ t₀`, and false when `n.awakeSince` is `none`. -/
def NodeState.awake_since (n : NodeState V) (t₀ : Time) : Bool := Id.run do
  if n.awakeSince ≠ none then
    return n.awakeSince.value ≤ t₀
  return false

end Spec
