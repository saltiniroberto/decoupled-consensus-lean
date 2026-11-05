module
public import StsMultisetLog

@[expose] public section

/-!
# What a statement over a protocol's views reads of its blocks and messages

`ViewVocab V B M`: for validators `V`, a block type `B` and a message type `M`, the operations a
statement written for any protocol reads of the protocol's blocks and messages: ancestry, root
equality, the block a message carries, the validator a message's object is attributed to, and the
objects a message's object includes. Each protocol supplies one value of it.

- `ViewVocab`: the five operations;
- `ViewVocab.Compatible`: one block is the other or an ancestor of it;
- `ViewVocab.AncStrict`: one block is an ancestor of the other and not the other.

This page imports only the sts framework, so that it reads no protocol.
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Statements.Network

/-- `ViewVocab V B M`: what a statement over a protocol's views reads of the protocol's blocks `B`
and messages `M`, for validators `V`. -/
structure ViewVocab (V B M : Type) where
  /-- `anc b b'`: `b` is `b'` or an ancestor of `b'`. -/
  anc : (b b' : B) → Prop
  /-- `sameRoot b b'`: `b` and `b'` carry the same root. -/
  sameRoot : (b b' : B) → Prop
  /-- `blockOf m`: the block the message `m` carries as its object, if any. -/
  blockOf : (m : M) → Option B
  /-- `author m`: the validator the object of the message `m` is attributed to, if any. -/
  author : (m : M) → Option V
  /-- `carries m m'`: the object of the message `m` includes the object of the message `m'`. -/
  carries : (m m' : M) → Prop

namespace ViewVocab

variable {V B M : Type} (W : ViewVocab V B M)

/-- `W.Compatible b b'`: one of the blocks `b`, `b'` is the other or an ancestor of it.

The variables:
- `W`: the vocabulary; `b`, `b'`: the two blocks.

Read aloud: `b` and `b'` lie on one chain. -/
def Compatible (b b' : B) : Prop := W.anc b b' ∨ W.anc b' b

/-- `W.AncStrict b b'`: the block `b` is an ancestor of the block `b'` and is not `b'`.

The variables:
- `W`: the vocabulary; `b`, `b'`: the two blocks.

Read aloud: `b` is a strict ancestor of `b'`. -/
def AncStrict (b b' : B) : Prop := W.anc b b' ∧ b ≠ b'

end ViewVocab

end GoldilocksCorrectness.Statements.Network
