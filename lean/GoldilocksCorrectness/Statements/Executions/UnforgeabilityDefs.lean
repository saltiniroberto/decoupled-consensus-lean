module
public import GoldilocksCorrectness.Statements.Executions.ExecutionDefs
public import GoldilocksCorrectness.Statements.Routines.ObjectDefs
public import GoldilocksCorrectness.Statements.View.ConclusionDefs
public import GoldilocksCorrectness.Statements.View.GoldilocksViewDefs

@[expose] public section

/-!
# The vocabulary of unforgeability and of the honest corollaries of accountable safety

The definitions the statements about unforgeability (`UnforgeabilityStatements.lean`) and the
honest corollaries of accountable safety (`HonestAccountableStatements.lean`) read:

- `author o`, the validator an object is attributed to, and `carries o o'`, the objects a block
  includes;
- `HonestThrough x i v`, a validator outside the adversary set at every time up to the time after
  a step (`HonestThroughTime Sched t v` at that time);
- `blockOf o`, the block an object is, and `Vocab.goldilocks`, Goldilocks's blocks and objects as
  the shared vocabulary `ViewVocab` reads them;
- `RootCollisionHeldBy S Sched x t`, two distinct blocks honest validators hold by the time `t`
  share a root, the negation of `RootsNameBlocksUntil S Sched x t`.

`HonestThroughTime`, `Unforgeability` (read as `Unforgeability Vocab.goldilocks Sched x.toTrace`)
and `AdversaryFewerThanThirdUntil` (read with `validator_count V`) are stated for any protocol in
`Statements/Network/NetworkDefs.lean`.


-/

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (carries)

open GoldilocksCorrectness.Statements.Network

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
/-- `author o`: the validator the object `o` is attributed to: a block's proposer (`none` for the
genesis block), a Goldfish vote's validator, an attestation's validator.

The variables:
- `o`: the object.

Read aloud: the validator who made the object, when there is one. -/
def author : NamedObject V → Option V
  | .block B => B.proposer?
  | .gfVote vote => some vote.val_index
  | .attest a => some a.val_index

section Executions

variable [RootOrder]

omit [Fintype V] in
/-- `HonestThrough x i v`: `v` is outside the adversary set at every time at most the time after
`i` steps, `HonestThroughTime Sched (x[i].time) v`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator.

Read aloud: `v` has not been in the adversary set at any time up to the time after `i` steps. -/
def HonestThrough {S : Setup V} {Sched : Schedule V} (x : AtomicExec (protocol S) Sched)
    (i : ℕ) (v : V) : Prop :=
  HonestThroughTime Sched (x[i].time : Int) v

end Executions

omit [DecidableEq V] [Fintype V] in
/-- `blockOf o`: the block the object `o` is, when it is one.

The variables:
- `o`: the object.

Read aloud: the block `o` carries, if `o` is a block. -/
def blockOf : NamedObject V → Option (Block V)
  | .block B => some B
  | _ => none

omit [DecidableEq V] [Fintype V] in
/-- `Vocab.goldilocks`: Goldilocks's blocks and objects as the shared vocabulary reads them:
ancestry is `Block.AncestorEq`, two blocks carry the same root when their `root` fields are equal,
an object carries the block it is, and `author` and `carries` are the attribution and the inclusion
of objects.

Read aloud: what a statement written for any protocol reads of Goldilocks's blocks and objects. -/
def Vocab.goldilocks : ViewVocab V (Block V) (NamedObject V) where
  anc := Block.AncestorEq
  sameRoot := fun B B' => B.root = B'.root
  blockOf := blockOf
  author := author
  carries := carries

section RootCollision

open GoldilocksCorrectness.Statements.View

variable [RootOrder]

/-- `RootCollisionHeldBy S Sched x t`: two distinct blocks that honest validators hold at steps at
times at most `t` have the same root. It is the negation of `RootsNameBlocksUntil S Sched x t`.

Defined as its view form: `RootCollisionHeldByV` with Goldilocks's
vocabulary `Vocab.goldilocks`, on the view of `x`, `projectTrace nodeView x.toTrace`, whose node
states are read as each validator's finalized block, confirmed tip (`confirmedOf`) and held blocks.
`rootCollisionHeldBy_unfold` (`Proofs/View/Bridges.lean`) reads it on the execution's node states.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the bound on the time.

Read aloud: by the time `t`, a root collision has hit two blocks honest validators hold. -/
def RootCollisionHeldBy (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (t : ℕ) : Prop :=
  RootCollisionHeldByV Vocab.goldilocks Sched (projectTrace nodeView x.toTrace) t

end RootCollision

end GoldilocksCorrectness.Statements.Executions
