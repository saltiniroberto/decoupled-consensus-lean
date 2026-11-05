module
public import GoldilocksCorrectness.Statements.Executions.WiringDefs
public import GoldilocksCorrectness.Statements.Routines.WalkDefs
public import GoldilocksCorrectness.Statements.Routines.ScheduleDefs
public import GoldilocksCorrectness.Statements.Network.NetworkDefs

@[expose] public section

/-!
# An sts execution of Goldilocks: the definitions the statements read

An execution `x` of Goldilocks's node under the sts framework's atomic semantics (`AtomicExec`),
with the copy of the wiring that ticks at every reading (`GoldilocksCorrectness.Wiring.protocol`),
is read through the schedule's awake and adversary sets and each validator's node state strictly
before a time. The assumptions the statements take on the execution are stated here as `Prop`s.
Nothing is proved here.

Times are natural numbers, as the framework's: the spec's times, which are `Int`, are read as
natural numbers, and `GST` is a parameter of the statements.

## Reading the execution

- `stepBefore`: the step of the tick at a time, whose configuration holds every step at earlier
  times;
- `stateBefore`: a validator's node state strictly before a time;
- `inHonestTree`: a block is held, at some step, by a validator honest at that step;
- `inHonestTreeBy`: the same, at a step at a time at most a bound;
- `tickInputState`: the node state a validator's tick at a time starts from.

## The times

- `Δ`, `Δ_F`: the two delays;
- `slotStart`, `voteTime`, `supportCutoff`, `viewFreeze`, `lateVoteCutoff`: the start of a slot
  and its times `Δ`, `2Δ`, `3Δ` and `6Δ` after it;
- `dutyWindowStart`, `proposalWindowStart`: the two times the wake rule compares with.

## The object classes

- `acObject`: a block or a Goldfish vote;
- `fgObject`: an attestation.

## The assumptions

The network model and the divergence of time (`TimeDiverges`, `HonestSendAt`,
`SynchronyFromWake`, `CatchUpOnWake`) are stated for any protocol, over the execution's trace
`x.toTrace`, in `Statements/Network/NetworkDefs.lean`; the object classes they are taken at are
`acObject` and `fgObject`. The assumptions that read Goldilocks's own objects and node states:

- `RootsNameBlocks`: within the blocks honest validators hold, a root names one block;
- `RootsNameBlocksUntil`: within the blocks honest validators hold by a time, a root names one
  block (its negation, `RootCollisionHeldBy`, is on `UnforgeabilityDefs.lean`, beside the
  vocabulary its view form reads);
- `ParentHeldAtDelivery`: a block is delivered to a validator only when the validator holds its
  parent;
- `VotesCastByOwner`: every copy of an honest validator's Goldfish vote on the wire descends from
  that validator's own tick.

## The properties every execution has

- `TicksSucceed`: an honest awake validator's tick never fails (proved by
  `ticksSucceed_of_exec`).
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction AtomicHonest Schedule SignedMsg entrants)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol DREBOutcomesOk)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## Reading the execution -/

section Reading

variable {S : Setup V} {Sched : Schedule V}

open Classical in
/-- `stepBefore x t`: the step of `x` whose label is the tick of every awake validator at the
time `t`, `tickAllAwake t`, the first one if there were several; `0` when there is none, which is
the case at `t = 0` (the first tick is at `1`) and at a time `x` never reaches. The configuration
`x[stepBefore x t]` is at the time `t − 1` and holds every step at a time before `t`.

Read aloud: the step at which the execution moves to the time `t`. -/
noncomputable def stepBefore (x : AtomicExec (protocol S) Sched) (t : ℕ) : ℕ :=
  if h : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake t then Nat.find h else 0

/-- `stateBefore x t v`: the node state of the validator `v` in the configuration
`x[stepBefore x t]`.

Read aloud: `v`'s node state after every step of `x` at a time before `t`, the state `v`'s tick at
`t` starts from. -/
noncomputable def stateBefore (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) :
    NodeState V :=
  x[stepBefore x t][v].st

/-- `inHonestTree x B`: some validator holds the block `B` in its FG state's tree at some step of
`x`, and is outside the schedule's adversary set at that step's time.

Read aloud: an honest validator holds `B` at some point of the execution. -/
def inHonestTree (x : AtomicExec (protocol S) Sched) (B : Block V) : Prop :=
  ∃ (i : ℕ) (v : V), AtomicHonest x i v ∧ B ∈ (x[i][v].st).S.T

/-- `inHonestTreeBy x t B`: some validator holds the block `B` in its FG state's tree at some step
of `x` whose time is at most `t`, and is outside the schedule's adversary set at that step's time.
It is `inHonestTree x B` with the step's time bounded by `t`.

The variables:
- `x`: the execution; `t`: the bound on the time; `B`: the block.

Read aloud: an honest validator holds `B` at some step at a time at most `t`. -/
def inHonestTreeBy (x : AtomicExec (protocol S) Sched) (t : ℕ) (B : Block V) : Prop :=
  ∃ (i : ℕ) (v : V), AtomicHonest x i v ∧ x[i].time ≤ t ∧ B ∈ (x[i][v].st).S.T

/-- `tickInputState x i t v`: the node state the tick reaction of the validator `v` starts from at
the step `i` of `x`, when that step is the tick of every awake validator at the time `t`. For a
validator entering the awake set at `t` (`entrants Sched t`: awake and outside the adversary set
at `t`, asleep at `t − 1`), its state after the wake reaction, which the sts framework runs at
`v`'s framework clock `x[i][v].clock`: `wake x[i][v].st x[i][v].clock`; for any other, its state
`x[i][v].st`.

Read aloud: what `v`'s tick at `t` starts from, a validator that has just woken having first
forgotten the time it had been awake since and set its clock to its framework clock. -/
def tickInputState (x : AtomicExec (protocol S) Sched) (i t : ℕ) (v : V) : NodeState V :=
  if v ∈ entrants Sched t then wake x[i][v].st (x[i][v].clock : Int) else x[i][v].st

end Reading

/-! ## The times -/

/-! ## The object classes -/

/-- `acObject o`: the object `o` is a block or a Goldfish vote, not an attestation.

Read aloud: `o` is an object the protocol is designed to have delivered within `Δ`. -/
def acObject : NamedObject V → Prop
  | .attest _ => False
  | _ => True

/-- `fgObject o`: the object `o` is an attestation.

Read aloud: `o` is an object the protocol is designed to have delivered within `Δ_F`. -/
def fgObject : NamedObject V → Prop
  | .attest _ => True
  | _ => False

/-! ## The assumptions -/

section Assumptions

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

/-- Every honest awake validator's tick succeeds: at every step that is the tick of every awake
validator at a time `t`, for every validator awake and outside the adversary set at `t`, the
failure is not among the outcomes of the node's `tick` at `t` and an outcome exists
(`DREBOutcomesOk`), from the node state it starts from (`tickInputState`, the woken state for a
validator that has just woken).

The variables:
- `x`: the execution; `i`: the step; `t`: the time of the tick; `v`: the validator.

Every execution has this property (`ticksSucceed_of_exec`,
`Statements/Executions/NoRaiseStatements.lean`); no theorem of the library takes it as a hypothesis.

Read aloud: an honest awake validator's tick never fails. -/
def TicksSucceed : Prop :=
  ∀ (i t : ℕ) (v : V), x.lbl i = AtomicAction.tickAllAwake t →
    v ∈ Sched.awake (t : Int) → v ∉ Sched.adv (t : Int) →
    DREBOutcomesOk (tick S.C S.P S.X (tickInputState x i t v) (t : Int))

/-- Roots name blocks within the honest trees: two blocks that honest validators hold, at any
steps, and that have the same root are the same block.

The variables:
- `x`: the execution; `B`, `B'`: the two blocks.

Read aloud: within what honest validators ever hold, a root names one block. -/
def RootsNameBlocks : Prop :=
  ∀ B B' : Block V, inHonestTree x B → inHonestTree x B' → B.root = B'.root → B = B'

/-- `RootsNameBlocksUntil S Sched x t`: two blocks that honest validators hold at steps at times at
most `t`, and that have the same root, are the same block. It is `RootsNameBlocks S Sched x` with
the blocks restricted to those held by the time `t` (`inHonestTreeBy`).

The variables:
- `x`: the execution; `t`: the bound on the time; `B`, `B'`: the two blocks.

Read aloud: within what honest validators hold by the time `t`, a root names one block. -/
def RootsNameBlocksUntil (t : ℕ) : Prop :=
  ∀ B B' : Block V, inHonestTreeBy x t B → inHonestTreeBy x t B' → B.root = B'.root → B = B'

/-- A block compatible with a validator's finalized block is delivered to the validator only when
the validator holds its parent: at every step that delivers a signed message carrying a block
other than the genesis block to a validator, if the block is compatible with that validator's
finalized block `S.F`, that validator's FG state holds the block's parent in its tree `S.T`.
Nothing is assumed of a block that conflicts with the receiver's finalized block: synchrony may
require such a block to be delivered to a validator that refused its parent and never will hold
it, and the unrestricted form would then allow no execution.

The variables:
- `x`: the execution; `j`: the step of the delivery; `v`: the receiver; `sm`: the signed message;
  `B`: the block it carries.

Read aloud: a block that does not conflict with a validator's finalized block reaches that
validator only once the validator holds its parent. -/
def ParentHeldAtDelivery : Prop :=
  ∀ (j : ℕ) (v : V) (sm : SignedMsg V (NamedObject V)) (B : Block V),
    x.lbl j = AtomicAction.deliver v sm →
    -- the delivered message carries the block `B`, not the genesis block
    sm.msg = NamedObject.block B → B ≠ Block.genesis →
    -- `B` does not conflict with the receiver's finalized block
    (x[j][v].st).S.F.compatible B = true →
    B.parent ∈ (x[j][v].st).S.T

/-- Nobody casts a Goldfish vote in an honest validator's name: whenever a step `i` puts on the
wire a signed message carrying the Goldfish vote `vote`, as the object or in the `votes` of a
block, and `vote.val_index` is honest at that step's time, some step `k ≤ i` is the tick of every
awake validator at a time `t` and puts the signed message `⟨vote.val_index, .gfVote vote⟩` on the
wire. A relayed object is signed by the relayer, so the signer of the message says nothing of who
cast the vote; the assumption is therefore about the vote's own validator. Signatures are not
modelled, and this is the unforgeability they would give.

The variables:
- `x`: the execution; `i`: the step of the send; `sm`: the signed message; `vote`: the Goldfish
  vote it carries;
- `k`: the step of the voter's own send; `t`: the time of that step's tick.

Read aloud: every copy of an honest validator's Goldfish vote on the wire descends from that
validator's own tick. -/
def VotesCastByOwner : Prop :=
  ∀ (i : ℕ) (sm : SignedMsg V (NamedObject V)) (vote : GoldfishVote V),
    sm ∈ x[i + 1].sent - x[i].sent →
    -- `sm` carries `vote`, as its object or in the `votes` of the block it carries
    (sm.msg = NamedObject.gfVote vote ∨
      ∃ B : Block V, sm.msg = NamedObject.block B ∧ vote ∈ B.votes) →
    vote.val_index ∉ Sched.adv (x[i].time : Int) →
    ∃ (k t : ℕ), k ≤ i ∧ x.lbl k = AtomicAction.tickAllAwake t ∧
      (⟨vote.val_index, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[k + 1].sent - x[k].sent

end Assumptions

end GoldilocksCorrectness.Statements.Executions
