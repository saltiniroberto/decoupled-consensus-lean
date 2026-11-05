import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import RStsVariant2.Spec.ValidatorSets

/-!
# The real-time trace of any protocol

A trace is what a statement reads of a run of any protocol: its committees and what its proposers
require; after each step, the configuration: the real time, every validator's view (when its node state is known)
and clock reading (when it exists), the sent log, who is awake and who is corrupted; and for each
step, its event. Nothing here names a protocol, a node state type or a block type: the message type
`Msg` and the block type `Block` are parameters, and there is no node state type. Where a run with
node states is turned into a trace, the class `LARuns.NodeViewOf` fills each node's view
(`LARuns.Readers`, `LARuns.Bridge`). What a statement reads of the blocks and messages themselves (ancestry, roots, the
block a message carries, its author, its inclusions) is not part of a trace: it is read through the
classes `LARuns.BlockVocab` and `LARuns.MessageVocab` on the block and message types
(`LARuns.Statements.Statement4Defs`).

The message vocabulary (`SignedMsg`, `Recipients`, `Envelope`) has the shape of `RStsVariant2`'s,
so that a condition on the trace can be written as the condition on executions of `RStsVariant2`
it corresponds to. The view type (`NodeView`) and the types of the trace's committees and
proposer requirements (`CommitteeSpec`, `ProposerRequirement`) are here because the trace's fields
have them as types. The sleepiness window and the committee type that `CommitteeSpec`
abbreviates are `RStsVariant2`'s, shared with its conditions on executions.

Statement 4 (`LARuns.ConfirmedPersistsThroughAsyncPeriodOnRuns`) and Goldilocks's claim read no
trace: they read a run as observed. The types of this page give what the classes
`LARuns.NodeViewOf` and `LARuns.ProtocolCommittees` return (`NodeView`, `CommitteeSpec`,
`ProposerRequirement`) and what the protocol's healing premise sees of a step (`Event`, `Envelope`,
through `LARuns.PhaseStep`). The trace of a run (`LARuns.toRealTrace`) and the readings of this page
are what `LARuns.Proofs` relates to the run.

Every definition's docstring ends with its kind: the trace (what every trace is), or a reading of
a trace (a definition over a trace that assumes nothing).

This page imports Mathlib and `RStsVariant2.Spec.ValidatorSets` (for the committee type).
-/

set_option autoImplicit false

namespace LARuns

/-! ## 1. Messages -/

/-- A message together with its signer. Signing is structural: appearing under `sender = v` is
being signed by `v`.

Kind: the trace. -/
structure SignedMsg (Node Msg : Type) where
  /-- The signer. -/
  sender : Node
  /-- The message. -/
  msg : Msg
  deriving DecidableEq

/-- Whom a send is addressed to: every validator (a broadcast), or the validators of a set (a
multicast; a singleton is a point-to-point send).

Kind: the trace. -/
inductive Recipients (Node : Type) where
  /-- Every validator. -/
  | all
  /-- The validators of `nodes`. -/
  | only (nodes : Finset Node)
  deriving DecidableEq

/-- `recipients.Has v`: `v` is among the recipients `recipients`.

Kind: the trace. -/
def Recipients.Has {Node : Type} (recipients : Recipients Node) (v : Node) : Prop :=
  match recipients with
  | .all => True
  | .only nodes => v ∈ nodes

/-- A signed message with its recipients: what the sent log holds.

Kind: the trace. -/
structure Envelope (Node Msg : Type) extends SignedMsg Node Msg where
  /-- The recipients. -/
  recipients : Recipients Node
  deriving DecidableEq

/-! ## 2. Views -/

/-- What a statement reads of one node's state: its finalized block `F`, its confirmed tip `C`, the
blocks it holds `T`.

Kind: the trace (the type of a field). -/
structure NodeView (Block : Type) where
  /-- The finalized block. -/
  F : Block
  /-- The confirmed tip. -/
  C : Block
  /-- The blocks the node holds. -/
  T : Finset Block

/-! ## 3. Events and steps -/

/-- One step of a trace, as far as the statements read it: a tick, a restart, the delivery of an
envelope, or any other step.

Kind: the trace. -/
inductive Event (Node Msg : Type) where
  /-- `tick v t`: `v` runs its tick at its clock reading `t`. -/
  | tick (v : Node) (t : ℕ)
  /-- `restart v t keep`: `v` comes back up with its clock reading `t` and runs its wake reaction;
  `keep` says whether it keeps its memory. -/
  | restart (v : Node) (t : ℕ) (keep : Bool)
  /-- `deliver v e`: the envelope `e` is delivered to `v`, which runs its receive reaction. -/
  | deliver (v : Node) (e : Envelope Node Msg)
  /-- Any other step: a step of the environment (a clock change, a corruption, a crash), a send by
  a validator in the adversary set, a copy of a message already on the wire. -/
  | other

/-- A configuration, what is read of the nodes and the environment after `i` steps of a run, the
sent log aside: the real time at which it is entered; every validator's view, `none` when its node
state is not known (before the validator first comes online, and from its corruption on); every
validator's clock reading, `none` when its clock does not exist; the validators awake (online and not
crashed); the validators corrupted. The sent log is beside it in a `Step`, and the event of the
step taken from it is the trace's `RealTrace.action i`.

The view is what the statements read of a node: the trace carries the view, and no node state.
Where a run with node states is turned into a trace, the class `NodeViewOf` fills this field
(`LARuns.toRealTrace`).

The clock is a field, not read off the events: a validator's clock may exist before it first comes
online and may be moved while it is crashed, as in `RStsVariant2` (`Config.clock`), and neither
shows in the events. The facts tying the field to the events (`v`'s tick to `t` is taken while its
clock reads `t`) are no condition of this library: on the trace of a run they hold by the run's
steps.

Read aloud: the real time, what is read of every node, the clocks, who is awake and who is
corrupted.

Kind: the trace. -/
structure Configuration (Node Msg Block : Type) where
  /-- The real time at which this configuration is entered. -/
  time : ℝ
  /-- `view v`: what is read of `v`'s node state (its finalized block, its confirmed tip, the
  blocks it holds), or `none` when the node state is not known. -/
  view : (v : Node) → Option (NodeView Block)
  /-- `clock v`: the clock reading of `v`, or `none` when its clock does not exist. -/
  clock : (v : Node) → Option ℕ
  /-- The validators awake: online and not crashed. -/
  awake : Finset Node
  /-- The validators corrupted. -/
  corrupted : Finset Node

/-- What holds after `i` steps of a run: the configuration `config` and, beside it, the sent log
`sent`, every envelope put on the wire so far, with multiplicity. The configuration's fields are
read through the step directly (`(x i).time`, `(x i).view v`), and the configuration itself as
`(x i).config`.

Read aloud: the configuration after `i` steps, and everything sent so far.

Kind: the trace. -/
structure Step (Node Msg Block : Type) extends config : Configuration Node Msg Block where
  /-- The sent log: every envelope put on the wire so far, with multiplicity. -/
  sent : Multiset (Envelope Node Msg)

/-! ## 4. The protocol's requirements: committees and proposers -/

/-- The protocol's specification of committee `ci` in a trace: `RStsVariant2.CommitteeSpec` with
its members computed from a node's view, its sleepiness window, and the time until which it needs
the network synchronous.
For Goldilocks committee `ci` is slot `ci`'s committee.

Read aloud: who is on the committee, as a node's view gives them, how long they must stay up and
honest for the protocol to work, and until when the committee needs the network synchronous.

Kind: the trace (the type of a field). -/
abbrev CommitteeSpec (Node Block : Type) : Type :=
  RStsVariant2.CommitteeSpec Node (NodeView Block)

/-- What a proposer requires: the proposer, the block it protects (its proposal), the start of its
sleepiness window, the time before the asynchronous period up to which confirmed blocks are
protected, and the time by which the asynchronous period and its recovery must have ended for this
proposer's protection to hold (it depends on the proposer's slot, so each requirement carries its
own; for Goldilocks it is the vote time of slot `s + k` less one delay, `s` the proposer's slot). A
trace carries the set of them (`RealTrace.proposerReqs`).

Read aloud: who proposes, the block it proposed, from when it must stay up and honest, up to when
what was confirmed is protected, and by when the period and its recovery must be over.

Kind: the trace (the type of a field). -/
structure ProposerRequirement (Node Block : Type) where
  /-- The proposer. -/
  proposer : Node
  /-- The block the requirement protects: the proposer's proposal. -/
  block : Block
  /-- The start of its sleepiness window. -/
  tProposalStart : ℝ
  /-- The time before the asynchronous period up to which confirmed blocks are protected. -/
  tPreAsync : ℝ
  /-- The time by which the asynchronous period and its recovery must have ended. -/
  tPeriodEndBy : ℝ

/-! ## 5. The trace -/

/-- A real-time trace: its committees, its proposer requirements, and `x i`, what is read after `i`
steps, with the event of step `i`. The committees and the proposer requirements are one
per trace; where a run of a protocol is turned into a trace, the protocol's instance of the class
`ProtocolCommittees` gives them (`ProtocolCommittees.committees`, `ProtocolCommittees.proposerReqs`),
and a committee's members are read from a node's view (`CommitteeSpec.members`).

Read aloud: the run's committees, what its proposers require, and the run, one configuration per
step.

Kind: the trace. -/
structure RealTrace (Node Msg Block : Type) where
  /-- `committees ci`: the protocol's specification of committee `ci` in this trace. -/
  committees : (ci : ℕ) → CommitteeSpec Node Block
  /-- The protocol's proposer requirements in this trace. -/
  proposerReqs : Set (ProposerRequirement Node Block)
  /-- `step i`: what holds after `i` steps, configuration `i` and the sent log beside it; written
  `x i`. -/
  step : (i : ℕ) → Step Node Msg Block
  /-- `action i`: the event of step `i`, the step from configuration `i` to configuration `i + 1`;
  its real time is configuration `i + 1`'s `time`. -/
  action : (i : ℕ) → Event Node Msg

/-- `x i` is what holds after `i` steps of the trace `x`, `x.step i`: configuration `i` and the sent
log.

Kind: the trace (notation). -/
instance {Node Msg Block : Type} :
    CoeFun (RealTrace Node Msg Block) (fun _ => (i : ℕ) → Step Node Msg Block) :=
  ⟨RealTrace.step⟩

/-! ## 6. Readings of a trace

Each is a definition over a trace that assumes nothing of it. `x i` is the configuration after `i`
steps, entered at the real time `(x i).time`; step `i` leads from `x i` to `x (i + 1)`, so its real
time is `(x (i + 1)).time`. -/

namespace RealTrace

variable {Node Msg Block : Type}

/-- Configuration `i` of `x` lies within the real window `[tStart, tEnd]`: it is left at `tStart` or
later (`tStart ≤ (x (i + 1)).time`) and entered at `tEnd` or earlier (`(x i).time ≤ tEnd`). Every
configuration in force at some real time of `[tStart, tEnd]` lies within it, and so does a
configuration entered and left at one real time of `[tStart, tEnd]`.

Read aloud: the configuration after `i` steps is one the run is in somewhere between `tStart` and
`tEnd`.

Kind: a reading of a trace. -/
def Within (x : RealTrace Node Msg Block) (i : ℕ) (tStart tEnd : ℝ) : Prop :=
  tStart ≤ (x (i + 1)).time ∧ (x i).time ≤ tEnd

/-- `v` is honest in configuration `i`: outside the corrupted set there.

Read aloud: `v` is not corrupted after `i` steps.

Kind: a reading of a trace. -/
def Honest (x : RealTrace Node Msg Block) (i : ℕ) (v : Node) : Prop := v ∉ (x i).corrupted

/-- `v` is awake in configuration `i`: online and not crashed there.

Read aloud: `v` is up after `i` steps.

Kind: a reading of a trace. -/
def Awake (x : RealTrace Node Msg Block) (i : ℕ) (v : Node) : Prop := v ∈ (x i).awake

/-- `v` is active in configuration `i`: awake and honest there.

Read aloud: `v` is up and not corrupted after `i` steps.

Kind: a reading of a trace. -/
def Active (x : RealTrace Node Msg Block) (i : ℕ) (v : Node) : Prop := x.Awake i v ∧ x.Honest i v

/-- `v` is active throughout the real window `[tStart, tEnd]`: awake and honest in every
configuration within it (`RStsVariant2.Execution.UpAndHonestThroughout`, which reads "up" as outside
`crashed` with the local state known).

Read aloud: from `tStart` to `tEnd`, `v` is never crashed and never corrupted, and has come online.

Kind: a reading of a trace. -/
def ActiveThroughout (x : RealTrace Node Msg Block) (tStart tEnd : ℝ) (v : Node) : Prop :=
  ∀ i : ℕ, x.Within i tStart tEnd → x.Active i v

/-- Step `k` is an acting step of `v`: `v`'s tick, at some reading
(`RStsVariant2.Execution.ActingStep`, whose protocol events and interrupted reactions the trace has
no event for).

Read aloud: at step `k`, `v` ticks.

Kind: a reading of a trace. -/
def ActingStep (x : RealTrace Node Msg Block) (k : ℕ) (v : Node) : Prop :=
  ∃ t : ℕ, x.action k = .tick v t

/-- Step `i` puts the envelope `e` on the wire: one more copy of it in the sent log after the step.

Read aloud: step `i` sends `e`.

Kind: a reading of a trace. -/
def Puts [DecidableEq Node] [DecidableEq Msg] (x : RealTrace Node Msg Block) (i : ℕ)
    (e : Envelope Node Msg) : Prop :=
  e ∈ (x (i + 1)).sent - (x i).sent

/-- Step `i` puts `e` on the wire and `e`'s signer is honest in the configuration the step starts
from.

Read aloud: at step `i`, an honest validator sends `e`.

Kind: a reading of a trace. -/
def HonestSendAt [DecidableEq Node] [DecidableEq Msg] (x : RealTrace Node Msg Block) (i : ℕ)
    (e : Envelope Node Msg) : Prop :=
  x.Puts i e ∧ x.Honest i e.sender

/-- By step `iBefore`, `v` has reacted to the reading `tAtLeast`: at some step `iReact` before
`iBefore`, `v` ticked to, or was restarted at, a reading `tReact` at least `tAtLeast`.

Read aloud: before step `iBefore`, `v` has run its reaction at a reading at least `tAtLeast`.

Kind: a reading of a trace. -/
def ReactedAtLeast (x : RealTrace Node Msg Block) (iBefore : ℕ) (v : Node) (tAtLeast : ℕ) : Prop :=
  ∃ (iReact : ℕ) (tReact : ℕ), iReact < iBefore ∧ tAtLeast ≤ tReact ∧
    (x.action iReact = .tick v tReact ∨ ∃ keep : Bool, x.action iReact = .restart v tReact keep)

end RealTrace

end LARuns
