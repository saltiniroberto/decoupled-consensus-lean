import LARuns.Environment
import LARuns.Bridge
import Mathlib.Data.NNReal.Defs

/-!
# The healing-phase segment, the conclusions of statement 4, and what every top statement shares,
read on the observed run

The definitions statement 4 (`LARuns.ConfirmedPersistsThroughAsyncPeriodOnRuns`) reads besides its
conditions, and the definitions all four top statements share (sections 5 and 6):

- `NodeObs`, `PhaseStep`: what the protocol's premise `healingConditions` sees of one configuration;
- `nodeObsOf`, `phaseSegment`: the healing-phase segment of an execution `τ` of any type with an
  `RStsVariant2.Observable` whose nodes' states are read as views (`NodeViewOf`) (a run `π : Exec Pr`, an observed run
  `RStsVariant2.ObservedRun Node Msg Ev (NodeView Block)`, or an `LARuns.ObservedRunWithCommittees`, which
  statement 4 reads: a run of a protocol of `RStsVariant2` as observed, each node's local
  state replaced by its view, with its committees and proposer requirements), with each step read as
  the bridge reads it (`eventOfG`) and the sent log as the bridge reads it (`envelopeOf`);
- the instance of `RStsVariant2.BlockTree` on `NodeView`: the tree of a view is its field `T`, so that
  statement 4 names no field of `NodeView` and passes no function for a node's blocks;
- the classes `BlockVocab` (ancestry and roots of blocks, with `BlockVocab.Compatible`) and
  `MessageVocab` (the block a message carries, the block it proposes, its author, its inclusions,
  conflicts), through which
  statement 4 reads the blocks and messages; `MessageVocab` extends `RStsVariant2.MessageAuthorship`,
  through which the condition on executions `RStsVariant2.UnforgeableSendsG` reads a message's author
  and inclusions;
- the conclusions `RootCollisionBy`, `ConfirmedPersistsBetween`, `FinalizedCompatibleBetween`, read on
  `τ`, an execution of any type with an `RStsVariant2.Observable` whose nodes' states are read as views (`NodeViewOf`),
  through its views and the two classes (`RootCollisionBy` through the readings of an execution
  `RStsVariant2.InHonestTreeByG` and `RStsVariant2.HonestSentByG`); the last two written with
  `HonestStateWithin` (a node honest in a configuration within a window, with its state) and
  `ProposedBy` (a block a node proposes while honest); beside `HonestStateWithin`,
  `HonestThroughEntryStateWithin` (the same, with the node honest in every configuration entered by
  the time that configuration is entered), read by statement 2's conclusions;
- `TopStatementConditions`, the conditions on the observed run every top statement takes
  (`LARuns.FinalizedCompatibleAfterHealingOnRuns`, `LARuns.ConfirmedTipAfterHealingOnRuns`,
  `LARuns.FinalityLivenessAfterHealingOnRuns` and statement 4), written once: the clock
  conditions, unforgeability, the two network conditions at the deadlines a statement passes, the
  weight bounds, the healing phase, the protocol's premise on it and committee sleepiness from
  `tGAT`;
- the readers the three statements after healing share: `HonestStateBy` (a node honest in a
  configuration entered by a time, with its state; read by statement 1's conclusion),
  `HonestThroughEntryStateBy` (a node's state in a configuration entered by a time, the node honest
  in every configuration entered by the time that configuration is entered; read by statements 2 and
  3), `ProposesAt` (the step at which a node proposes a block while honest) and
  `TickedAtLeastBefore` (a node has ticked at a reading at least a time before a configuration).

This page imports `LARuns.Environment` and `LARuns.Bridge` (the classes `NodeViewOf` and
`ProtocolCommittees`, and `RStsVariant2`), and `Mathlib.Data.NNReal.Defs` (the type `ℝ≥0`).
-/

set_option autoImplicit false

open scoped NNReal

namespace LARuns

open RStsVariant2 (ObservedRun HonestG UpAndHonestThroughoutG InHonestTreeByG HonestSentByG)
open RStsVariant2.Observable

/-! ## 1. The healing-phase segment -/

/-- What is read of one node in one configuration: its clock reading and its view.

Read aloud: one node's clock and its view.

Kind: part of the statements. -/
structure NodeObs (Block : Type) where
  /-- The node's clock reading. -/
  clock : ℕ
  /-- The node's view. -/
  view : NodeView Block

/-- One configuration of a trace as the protocol's premise `healingConditions` sees it: the real
time at which it is entered, the step taken from it, the sent log, who is awake, who is corrupted,
and what is read of each node (`NodeObs`, `none` when its view is not known or its clock does not
exist). The premise sees the environment's part of the configuration and the nodes through their
views and clocks only.

Read aloud: the time, the step, the wire, who is up, who is corrupted, and what is read of every
node.

Kind: part of the statements. -/
structure PhaseStep (Node Msg Block : Type) where
  /-- The real time at which the configuration is entered. -/
  time : ℝ
  /-- The step taken from it. -/
  action : Event Node Msg
  /-- The sent log. -/
  sent : Multiset (Envelope Node Msg)
  /-- The validators awake. -/
  awake : Finset Node
  /-- The validators corrupted. -/
  corrupted : Finset Node
  /-- `node v`: what is read of `v`, or `none` when its view is not known or its clock does not
  exist. -/
  node : (v : Node) → Option (NodeObs Block)

section Segment

variable {X Node Msg Ev Block L : Type} [DecidableEq Node] [DecidableEq Msg]
  [RStsVariant2.Observable X Node Msg L Ev] [NodeViewOf L Block]

/-- What is read of `v` in configuration `i` of the execution `τ`, any execution with an
`RStsVariant2.Observable` whose nodes' states are read as views (`NodeViewOf`): `some` of its clock reading and its view
when its view is known and its clock exists, `none` otherwise.

Read aloud: `v`'s clock and view, when its view is known.

Kind: a reading of an execution. -/
def nodeObsOf (τ : X) (i : ℕ) (v : Node) : Option (NodeObs Block) :=
  match state τ i v, clock τ i v with
  | some l, some tClock => some { clock := tClock, view := NodeViewOf.view l }
  | _, _ => none

open Classical in
/-- The healing-phase segment of the execution `τ`, any execution with an `RStsVariant2.Observable`
whose nodes' states are read as views (`NodeViewOf`): for each step index `i`, configuration
`i` as a `PhaseStep` when it lies within `[tStart, tEnd]` (left at `tStart` or later, entered at
`tEnd` or earlier), and nothing otherwise. The `PhaseStep` holds the real time `stamp τ i`, the step
`i` as the bridge reads it (`eventOfG τ i`), the sent log as the bridge reads it, the validators up
(outside the crashed set, view known), the validators corrupted, and what `nodeObsOf` reads of each
node. The protocol's premise `healingConditions` is applied to this segment, so by its type it can
test only the observed run within `[tStart, tEnd]`, and only the environment's part and what
`nodeObsOf` reads of each node.

Read aloud: the observed run as seen through the window `[tStart, tEnd]`, every step outside it
hidden, every node seen through its view.

Kind: a reading of an execution. -/
noncomputable def phaseSegment [Fintype Node] (τ : X) (tStart tEnd : ℝ) (i : ℕ) :
    Option (PhaseStep Node Msg Block) :=
  if tStart ≤ stamp τ (i + 1) ∧ stamp τ i ≤ tEnd then
    some { time := stamp τ i, action := eventOfG τ i, sent := (sent τ i).map envelopeOf,
           awake := Finset.univ.filter fun v => v ∉ crashed τ i ∧ (state τ i v).isSome,
           corrupted := adv τ i, node := nodeObsOf τ i }
  else none

end Segment

/-! ## 2. The tree of a view -/

/-- The tree of a node whose state is read as the view `w` is the view's field `T`, the blocks the
node has. The condition on executions `RStsVariant2.WeightBoundsG` reads a node's blocks through it
on an observed run whose nodes carry views.

Read aloud: a view's tree is its `T`.

Kind: part of the statements. -/
instance {Block : Type} : RStsVariant2.BlockTree (NodeView Block) Block :=
  ⟨NodeView.T⟩

/-! ## 3. The blocks and messages -/

/-- The ancestry and the roots of blocks of type `Block`, as the statements read them. A reading of
blocks, not part of the bare framework: no step reads it.

Read aloud: which blocks are ancestors of which, and which carry one root.

Kind: part of the statements. -/
class BlockVocab (Block : Type) where
  /-- `anc B B'`: `B` is `B'` or an ancestor of `B'`. -/
  anc : (B : Block) → (B' : Block) → Prop
  /-- `sameRoot B B'`: the blocks `B` and `B'` carry one root. -/
  sameRoot : (B : Block) → (B' : Block) → Prop

/-- `BlockVocab.Compatible B B'`: one of the blocks `B`, `B'` is the other or an ancestor of it.

Read aloud: `B` and `B'` are on one chain.

Kind: part of the statements. -/
def BlockVocab.Compatible {Block : Type} [BlockVocab Block] (B B' : Block) : Prop :=
  BlockVocab.anc B B' ∨ BlockVocab.anc B' B

/-- What the statements read of messages of type `Msg`, signed by validators of type `Node` and
carrying blocks of type `Block`: the block a message carries, the block a message proposes, and two
messages that conflict, on top of a message's author and inclusions
(`RStsVariant2.MessageAuthorship`). A reading of messages, not part of the bare framework: no step
reads it.

Read aloud: the block a message carries, the block it proposes, who its object is attributed to,
what it includes, and which two objects conflict.

Kind: part of the statements. -/
class MessageVocab (Msg : Type) (Node Block : outParam Type)
    extends RStsVariant2.MessageAuthorship Msg Node where
  /-- `blockOf m`: the block the message `m` carries, if any. -/
  blockOf : (m : Msg) → Option Block
  /-- `proposalOf m`: the block the message `m` proposes, if `m` is a block proposal. -/
  proposalOf : (m : Msg) → Option Block
  /-- `conflicts m m'`: two objects one validator must not both have authored (not read by
  statement 4). -/
  conflicts : (m : Msg) → (m' : Msg) → Prop

/-! ## 4. The conclusions -/

section Conclusions

variable {X Node Msg Ev Block L : Type} [DecidableEq Node] [DecidableEq Msg]
  [RStsVariant2.Observable X Node Msg L Ev] [NodeViewOf L Block]

/-- By the real time `tBy`, two distinct blocks with one root (`BlockVocab.sameRoot`) were each in
an honest node's tree (`RStsVariant2.InHonestTreeByG`, a node's tree being the `T` of its view) or
put on the
wire by one (the block a message carries read as `MessageVocab.blockOf`), in the execution `τ`, any
execution with an `RStsVariant2.Observable` whose nodes' states are read as views (`NodeViewOf`).

Read aloud: by `tBy`, a root collision has hit.

Kind: part of the statements. -/
def RootCollisionBy [BlockVocab Block] [MessageVocab Msg Node Block] (τ : X) (tBy : ℝ) : Prop :=
  -- a node's tree is the `T` of its view
  letI : RStsVariant2.BlockTree L Block := ⟨fun l => (NodeViewOf.view l).T⟩
  ∃ B B' : Block,
    (InHonestTreeByG τ tBy B ∨ HonestSentByG τ MessageVocab.blockOf tBy B) ∧
    (InHonestTreeByG τ tBy B' ∨ HonestSentByG τ MessageVocab.blockOf tBy B') ∧
    BlockVocab.sameRoot B B' ∧ B ≠ B'

/-- `HonestStateWithin τ tStart tEnd i v l`: configuration `i` of `τ` is entered within
`[tStart, tEnd]` (at a real time at or after `tStart` and at or before `tEnd`), the node `v` is
honest in it, and `l` is `v`'s state there.

Read aloud: `v` is honest in configuration `i`, entered within `[tStart, tEnd]`, and its state there
is `l`.

Kind: part of the statements. -/
def HonestStateWithin (τ : X) (tStart tEnd : ℝ) (i : ℕ) (v : Node) (l : L) : Prop :=
  -- `l` is `v`'s state in configuration `i`
  state τ i v = some l ∧
  -- `v` is honest in configuration `i`
  HonestG τ i v ∧
  -- configuration `i` is entered at or after `tStart`
  tStart ≤ stamp τ i ∧
  -- configuration `i` is entered at or before `tEnd`
  stamp τ i ≤ tEnd

/-- `HonestThroughEntryStateWithin τ tStart tEnd i v l`: configuration `i` of `τ` is entered within
`[tStart, tEnd]` (at a real time at or after `tStart` and at or before `tEnd`), the node `v` is
honest in every configuration entered by the time configuration `i` is entered, and `l` is `v`'s
state in configuration `i`.

Read aloud: `v`'s state in configuration `i` is `l`, `v` is honest in every configuration entered by
the time configuration `i` is entered, and that time is within `[tStart, tEnd]`.

Kind: part of the statements. -/
def HonestThroughEntryStateWithin (τ : X) (tStart tEnd : ℝ) (i : ℕ) (v : Node) (l : L) : Prop :=
  -- `l` is `v`'s state in configuration `i`
  state τ i v = some l ∧
  -- `v` is honest in configuration `i`
  HonestG τ i v ∧
  -- `v` is honest in every configuration entered by the time configuration `i` is entered
  (∀ j : ℕ, stamp τ j ≤ stamp τ i → HonestG τ j v) ∧
  -- configuration `i` is entered at or after `tStart`
  tStart ≤ stamp τ i ∧
  -- configuration `i` is entered at or before `tEnd`
  stamp τ i ≤ tEnd

/-- `ProposedBy τ v B`: at some step of `τ`, the node `v`, honest in the configuration the step is
taken from, puts on the wire an envelope it signs whose message proposes `B`
(`MessageVocab.proposalOf`).

Read aloud: `v`, while honest, proposed `B`.

Kind: part of the statements. -/
def ProposedBy [MessageVocab Msg Node Block] (τ : X) (v : Node) (B : Block) : Prop :=
  -- some step `i` of `τ` and some envelope `e`
  ∃ (i : ℕ) (e : RStsVariant2.Envelope Node Msg),
    -- step `i` adds a copy of `e` to the sent envelopes
    e ∈ sent τ (i + 1) - sent τ i ∧
    -- `e` is signed by `v`
    e.sender = v ∧
    -- `v` is honest in configuration `i`, the one step `i` is taken from
    HonestG τ i v ∧
    -- the message of `e` proposes `B`
    MessageVocab.proposalOf e.msg = some B

/-- If the node `vProposer`, while honest, proposed the block `B` (`ProposedBy`), then `B` is, in
every configuration of `τ` entered within `[tAsyncStart, tBy]`, the confirmed tip or an ancestor of the
confirmed tip of every node honest there (`HonestStateWithin`) that was up and honest throughout
`[tPreAsync − ΔPreAsync, tPreAsync]` (`RStsVariant2.UpAndHonestThroughoutG`). The tips are read in
the nodes' views in `τ`, any execution with an `RStsVariant2.Observable` whose nodes' states are read
as views (`NodeViewOf`), ancestry as `BlockVocab.anc`.

Read aloud: if `vProposer`, while honest, proposed `B`, then `B` stays, from `tAsyncStart` up to
`tBy`, an ancestor of or equal to the confirmed tip of every node that was up and honest just
before `tPreAsync`.

Kind: part of the statements. -/
def ConfirmedPersistsBetween [BlockVocab Block] [MessageVocab Msg Node Block] (τ : X)
    (tPreAsync ΔPreAsync tAsyncStart tBy : ℝ) (vProposer : Node) (B : Block) : Prop :=
  -- if `vProposer`, while honest, proposed `B`
  ProposedBy τ vProposer B →
    -- then for every node `v`, every configuration `i` of `τ`, and `v`'s state `l` there
    ∀ (v : Node) (i : ℕ) (l : L),
      -- if `v` is honest in configuration `i`, entered within `[tAsyncStart, tBy]`, and its
      -- state is `l`
      HonestStateWithin τ tAsyncStart tBy i v l →
      -- and `v` was up and honest throughout `[tPreAsync − ΔPreAsync, tPreAsync]`
      UpAndHonestThroughoutG τ (tPreAsync - ΔPreAsync) tPreAsync v →
      -- then `B` is the confirmed tip of `v`'s view, or an ancestor of it
      BlockVocab.anc B (NodeViewOf.view l).C

/-- If the node `vProposer`, while honest, proposed the block `B` (`ProposedBy`), then `B` is
compatible (`BlockVocab.Compatible`) with the finalized block of every node honest in any
configuration of `τ` entered within `[tAsyncStart, tBy]` (`HonestStateWithin`). The blocks are read in the
nodes' views in `τ`, any execution with an `RStsVariant2.Observable` whose nodes' states are read as
views (`NodeViewOf`).

Read aloud: if `vProposer`, while honest, proposed `B`, then from `tAsyncStart` up to `tBy` no
honest node finalizes a block conflicting with `B`.

Kind: part of the statements. -/
def FinalizedCompatibleBetween [BlockVocab Block] [MessageVocab Msg Node Block] (τ : X)
    (tAsyncStart tBy : ℝ) (vProposer : Node) (B : Block) : Prop :=
  -- if `vProposer`, while honest, proposed `B`
  ProposedBy τ vProposer B →
    -- then for every node `v`, every configuration `i` of `τ`, and `v`'s state `l` there
    ∀ (v : Node) (i : ℕ) (l : L),
      -- if `v` is honest in configuration `i`, entered within `[tAsyncStart, tBy]`, and its
      -- state is `l`
      HonestStateWithin τ tAsyncStart tBy i v l →
      -- then `B` is the finalized block of `v`'s view, an ancestor of it, or a descendant of it
      BlockVocab.Compatible B (NodeViewOf.view l).F

end Conclusions

/-! ## 5. The conditions every top statement takes -/

section TopStatementConditions

open RStsVariant2 (TickOncePerReadingG ClockWithinSkew ClockAdvancesWithin TicksWithin
  ActsWithinSkewG UnforgeableSendsG DeliveredBeforeActingG CatchUpAfterRestartG TickStepG WeightBoundsG
  HealingPhaseG CommitteeSleepinessFromG BlockRegistry)

/-- The conditions on the observed run `τ` that every top statement takes, after the extra
conditions a claim adds: the clocks, unforgeability, the network at the deadlines
`deliveryDeadline` and `catchUpDeadline` (each a function of the message and of the real time the
deadline counts from), the weight bounds at `tAwakeEnd`, the healing phase `[tGAT, tAwakeEnd]`, the
protocol's own premise `healingConditions` on the segment of that phase, and committee sleepiness
from `tGAT`.

Read aloud: the clocks are within their bounds and keep moving, no node acts at a stale reading,
nobody forges, the network delivers by its deadlines and catches a restarted node up, the adversary
is under the weight bounds, every honest node is online and up through the healing
phase, the protocol's premise holds on the phase, and from `tGAT` on every committee is mostly up
and honest.

Kind: part of the statements. -/
structure TopStatementConditions {Node Msg Ev Block : Type} [DecidableEq Node] [DecidableEq Msg]
    [Fintype Node] [BlockRegistry Block Node] [MessageVocab Msg Node Block]
    (tGST : ℝ) (deliveryDeadline catchUpDeadline : (m : Msg) → (t : ℝ) → ℝ)
    (ΔClockAhead ΔClockBehind : ℝ≥0) (tGAT tAwakeEnd : ℝ)
    (healingConditions : (segment : (i : ℕ) → Option (PhaseStep Node Msg Block)) → Prop)
    (τ : ObservedRunWithCommittees Node Msg Ev Block) : Prop where
  /-- A node ticks at most once at each reading of its clock. -/
  tickOnce : TickOncePerReadingG τ
  /-- Every step `setClock v t` is taken at a real time in `[t − ΔClockAhead, t + ΔClockBehind]`. -/
  clockWithinSkew : ClockWithinSkew ΔClockAhead ΔClockBehind τ
  /-- While a node is up and honest, its clock comes to every greater reading within the bounds,
  unless the node crashes or is corrupted first. -/
  clockAdvances : ClockAdvancesWithin ΔClockAhead ΔClockBehind τ
  /-- A node up and honest when its clock comes to read `t` ticks at the reading `t` by
  `t + ΔClockBehind`, unless it is corrupted or crashes first. -/
  ticksWithin : TicksWithin ΔClockBehind τ
  /-- Every tick and every restart a node takes while its clock reads `t` is at a real time at
  most `t + ΔClockBehind`. -/
  actsWithinSkew : ActsWithinSkewG ΔClockBehind τ
  /-- The adversary sends no honest validator's object that was not already sent (who an object is
  attributed to, and what it includes, read through `MessageVocab`). -/
  unforgeable : UnforgeableSendsG τ
  /-- Before each tick of a node, the network has delivered to it every envelope sent while it was
  up, with the node up since, by `deliveryDeadline` of its send. -/
  delivered : DeliveredBeforeActingG TickStepG deliveryDeadline τ
  /-- Before each tick of a node that restarted, it has been brought again after its last restart
  every earlier envelope addressed to it, by `catchUpDeadline` of the restart. -/
  catchUp : CatchUpAfterRestartG TickStepG deliveryDeadline catchUpDeadline τ
  /-- The validators corrupted by `tAwakeEnd` weigh less than any two quorums must share, and
  those corrupted by any time `t` less than a quorum, at every block honest nodes hold (the blocks
  of a node's view's `T`), in that block's validator set `BlockRegistry.registry B`. -/
  weights : WeightBoundsG tAwakeEnd τ
  /-- The healing phase `[tGAT, tAwakeEnd]` starts at or after `tGST`, and every honest node is
  online and up in it. -/
  healingPhase : HealingPhaseG tGST tGAT tAwakeEnd τ
  /-- The protocol's own premise, read on the observed run within the healing phase only. -/
  healing : healingConditions (phaseSegment τ (tStart := tGAT) (tEnd := tAwakeEnd))
  /-- In every committee of `τ` whose sleepiness window starts at or after `tGAT`, as any honest
  node computes it from its view in `τ`, the members up and honest throughout the window outnumber
  the rest. -/
  committees : CommitteeSleepinessFromG tGAT τ

end TopStatementConditions

/-! ## 6. The readers the statements after healing share -/

section AfterHealingReaders

variable {X Node Msg Ev Block L : Type} [DecidableEq Node] [DecidableEq Msg]
  [RStsVariant2.Observable X Node Msg L Ev] [NodeViewOf L Block]

/-- `HonestStateBy τ tBy i v l`: configuration `i` of `τ` is entered at or before `tBy`, the node
`v` is honest in it, and `l` is `v`'s state there.

Read aloud: `v` is honest in configuration `i`, entered by `tBy`, and its state there is `l`.

Kind: part of the statements. -/
def HonestStateBy (τ : X) (tBy : ℝ) (i : ℕ) (v : Node) (l : L) : Prop :=
  -- `l` is `v`'s state in configuration `i`
  state τ i v = some l ∧
  -- `v` is honest in configuration `i`
  HonestG τ i v ∧
  -- configuration `i` is entered at or before `tBy`
  stamp τ i ≤ tBy

/-- `HonestThroughEntryStateBy τ tBy i v l`: configuration `i` of `τ` is entered at or before `tBy`,
the node `v` is honest in every configuration entered by the time configuration `i` is entered,
and `l` is `v`'s state in configuration `i`.

Read aloud: `v`'s state in configuration `i` is `l`, `v` is honest in every configuration entered by
the time configuration `i` is entered, and that time is at most `tBy`.

Kind: part of the statements. -/
def HonestThroughEntryStateBy (τ : X) (tBy : ℝ) (i : ℕ) (v : Node) (l : L) : Prop :=
  -- `l` is `v`'s state in configuration `i`
  state τ i v = some l ∧
  -- `v` is honest in configuration `i`
  HonestG τ i v ∧
  -- `v` is honest in every configuration entered by the time configuration `i` is entered
  (∀ j : ℕ, stamp τ j ≤ stamp τ i → HonestG τ j v) ∧
  -- configuration `i` is entered at or before `tBy`
  stamp τ i ≤ tBy

/-- `ProposesAt τ i v B`: at step `i` of `τ`, the node `v`, honest in the configuration the step is
taken from, puts on the wire an envelope it signs whose message proposes `B`
(`MessageVocab.proposalOf`).

Read aloud: at step `i`, `v`, while honest, proposes `B`.

Kind: part of the statements. -/
def ProposesAt [MessageVocab Msg Node Block] (τ : X) (i : ℕ) (v : Node) (B : Block) : Prop :=
  -- some envelope `e`
  ∃ e : RStsVariant2.Envelope Node Msg,
    -- step `i` adds a copy of `e` to the sent envelopes
    e ∈ sent τ (i + 1) - sent τ i ∧
    -- `e` is signed by `v`
    e.sender = v ∧
    -- `v` is honest in configuration `i`, the one step `i` is taken from
    HonestG τ i v ∧
    -- the message of `e` proposes `B`
    MessageVocab.proposalOf e.msg = some B

/-- `TickedAtLeastBefore τ i v tAtLeast`: at some step before configuration `i`, `v` ticked at a
clock reading at least the real time `tAtLeast`.

Read aloud: before configuration `i`, `v` has run its tick at a reading at least `tAtLeast`.

Kind: part of the statements. -/
def TickedAtLeastBefore (τ : X) (i : ℕ) (v : Node) (tAtLeast : ℝ) : Prop :=
  -- some step `k` and some reading `tTick`
  ∃ (k : ℕ) (tTick : ℕ),
    -- step `k` is before configuration `i`
    k < i ∧
    -- the reading is at least `tAtLeast`
    tAtLeast ≤ (tTick : ℝ) ∧
    -- step `k` is `v`'s tick at the reading `tTick`
    TickAtG τ k v tTick

/-- `SettledAtG updateReadings τ t`: at the real time `t`, no update is half run. For every clock
reading `c` that `updateReadings` names an update reading and that is at most `t`, or to which some
node ticked by `t`, every node's tick to a reading at most `c` happened by `t`: step `k'` of `τ`
being `v'`'s tick at the reading `c' ≤ c`, the step is taken at a real time at most `t`.

Read aloud: at `t`, every update that is due or begun has run at every node, and so has every
earlier clock reading.

Kind: part of the statements. -/
def SettledAtG (updateReadings : ℕ → Prop) (τ : X) (t : ℝ) : Prop :=
  -- for every update reading `c`
  ∀ c : ℕ, updateReadings c →
    -- that is at most `t`, or to which some node ticked at a step taken by `t`
    ((c : ℝ) ≤ t ∨ ∃ (k : ℕ) (v : Node), TickAtG τ k v c ∧ stamp τ (k + 1) ≤ t) →
    -- every tick of a node to a reading at most `c` is taken by `t`
    ∀ (k' : ℕ) (v' : Node) (c' : ℕ), TickAtG τ k' v' c' → c' ≤ c → stamp τ (k' + 1) ≤ t

end AfterHealingReaders

end LARuns
