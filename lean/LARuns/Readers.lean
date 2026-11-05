import LARuns.Trace
import RStsVariant2

/-!
# The readers: how a node state and a run are read, as two classes

This page defines two classes, each a reading of a protocol, not part of the bare framework.

`NodeViewOf NodeState Block` reads a single node state as a view (`NodeView`: the finalized block,
the confirmed tip and the blocks the node holds), from which a run as observed is built
(`RStsVariant2.ObservedRun`, the run with each node's local state replaced by its view,
`RStsVariant2.observe NodeViewOf.view π`). `ProtocolCommittees Pr Block` reads each
run `π : Exec Pr` of the protocol `Pr`: its committees, and its proposer requirements for a healing
phase that ends at a time `tAwakeEnd`. Statement 4
(`LARuns.ConfirmedPersistsThroughAsyncPeriodOnRuns`) takes both as instances; it reads the blocks and
messages themselves through the classes `LARuns.BlockVocab` and `LARuns.MessageVocab` on their types.

Two instances of `NodeViewOf` let the segment and the conclusions of statement 4 read either a trace
or a run: on `NodeView Block`, a view read as itself, and on a run's local state
`RStsVariant2.Local Node Msg NodeState`, the view of its memory state.

The page also defines the view of one node read from its node state (`NodeViewOf.viewOf`) and the
view of one node in one configuration of a run (`NodeViewOf.viewAt`). The bridge from `RStsVariant2`
(`LARuns.Bridge`) reads the first; statement 4 reads neither.

This page imports `LARuns.Trace` (for `NodeView`, `CommitteeSpec` and
`ProposerRequirement`) and `RStsVariant2` (for `Protocol` and `Exec`).
-/

set_option autoImplicit false

namespace LARuns

open RStsVariant2 (Exec Protocol)

/-- How a node state of type `NodeState` is read as a view with blocks of type `Block`. A reading of
a protocol, not part of the bare framework: no step reads it.

Read aloud: what one node state says its node has finalized, confirmed and holds.

Kind: part of the statements. -/
class NodeViewOf (NodeState : Type) (Block : outParam Type) where
  /-- `view st`: the node state `st` read as a view: its finalized block, its confirmed tip and the
  blocks it holds. -/
  view : (st : NodeState) → NodeView Block

/-- A view read as a view is itself. A reading of a node state, not part of the bare framework: no
step reads it. The segment and the conclusions of statement 4 read it on a trace whose nodes' states
are views.

Read aloud: a view's finalized block, confirmed tip and held blocks are its own.

Kind: part of the statements. -/
instance {Block : Type} : NodeViewOf (NodeView Block) Block where
  view w := w

/-- A run's local state `l` read as a view is the view of its memory state `l.st`. A reading of a
node state, not part of the bare framework: no step reads it. The segment and the conclusions of
statement 4 read it on a run.

Read aloud: a node's view in a run is the view of the state it holds in memory.

Kind: part of the statements. -/
instance {Node Msg NodeState Block : Type} [NodeViewOf NodeState Block] :
    NodeViewOf (RStsVariant2.Local Node Msg NodeState) Block where
  view l := NodeViewOf.view l.st

/-- The committees and the proposer requirements of each run of the protocol `Pr`, whose committees'
members are computed from views with blocks of type `Block`, and the clock readings at which the
protocol runs an update. A reading of a protocol, not part of the bare framework: no step reads it.

Read aloud: for every run of the protocol, its committees and what it requires of its proposers, and
the clock readings of its updates.

Kind: part of the statements. -/
class ProtocolCommittees {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    (Pr : Protocol Node Msg NodeState Ev) (Block : outParam Type) where
  /-- `committees π ci`: the specification of committee `ci` in the run `π` of `Pr`: its members as
  a node computes them from its view, its sleepiness window, and until when it needs the network
  synchronous. -/
  committees : (π : Exec Pr) → (ci : ℕ) → CommitteeSpec Node Block
  /-- `proposerReqs tAwakeEnd π`: the proposer requirements in the run `π` of `Pr`, for a healing
  phase that ends at `tAwakeEnd`. -/
  proposerReqs : (tAwakeEnd : ℝ) → (π : Exec Pr) → Set (ProposerRequirement Node Block)
  /-- `updateReadings c`: the clock reading `c` is one at which a node runs an update of the
  protocol. -/
  updateReadings : ℕ → Prop

namespace NodeViewOf

variable {Node Msg NodeState Ev Block : Type} [DecidableEq Node] [DecidableEq Msg]
  [NodeViewOf NodeState Block]

/-- The view of a node whose node state is `st`, `none` when the node state is not known.

Read aloud: the node state read as a view, when there is one.

Kind: the bridge. -/
def viewOf (st : Option NodeState) : Option (NodeView Block) :=
  st.map NodeViewOf.view

/-- `viewAt π i v`: the view of `v` in configuration `i` of the run `π`, the reading of the memory
state of `v`'s local state there, `none` when that local state is not known (before `v` first comes
online, and from its corruption on).

Read aloud: `v`'s finalized block, confirmed tip and held blocks after `i` steps of `π`, when `v`'s
state is known.

Kind: a reading of a run. -/
def viewAt {Pr : Protocol Node Msg NodeState Ev} (π : Exec Pr) (i : ℕ) (v : Node) :
    Option (NodeView Block) :=
  viewOf ((π[i][v]).map fun l => l.st)

end NodeViewOf

end LARuns
