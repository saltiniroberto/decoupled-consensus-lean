import LARuns.Readers
import RStsVariant2

/-!
# An execution of `RStsVariant2` read as a real-time trace

**This page imports `RStsVariant2`, the bare real-time variant of the sts framework**: states,
steps, executions; not Goldilocks and not `GoldilocksCorrectness`. The bridge is a function of
`RStsVariant2`'s executions, `Exec Pr`.

What it gives: `toRealTrace tAwakeEnd π`, the execution `π` of any protocol `Pr` of `RStsVariant2`
read as a real-time trace through the classes `NodeViewOf` and `ProtocolCommittees`
(`LARuns.Readers`): the instance of `ProtocolCommittees` on `Pr` fills the trace's committees and
proposer requirements (read from `π`, the latter for a healing phase that ends at `tAwakeEnd`), and
the instance of `NodeViewOf` on the node states each node's view from the node's memory state; the
event of a step, read from a run (`eventOf`) or from any execution with an
`RStsVariant2.Observable` (`eventOfG`, which statement 4's healing-phase segment reads on an observed
run); and the observed run that carries its committees and proposer requirements
(`ObservedRunWithCommittees`, built from a run by `observeWithCommittees`), which statement 4 reads.

Statement 4 and Goldilocks's claim read no `RealTrace`: `toRealTrace` has no reader among the
statements, and the theorems of `LARuns.Proofs` are about it.

This page imports `LARuns.Readers` (and through it `LARuns.Trace` and `RStsVariant2`).
-/

set_option autoImplicit false

namespace LARuns

open RStsVariant2 (Exec Protocol Observable)

section Bridge

variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg] [Fintype Node]

/-- The recipients of `RStsVariant2`, as this folder's. -/
def recipientsOf : RStsVariant2.Recipients Node → Recipients Node
  | .all => .all
  | .only nodes => .only nodes

/-- An envelope of `RStsVariant2`, as this folder's. -/
def envelopeOf (e : RStsVariant2.Envelope Node Msg) : Envelope Node Msg :=
  { sender := e.sender, msg := e.msg, recipients := recipientsOf e.recipients }

/-- The event of step `i` of `π`, read from the configuration the step is taken from: a `tick v`
is `tick v t` at `v`'s clock reading `t` there; a `restart v keep` is `restart v t keep` at that
reading; a `deliver v e` is the trace's delivery when `v` is up (outside `crashed`, local state
known) and honest there, and a step of another kind otherwise (a delivery to a corrupted validator
files the message into its view and runs no reaction); every other step, and a tick or a restart
of a node whose clock does not exist (not enabled in the framework), is `other`.

Read aloud: the step of `π`, as the trace's events have it. -/
def eventOf {Pr : Protocol Node Msg NodeState Ev} (π : Exec Pr) (i : ℕ) : Event Node Msg :=
  match π.lbl i with
  | .tick v =>
    match π[i].clock v with
    | some t => .tick v t
    | none => .other
  | .restart v keep =>
    match π[i].clock v with
    | some t => .restart v t keep
    | none => .other
  | .deliver v e =>
    if v ∉ π[i].crashed ∧ (π[i][v]).isSome ∧ v ∉ π[i].adv then .deliver v (envelopeOf e) else .other
  | _ => .other

/-- The event of step `i` of `x`, any execution with an `RStsVariant2.Observable` (a run, or an observed
run), read from the configuration the step is taken from: as `eventOf`, with the run's
readings replaced by the class's (`Observable.lbl x i` for `π.lbl i`, `Observable.clock x i v` for
`π[i].clock v`, `Observable.crashed x i`, `Observable.adv x i`, and whether `Observable.state x i v`
is known for whether `π[i][v]` is). A `tick v` is `tick v t` at `v`'s clock reading `t` there; a
`restart v keep` is `restart v t keep` at that reading; a `deliver v e` is the trace's delivery when
`v` is up (outside the crashed set, state known) and honest there, and a step of another kind
otherwise; every other step, and a tick or a restart of a node whose clock does not exist, is
`other`.

Read aloud: the step of `x`, as the trace's events have it. -/
def eventOfG {X L : Type} [Observable X Node Msg L Ev] (x : X) (i : ℕ) : Event Node Msg :=
  match Observable.lbl x i with
  | .tick v =>
    match Observable.clock x i v with
    | some t => .tick v t
    | none => .other
  | .restart v keep =>
    match Observable.clock x i v with
    | some t => .restart v t keep
    | none => .other
  | .deliver v e =>
    if v ∉ Observable.crashed x i ∧ (Observable.state x i v).isSome ∧ v ∉ Observable.adv x i then
      .deliver v (envelopeOf e)
    else .other
  | _ => .other

/-- The execution `π` of the protocol `Pr` of `RStsVariant2` read as a real-time trace: the
committees and the proposer requirements are what the instance of `ProtocolCommittees` reads from `π`
(`ProtocolCommittees.committees π`, `ProtocolCommittees.proposerReqs tAwakeEnd π`); after `i` steps,
the real time is the stamp `π.stamp i`, every validator's view is the view (`NodeViewOf.view`) of the
memory state of its local state when known, its clock reading is
`π[i].clock v`, the sent log is `π[i].sent`, the validators awake are those outside `crashed` whose
local state is known, the validators corrupted are `π[i].adv`; and the event of step `i` is
`eventOf π i`.

Read aloud: the run, with the committees and proposer requirements read from it, and every
configuration read as the trace reads it.

Kind: the bridge from `RStsVariant2`. -/
noncomputable def toRealTrace {Block : Type} {Pr : Protocol Node Msg NodeState Ev}
    [NodeViewOf NodeState Block] [ProtocolCommittees Pr Block] (tAwakeEnd : ℝ) (π : Exec Pr) :
    RealTrace Node Msg Block where
  committees := ProtocolCommittees.committees π
  proposerReqs := ProtocolCommittees.proposerReqs tAwakeEnd π
  step i :=
    { time := π.stamp i
      view := fun v => NodeViewOf.viewOf ((π[i][v]).map fun l => l.st)
      clock := fun v => π[i].clock v
      sent := π[i].sent.map envelopeOf
      awake := Finset.univ.filter fun v => v ∉ π[i].crashed ∧ (π[i][v]).isSome
      corrupted := π[i].adv }
  action i := eventOf π i

#check @toRealTrace

end Bridge

/-! ## The observed run that carries its committees -/

/-- An observed run with the committees and proposer requirements its protocol gives it.

An `RStsVariant2.ObservedRun Node Msg Ev (NodeView Block)`, whose nodes'
states are read as views, together with the two things a protocol supplies through its instance
of `ProtocolCommittees`: its committees (`committees`) and its proposer requirements
(`proposerReqs`). An `RStsVariant2.ObservedRun` carries neither; this structure adds them, and
`run` is the observed run itself, unchanged. A reading of an execution, not part of the bare
framework: no step of `RStsVariant2` reads it, and it has no step relation.

Read aloud: the run seen through its nodes' views, with the committees and the proposer
requirements its protocol gives it. -/
structure ObservedRunWithCommittees (Node Msg Ev Block : Type) where
  /-- The observed run: the run's actions, real times, clocks, delivered messages, sent
  envelopes, corrupted and crashed sets, each node's state read as a view. -/
  run : RStsVariant2.ObservedRun Node Msg Ev (NodeView Block)
  /-- `committees ci`: the specification of committee `ci`, its members computed from a node's
  view. -/
  committees : (ci : ℕ) → CommitteeSpec Node Block
  /-- `proposerReqs tAwakeEnd`: the proposer requirements, for a healing phase that ends at
  `tAwakeEnd`. -/
  proposerReqs : (tAwakeEnd : ℝ) → Set (ProposerRequirement Node Block)

/-- An `ObservedRunWithCommittees` is read as its observed run `y.run` is, with its own committees
`y.committees`. A reading of an execution, not part of the bare framework.

Read aloud: its steps, times, clocks, views and sets are those of its observed run `y.run`, and
its committees are its own. -/
instance {Node Msg Ev Block : Type} :
    RStsVariant2.ObservableWithCommittees (ObservedRunWithCommittees Node Msg Ev Block) Node Msg (NodeView Block) Ev where
  lbl y := Observable.lbl y.run
  stamp y := Observable.stamp y.run
  clock y := Observable.clock y.run
  state y := Observable.state y.run
  view y := Observable.view y.run
  sent y := Observable.sent y.run
  adv y := Observable.adv y.run
  crashed y := Observable.crashed y.run
  committees y := y.committees

section RunCommittees

variable {Node Msg NodeState Ev Block : Type} [DecidableEq Node] [DecidableEq Msg]
  {Pr : Protocol Node Msg NodeState Ev} [NodeViewOf NodeState Block] [ProtocolCommittees Pr Block]

/-- A run `π` of `Pr` is read by its own readings, with the committees of the protocol's instance of
`ProtocolCommittees`, `ProtocolCommittees.committees π`, their members computed from the view
(`NodeViewOf.view`) of a node's memory state. A reading of an execution, not part of the bare
framework.

Read aloud: a run's steps, times, clocks, states and sets are its own, and its committees are the
protocol's, each member read through the node's view. -/
instance : RStsVariant2.ObservableWithCommittees (Exec Pr) Node Msg (RStsVariant2.Local Node Msg NodeState) Ev where
  toObservable := inferInstance
  committees π ci :=
    (ProtocolCommittees.committees π ci).comap fun l => NodeViewOf.view l.st

/-- The run `π` as observed, with committees.

The run `π` of `Pr` read as an `ObservedRunWithCommittees`. Its `run` is the run `π` as observed, each
node's local state replaced by the view of its memory state
(`RStsVariant2.observe NodeViewOf.view π`, where `NodeViewOf.view` on a run's local state `l` is the
view of its memory state `l.st`); that observed run alone carries no
committees and no proposer requirements. The two are added from `Pr`'s instance of
`ProtocolCommittees`: the committees `ProtocolCommittees.committees π` and the proposer
requirements `ProtocolCommittees.proposerReqs tAwakeEnd π`. A reading of an execution, not part of
the bare framework.

Read aloud: the run seen through its nodes' views, with the committees and the proposer
requirements its protocol supplies. -/
def observeWithCommittees (π : Exec Pr) : ObservedRunWithCommittees Node Msg Ev Block where
  run := RStsVariant2.observe NodeViewOf.view π
  committees := ProtocolCommittees.committees π
  proposerReqs tAwakeEnd := ProtocolCommittees.proposerReqs tAwakeEnd π

end RunCommittees

end LARuns
