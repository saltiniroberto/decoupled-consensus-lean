module
public import GoldilocksCorrectness.Statements.Network.NetworkDefs

@[expose] public section

/-!
# What a statement reads of a validator, and a run read through it

For a block type `B`, `NodeView B` is what a statement written for any protocol reads of one
validator's node state: its finalized block, its confirmed tip and the blocks it holds. A protocol
supplies a map from its node states to `NodeView B`; a run of the protocol is read through it by
mapping every node state of every configuration, and keeping the time, the clocks, the views, the
sent log and the labels as they are.

This page imports only the sts framework and the vocabulary, so that it reads no protocol.

## The view

- `NodeView`: the finalized block `F`, the confirmed tip `C`, the held blocks `T`;
- `projectConfig`, `projectTrace`: a configuration, a trace, with every node state mapped.

## Reading a trace

- `HonestThroughV`: a validator outside the adversary set at every time up to a step's time;
- `stepBeforeV`, `stateBeforeV`: the step at which the time becomes `t`, and a validator's node
  state then;
- `PutsBlockV`: a validator puts a message carrying a block on the wire at a step.

The read-back equalities (`projectTrace_time`, …) hold by `rfl`.
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Statements.View

open Framework.StsMultisetLog (AtomicAction Schedule SignedMsg Config Local)
open GoldilocksCorrectness.Statements.Network

/-- `NodeView B`: what a statement reads of one validator's node state, for the block type `B`. -/
structure NodeView (B : Type) where
  /-- `F`: the validator's finalized block. -/
  F : B
  /-- `C`: the validator's confirmed tip. -/
  C : B
  /-- `T`: the blocks the validator holds. -/
  T : Finset B

/-! ## The projection -/

section Projection

variable {Node Msg St St' Ev : Type}

/-- `projectConfig f c`: the configuration `c` with every validator's node state `n` replaced by
`f n`; the time, the clocks, the views and the sent log are kept.

The variables:
- `f`: the map of node states (a protocol's map to `NodeView B`, for instance); `c`: the
  configuration.

Read aloud: `c`, with each validator's node state read through `f`. -/
def projectConfig (f : (n : St) → St') (c : Config Node Msg St) : Config Node Msg St' where
  time := c.time
  nodes := fun v => ⟨c[v].clock, f c[v].st, c[v].view⟩
  sent := c.sent

/-- `projectTrace f x`: the trace `x` with every configuration's node states mapped by `f`
(`projectConfig f`) and the labels kept.

The variables:
- `f`: the map of node states; `x`: the trace.

Read aloud: the run `x`, with each validator's node state after each step read through `f`. -/
def projectTrace (f : (n : St) → St') (x : Trace Node Msg St Ev) : Trace Node Msg St' Ev :=
  ⟨fun i => projectConfig f x[i], x.lbl⟩

/-- The time after `i` steps of `projectTrace f x` is the one of `x`.

Read aloud: the projection keeps the time. -/
@[simp] theorem projectTrace_time (f : (n : St) → St') (x : Trace Node Msg St Ev) (i : ℕ) :
    (projectTrace f x)[i].time = x[i].time := rfl

/-- The node state of `v` after `i` steps of `projectTrace f x` is `f` of the one of `x`.

Read aloud: the projection reads each node state through `f`. -/
@[simp] theorem projectTrace_st (f : (n : St) → St') (x : Trace Node Msg St Ev) (i : ℕ)
    (v : Node) : (projectTrace f x)[i][v].st = f x[i][v].st := rfl

/-- The clock of `v` after `i` steps of `projectTrace f x` is the one of `x`.

Read aloud: the projection keeps the clocks. -/
@[simp] theorem projectTrace_clock (f : (n : St) → St') (x : Trace Node Msg St Ev) (i : ℕ)
    (v : Node) : (projectTrace f x)[i][v].clock = x[i][v].clock := rfl

/-- The view of `v` after `i` steps of `projectTrace f x` is the one of `x`.

Read aloud: the projection keeps what each validator has received. -/
@[simp] theorem projectTrace_view (f : (n : St) → St') (x : Trace Node Msg St Ev) (i : ℕ)
    (v : Node) : (projectTrace f x)[i][v].view = x[i][v].view := rfl

/-- The sent log after `i` steps of `projectTrace f x` is the one of `x`.

Read aloud: the projection keeps every message sent. -/
@[simp] theorem projectTrace_sent (f : (n : St) → St') (x : Trace Node Msg St Ev) (i : ℕ) :
    (projectTrace f x)[i].sent = x[i].sent := rfl

/-- The labels of `projectTrace f x` are the ones of `x`.

Read aloud: the projection keeps the steps' labels. -/
@[simp] theorem projectTrace_lbl (f : (n : St) → St') (x : Trace Node Msg St Ev) :
    (projectTrace f x).lbl = x.lbl := rfl

end Projection

/-! ## Reading a trace -/

section Reading

variable {Node Msg St Ev : Type}

/-- `HonestThroughV Sched x i v`: `v` is outside the adversary set at every time at most the time
after `i` steps of `x`, `HonestThroughTime Sched x[i].time v`.

The variables:
- `Sched`: the schedule; `x`: the trace; `i`: the step; `v`: the validator.

Read aloud: `v` has not been in the adversary set at any time up to the time after `i` steps. -/
def HonestThroughV (Sched : Schedule Node) (x : Trace Node Msg St Ev) (i : ℕ) (v : Node) : Prop :=
  HonestThroughTime Sched (x[i].time : Int) v

open Classical in
/-- `stepBeforeV x t`: the first step of `x` whose label is the tick of every awake validator at
the time `t`, `tickAllAwake t`; `0` when there is none. Under the sts framework's atomic semantics
the configuration after that many steps holds every step at a time before `t`.

The variables:
- `x`: the trace; `t`: the time.

Read aloud: the step at which the run moves to the time `t`. -/
noncomputable def stepBeforeV (x : Trace Node Msg St Ev) (t : ℕ) : ℕ :=
  if h : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake t then Nat.find h else 0

/-- `stateBeforeV x t v`: the node state of `v` after `stepBeforeV x t` steps of `x`.

The variables:
- `x`: the trace; `t`: the time; `v`: the validator.

Read aloud: `v`'s node state when the run moves to the time `t`, the state `v`'s tick at `t`
starts from. -/
noncomputable def stateBeforeV (x : Trace Node Msg St Ev) (t : ℕ) (v : Node) : St :=
  x[stepBeforeV x t][v].st

/-- `PutsBlockV W x i v b`: the step `i` of `x` adds to the sent log a message signed by `v` that
carries the block `b` (`W.blockOf`).

The variables:
- `W`: the vocabulary; `x`: the trace; `i`: the step; `v`: the signer; `b`: the block.

Read aloud: at the step `i`, `v` puts the block `b` on the wire. -/
def PutsBlockV {B : Type} [DecidableEq Node] [DecidableEq Msg] (W : ViewVocab Node B Msg)
    (x : Trace Node Msg St Ev) (i : ℕ) (v : Node) (b : B) : Prop :=
  ∃ sm ∈ x[i + 1].sent - x[i].sent, sm.sender = v ∧ W.blockOf sm.msg = some b

/-- The step at which `projectTrace f x` moves to the time `t` is the one of `x`: the projection
keeps the labels.

Read aloud: the projection moves to each time at the same step. -/
theorem stepBeforeV_projectTrace {St' : Type} (f : (n : St) → St') (x : Trace Node Msg St Ev)
    (t : ℕ) : stepBeforeV (projectTrace f x) t = stepBeforeV x t := rfl

/-- The node state of `v` when `projectTrace f x` moves to the time `t` is `f` of the one of
`x`.

Read aloud: what `v` holds when the time becomes `t`, read through `f`. -/
theorem stateBeforeV_projectTrace {St' : Type} (f : (n : St) → St') (x : Trace Node Msg St Ev)
    (t : ℕ) (v : Node) : stateBeforeV (projectTrace f x) t v = f (stateBeforeV x t v) := rfl

end Reading

end GoldilocksCorrectness.Statements.View
