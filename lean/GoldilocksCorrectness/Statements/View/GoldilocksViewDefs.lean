module
public import GoldilocksCorrectness.Statements.View.NodeViewDefs
public import GoldilocksCorrectness.Statements.Routines.NodeDefs
public import GoldilocksCorrectness.Statements.Executions.WiringDefs

@[expose] public section

/-!
# Goldilocks's node state read as a view

- `nodeView`: a Goldilocks node state read as a `NodeView`: its FG state's finalized block, its
  confirmed tip `confirmedOf`, its FG state's tree. It is the one definition that names the node
  state's fields for the statements read on the views.

A Goldilocks execution `x` is read on the views as `projectTrace nodeView x.toTrace`; the
equalities of this page read that trace back as `x`, each by `rfl`.
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Statements.View

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (confirmedOf)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `nodeView n`: the node state `n` read as a view: its finalized block `n.S.F`, its confirmed tip
`confirmedOf n`, and the tree of blocks it holds `n.S.T`.

The variables:
- `n`: the node state.

Read aloud: what a statement reads of a Goldilocks node: its finalized block, its confirmed block
and the blocks it holds. -/
def nodeView (n : NodeState V) : NodeView (Block V) := ⟨n.S.F, confirmedOf n, n.S.T⟩

section ReadBack

variable {S : Setup V} {Sched : Schedule V} (x : AtomicExec (protocol S) Sched)

/-- The time after `i` steps of `projectTrace nodeView x.toTrace` is the one of `x`.

Read aloud: the view of `x` keeps its time. -/
@[simp] theorem projectTrace_nodeView_time (i : ℕ) :
    (projectTrace nodeView x.toTrace)[i].time = x[i].time := rfl

/-- `v`'s finalized block after `i` steps of `projectTrace nodeView x.toTrace` is the one of `v`'s
node state after `i` steps of `x`.

Read aloud: the view's finalized block is the node's. -/
@[simp] theorem projectTrace_nodeView_F (i : ℕ) (v : V) :
    (projectTrace nodeView x.toTrace)[i][v].st.F = (x[i][v].st).S.F := rfl

/-- `v`'s confirmed tip after `i` steps of `projectTrace nodeView x.toTrace` is `confirmedOf` of
`v`'s node state after `i` steps of `x`.

Read aloud: the view's confirmed tip is the node's. -/
@[simp] theorem projectTrace_nodeView_C (i : ℕ) (v : V) :
    (projectTrace nodeView x.toTrace)[i][v].st.C = confirmedOf (x[i][v].st) := rfl

/-- The blocks `v` holds after `i` steps of `projectTrace nodeView x.toTrace` are the tree of `v`'s
node state after `i` steps of `x`.

Read aloud: the view's held blocks are the node's tree. -/
@[simp] theorem projectTrace_nodeView_T (i : ℕ) (v : V) :
    (projectTrace nodeView x.toTrace)[i][v].st.T = (x[i][v].st).S.T := rfl

/-- The sent log after `i` steps of `projectTrace nodeView x.toTrace` is the one of `x`.

Read aloud: the view of `x` keeps every message sent. -/
@[simp] theorem projectTrace_nodeView_sent (i : ℕ) :
    (projectTrace nodeView x.toTrace)[i].sent = x[i].sent := rfl

/-- The labels of `projectTrace nodeView x.toTrace` are the ones of `x`.

Read aloud: the view of `x` keeps the steps' labels. -/
@[simp] theorem projectTrace_nodeView_lbl :
    (projectTrace nodeView x.toTrace).lbl = x.lbl := rfl

end ReadBack

end GoldilocksCorrectness.Statements.View
