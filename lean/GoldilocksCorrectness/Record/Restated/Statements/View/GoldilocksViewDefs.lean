module
public import GoldilocksCorrectness.Record.Wiring
public import GoldilocksCorrectness.Record.ModelSpellings
public import GoldilocksCorrectness.Statements.View.GoldilocksViewDefs
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.RunFactsDefs
public import GoldilocksCorrectness.Statements.AbstractTrace.DeliveryDefs
public import GoldilocksCorrectness.Statements.Executions.UnforgeabilityDefs

@[expose] public section

/-!
# GoldilocksViewDefs, over a model

The definitions of `GoldilocksCorrectness/Statements/View/GoldilocksViewDefs.lean` over a model `M`:
a node state of the model read as a view, its finalized block, its confirmed tip `M.ac_confirmed n`
and its tree, and the equalities that read the view of an execution of `protocolOf M S` back as the
execution.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GoldilocksCorrectness.Record.Statements.View

open GoldilocksCorrectness.Statements.View (NodeView)

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Routines (confirmedOf)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)

/-- `nodeView M n`: the node state `n` read as a view: its finalized block `n.finalized`, its
confirmed tip `M.ac_confirmed n`, and the tree of blocks it holds `n.tree`.

The variables:
- `M`: the model;
- `n`: the node state.

Read aloud: what a statement reads of a Goldilocks node: its finalized block, its confirmed block
and the blocks it holds. -/
def nodeView (n : M.N) : NodeView (Block V) := ⟨n.finalized, M.ac_confirmed n, n.tree⟩

section ReadBack

variable (x : Trace V (NamedObject V) M.N)

/-- The time after `i` steps of `x.map (nodeView M)` is the one of `x`.

The variables:
- `M`: the model.

Read aloud: the view of `x` keeps its time. -/
@[simp] theorem projectTrace_nodeView_time (i : ℕ) :
    (x.map (nodeView M)).time i = x.time i := rfl

/-- `v`'s finalized block after `i` steps of `x.map (nodeView M)` is the one of
`v`'s node state after `i` steps of `x`.

The variables:
- `M`: the model.

Read aloud: the view's finalized block is the node's. -/
@[simp] theorem projectTrace_nodeView_F (i : ℕ) (v : V) :
    ((x.map (nodeView M)).st i v).F = (x.st i v).finalized := rfl

/-- `v`'s confirmed tip after `i` steps of `x.map (nodeView M)` is `confirmedOf` of
`v`'s node state after `i` steps of `x`.

The variables:
- `M`: the model.

Read aloud: the view's confirmed tip is the node's. -/
@[simp] theorem projectTrace_nodeView_C (i : ℕ) (v : V) :
    ((x.map (nodeView M)).st i v).C = M.ac_confirmed (x.st i v) := rfl

/-- The blocks `v` holds after `i` steps of `x.map (nodeView M)` are the tree of
`v`'s node state after `i` steps of `x`.

The variables:
- `M`: the model.

Read aloud: the view's held blocks are the node's tree. -/
@[simp] theorem projectTrace_nodeView_T (i : ℕ) (v : V) :
    ((x.map (nodeView M)).st i v).T = (x.st i v).tree := rfl

/-- The sent log after `i` steps of `x.map (nodeView M)` is the one of `x`.

The variables:
- `M`: the model.

Read aloud: the view of `x` keeps every message sent. -/
@[simp] theorem projectTrace_nodeView_sent (i : ℕ) :
    (x.map (nodeView M)).sent i = x.sent i := rfl

/-- The labels of `x.map (nodeView M)` are the ones of `x`.

The variables:
- `M`: the model.

Read aloud: the view of `x` keeps the steps' labels. -/
@[simp] theorem projectTrace_nodeView_lbl :
    (x.map (nodeView M)).lbl = x.lbl := rfl

end ReadBack

end GoldilocksCorrectness.Record.Statements.View

