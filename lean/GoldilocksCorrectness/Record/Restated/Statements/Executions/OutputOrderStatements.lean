module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.OutputOrder

@[expose] public section

/-!
# OutputOrderStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/OutputOrderStatements.lean`, over a
model `M` whose facts `F` hold, for a trace `x` whose node states are the model's: how a
validator's finalized block sits with respect to its confirmed tip and to its own later finalized
blocks. Each is a one-line call of the theorem of the same name of
`Record/Restated/Proofs/Executions/OutputOrder.lean`.

- `finalized_ancestorEq_confirmed_of_exec`: a validator's finalized block is its confirmed tip or
  an ancestor of it;
- `finalized_only_extends_of_exec`: a validator's finalized block at a step is its finalized block
  at every later step or an ancestor of it.

Each takes the validator honest through the step it reads.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **The finalized block is on the confirmed tip's chain.** At every step `i` of a trace, the
finalized block of a validator `v` honest through step `i` is its confirmed tip
(`M.ac_confirmed`) or an ancestor of it.

Why: the confirmed tip is the record of the latest confirmed block when that block is in the tree
of the frame the FG state gives the available chain, every block of which has the finalized block
as an ancestor or is it; otherwise the confirmed tip is the finalized block.

The variables:
- `M`: the model; `F`: its facts;
- `A`: the activity; `x`: the trace; `i`: the step; `v`: the validator.

Read aloud: an honest validator's finalized block is its confirmed tip or an ancestor of it. -/
theorem finalized_ancestorEq_confirmed_of_exec (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (i : ℕ) (v : V)
    (hH : x.HonestThrough A i v) :
    (x.st i v).finalized.AncestorEq (M.ac_confirmed (x.st i v)) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.finalized_ancestorEq_confirmed_of_exec M F) A x i
    v hH

/-- **The finalized block only extends.** For steps `i ≤ j` of a trace and a validator `v` honest
through step `j`, `v`'s finalized block after `i` steps is its finalized block after `j` steps or
an ancestor of it.

Why: no step of the trace replaces a validator's finalized block by one that is not a descendant
of it or it.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `A`: the activity; `x`: the trace; `R`: the run's facts (no promise of the
  environment is read); `v`: the validator; `i ≤ j`: the two steps.

Read aloud: an honest validator never abandons a finalized block. -/
theorem finalized_only_extends_of_exec (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (v : V) (i j : ℕ) (hij : i ≤ j)
    (hH : x.HonestThrough A j v) :
    (x.st i v).finalized.AncestorEq (x.st j v).finalized :=
  (GoldilocksCorrectness.Record.Proofs.Executions.finalized_only_extends_of_exec M F) S A x R v i
    j hij hH

end GoldilocksCorrectness.Record.Statements.Executions
