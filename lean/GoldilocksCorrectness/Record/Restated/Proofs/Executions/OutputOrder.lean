module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Monotone
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReadersOnChain

@[expose] public section

/-!
# OutputOrder, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/OutputOrder.lean`, over a model `M` whose
facts `F` hold, for a trace `x` whose node states are the model's: the order of a validator's two
outputs. The audited statements are in
`Record/Restated/Statements/Executions/OutputOrderStatements.lean`:

- `finalized_ancestorEq_confirmed_of_exec`: the finalized block is the confirmed tip or an ancestor
  of it;
- `finalized_only_extends_of_exec`: the finalized block at a step is the finalized block at every
  later step or an ancestor of it.

The kit: `finalized_ancestorEq_ac_confirmed`, the first at every node state of the model.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl)

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- A node state's finalized block is its confirmed tip or an ancestor of it.

Why: the confirmed tip is the record `n.latestConfirmed` when the record is in the tree of the
frame `M.fg_to_ac n`, whose blocks all have the finalized block as an ancestor or are it; and it is
the frame's finalized block, `n.finalized`, otherwise (the reader fact `ac_confirmed_eq`).

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state.

Read aloud: at every node state of the model, the finalized block is the confirmed tip or an
ancestor of it. -/
theorem finalized_ancestorEq_ac_confirmed (n : M.N) :
    n.finalized.AncestorEq (M.ac_confirmed n) := by
  rw [F.rd.ac_confirmed_eq]
  split
  · rename_i hin
    exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hin).2
  · rw [(GoldilocksCorrectness.Record.Proofs.Routines.fg_to_ac_F M F)]
    exact ancestorEq_refl _

variable [RootOrder]

/-- The finalized block is the confirmed tip or an ancestor of it, the proof; the audited statement
is in `Record/Restated/Statements/Executions/OutputOrderStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `A`: the activity; `x`: the trace; `i`: the step; `v`: the validator. -/
theorem finalized_ancestorEq_confirmed_of_exec (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (i : ℕ) (v : V)
    (_hH : x.HonestThrough A i v) :
    (x.st i v).finalized.AncestorEq (M.ac_confirmed (x.st i v)) :=
  (finalized_ancestorEq_ac_confirmed M F) _

/-- The finalized block only extends, the proof; the audited statement is in
`Record/Restated/Statements/Executions/OutputOrderStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `A`: the activity; `x`: the trace; `R`: the run's facts (no promise of the
  environment is read); `v`: the validator; `i ≤ j`: the two steps. -/
theorem finalized_only_extends_of_exec (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (v : V) (i j : ℕ) (hij : i ≤ j)
    (_hH : x.HonestThrough A j v) :
    (x.st i v).finalized.AncestorEq (x.st j v).finalized :=
  (F_ancestorEq_of_le_of_tickActive M F) x R v hij

end GoldilocksCorrectness.Record.Proofs.Executions
