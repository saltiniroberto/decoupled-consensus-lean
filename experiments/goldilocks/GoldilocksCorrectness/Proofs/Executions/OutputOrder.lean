module
public import GoldilocksCorrectness.Statements.Executions.UnforgeabilityDefs
public import GoldilocksCorrectness.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Proofs.Executions.Monotone
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders

@[expose] public section

/-!
# The order of a validator's two outputs, the proofs

The audited statements are in `Statements/Executions/OutputOrderStatements.lean`:

- `finalized_ancestorEq_confirmed_of_exec`: the finalized block is the confirmed tip or an ancestor
  of it;
- `finalized_only_extends_of_exec`: the finalized block at a step is the finalized block at every
  later step or an ancestor of it.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (confirmedOf ac_confirmed_cases)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl mem_fg_to_ac_tree fg_to_ac_F)

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- A node state's finalized block is its confirmed tip or an ancestor of it.

Why: the confirmed tip is the record `n.A.latest_confirmed` when the record is in the tree of the
frame `fg_to_ac n.S`, whose blocks all have the finalized block as an ancestor or are it; and it
is the finalized block otherwise.

The variables:
- `n`: the node state. -/
theorem F_ancestorEq_confirmedOf [RootOrder] (n : NodeState V) :
    n.S.F.AncestorEq (confirmedOf n) := by
  unfold confirmedOf
  rcases ac_confirmed_cases n.A (fg_to_ac n.S) with ⟨hin, h⟩ | ⟨-, h⟩
  · rw [h]
    exact ((mem_fg_to_ac_tree n.S _).1 hin).2
  · rw [h, fg_to_ac_F]
    exact ancestorEq_refl n.S.F

variable [RootOrder]

/-- The finalized block is the confirmed tip or an ancestor of it, the proof; the audited
statement is in `Statements/Executions/OutputOrderStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator. -/
theorem finalized_ancestorEq_confirmed_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V)
    (_hH : HonestThrough x i v) :
    (x[i][v].st).S.F.AncestorEq (confirmedOf (x[i][v].st)) :=
  F_ancestorEq_confirmedOf _

/-- The finalized block only extends, the proof; the audited statement is in
`Statements/Executions/OutputOrderStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `v`: the validator; `i ≤ j`: the two
  steps. -/
theorem finalized_only_extends_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (v : V) (i j : ℕ) (hij : i ≤ j)
    (_hH : HonestThrough x j v) :
    (x[i][v].st).S.F.AncestorEq (x[j][v].st).S.F :=
  F_ancestorEq_of_le x v hij

end GoldilocksCorrectness.Proofs.Executions
