module
public import GoldilocksCorrectness.Proofs.Executions.NoRaise
public import GoldilocksCorrectness.Statements.Routines.NoRaiseStatements

@[expose] public section

/-!
# The statements that the tick never fails

The tick answers on every node state satisfying the node invariant `NodeInv`, at a time no earlier
than the node's clock (`tick_ok`), and so every execution satisfies `TicksSucceed`: the tick of
every honest awake validator answers (`ticksSucceed_of_exec`). Both are proved in
`GoldilocksCorrectness/Proofs/Executions/NoRaise.lean`. A duty `m` answers, `DREBOk m`, when from
every list of objects sent so far it returns a value and the objects it has sent rather than
failing (`GoldilocksCorrectness/Proofs/Routines/NoRaise.lean`).
-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Proofs.Routines (DREBOk)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Every execution satisfies `TicksSucceed`.** At every step that is the tick of every awake
validator at a time `t`, the tick of every validator awake and outside the adversary set at `t`
answers, from the node state it starts from.

Why: Lemma 11 (`lem11_node_invariant`) gives `NodeInv` of the node state before the step, a wake
keeps it, and the node's clock is at most the time of the tick; then `tick_ok`. Awakeness and
honesty are not used.

Read aloud: an honest awake validator's tick never fails, in every execution.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution. -/
theorem ticksSucceed_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) : TicksSucceed S Sched x :=
  GoldilocksCorrectness.Proofs.Executions.ticksSucceed_of_exec S Sched x

end GoldilocksCorrectness.Statements.Executions
