module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.NoRaise
public import GoldilocksCorrectness.Statements.Routines.NoRaiseStatements

@[expose] public section

/-!
# NoRaiseStatements, over a model

The statement of `GoldilocksCorrectness/Statements/Executions/NoRaiseStatements.lean` over a model
`M` whose facts `F` hold, for an execution `x` of `protocolOf M S`, proved in
`Record/Restated/Proofs/Executions/NoRaise.lean`: every execution satisfies `TicksSucceed`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Proofs.Routines (DREBOk)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Every execution satisfies `TicksSucceed`.** At every step that is the tick of every awake
validator at a time `t`, the tick of every validator awake and outside the adversary set at `t`
answers, from the node state it starts from.

Why: Lemma 11 (`lem11_node_invariant`) gives `NodeInv` of the node state before the step, a wake
keeps it, and the node's clock is at most the time of the tick; then `tick_ok`. Awakeness and
honesty are not used.

Read aloud: an honest awake validator's tick never fails, in every execution.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `Sched`: the schedule; `x`: the execution. -/
theorem ticksSucceed_of_exec (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) : TicksSucceed M S A x :=
  (GoldilocksCorrectness.Record.Proofs.Executions.ticksSucceed_of_exec M F) S A x R E

end GoldilocksCorrectness.Record.Statements.Executions

