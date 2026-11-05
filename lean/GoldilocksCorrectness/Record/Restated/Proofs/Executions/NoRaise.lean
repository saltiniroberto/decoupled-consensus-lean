module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Invariants
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Steps
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ExecutionDefs
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements

@[expose] public section

/-!
# NoRaise, over a model

The theorem of `GoldilocksCorrectness/Proofs/Executions/NoRaise.lean` that reads an execution, over
a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: every execution
satisfies `TicksSucceed`, the tick of every honest awake validator having an outcome and no failing
one, from Lemma 11 and the field `tick_ok` of `F.nd`. The page's routine-level theorems are the
fields `tick_ok` and `tick_nodeInv`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (NodeInv)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (DREBOutcomesOk)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn)
open GoldilocksCorrectness.Record.Proofs.Routines

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## The routines that read the pool's stamps -/

section Routines

variable [RootOrder]

-- The filter `{vote ∈ᴹ s | (← resolved Φ.tree vote)}` elaborates to `filterM (resolved Φ.tree) s`
-- with no bind: the first alternative of its `first` closes it, and the second is never run.

end Routines

/-! ## The node -/

section Node

variable [RootOrder]

end Node

/-! ## Every execution -/

section Execution

variable [RootOrder]

/-- **Every execution satisfies `TicksSucceed`**: at every step that is the tick of every awake
validator at a time `t`, the tick of every validator awake and outside the adversary set at `t`
answers, from the node state it starts from.

Why: Lemma 11 (`lem11_node_invariant`) gives `NodeInv` of the node state before the step, a wake
keeps it (`wake_nodeInv`), and the node's clock is at most the framework's clock, which is at most
the time `t − 1` of the step; a tick from a node state satisfying `NodeInv`, at a time no earlier
than its clock, answers (`tick_ok`). Awakeness and honesty are not used.

Read aloud: an honest awake validator's tick never fails, in every execution.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `Sched`: the schedule; `x`: the execution. -/
theorem ticksSucceed_of_exec (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) : TicksSucceed M S A x := by
  intro i t v hl hact
  have hv : v ∉ A.corrupted i := Activity.not_mem_corrupted_of_mem_active hact
  have hts := (tickStep_eq_of_lbl M) x E hl
  have hI := (GoldilocksCorrectness.Record.Statements.Executions.lem11_node_invariant M F)
    S A x R E.noDelivery i v hv
  have hin : x.tickInput v t = x.st i v := by
    unfold Trace.tickInput
    rw [hts]
  rw [hin]
  -- the clock value before the tick was set by an earlier tick or restart of `v`, to a value at most `t`
  -- (`clock_mono`), or is the initial `0`
  have hcl : x.clockValue i v ≤ t := by
    rcases x.clockValue_cases i v with ⟨h0, -⟩ | ⟨j, hj, hset, -⟩
    · rw [h0]; exact Nat.zero_le _
    · exact E.clock_mono j i v _ t hj hv hset (Or.inl hl)
  have hle : (x.st i v).t ≤ (t : Int) := by rw [hI.2.2]; exact_mod_cast hcl
  obtain ⟨⟨r, hr⟩, hne⟩ := F.nd.tick_ok S.C S.P S.X _ (t : Int) hI.1 hle
  refine ⟨fun r' hr' => ?_, ⟨r, hr⟩⟩
  cases r' with
  | ok p => exact ⟨p, rfl⟩
  | error e => exact absurd hr' (hne e)

end Execution

end GoldilocksCorrectness.Record.Proofs.Executions

