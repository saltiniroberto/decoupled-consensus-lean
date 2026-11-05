module
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Proofs.Executions.Invariants
public import GoldilocksCorrectness.Proofs.Executions.Steps
public import GoldilocksCorrectness.Proofs.Routines.NoRaise
public import GoldilocksCorrectness.Proofs.Routines.ACInterfaceTick
public import GoldilocksCorrectness.Proofs.Routines.ACStore
public import GoldilocksCorrectness.Proofs.Routines.ConfirmationSupporters
public import GoldilocksCorrectness.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Proofs.Routines.RevokeLocks
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.NodeTick

@[expose] public section

/-!
# The tick never fails

The routines that read the pool's stamps answer when every vote of the pool is stamped
(`PoolStamped`): the revocation of the locks, the confirmation update, the Goldfish vote duty, the
tick of the available chain, its proposal and the source it hands the finality gadget. On a node
state satisfying the node invariant `NodeInv`, the proposal, the attestation duty and the tick
answer (`tick_ok`); with Lemma 11, the tick of every honest awake validator answers in every
execution (`ticksSucceed_of_exec`).
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (PoolStamped)

open GoldilocksCorrectness.Statements.Routines (NodeInv)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol DREBOutcomesOk)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn)
open GoldilocksCorrectness.Proofs.Routines

variable {V : Type} [DecidableEq V] [Fintype V]

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
- `S`: the setup; `Sched`: the schedule; `x`: the execution. -/
theorem ticksSucceed_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) : TicksSucceed S Sched x := by
  intro i t v hl _ _
  have hI := GoldilocksCorrectness.Statements.Executions.lem11_node_invariant S Sched x i v
  have hN : NodeInv S.C S.P S.X (tickInputState x i t v) := by
    unfold tickInputState
    split
    · exact (wake_nodeInv S.C S.P S.X _ _ hI.1 hI.2.2).1
    · exact hI.1
  have hle : (tickInputState x i t v).t ≤ (t : Int) := by
    have h2 : ((x[i][v].clock : ℕ) : Int) ≤ ((x[i].time : ℕ) : Int) := by
      exact_mod_cast Framework.StsMultisetLog.atomic_clock_le_time x i v
    have h3 : ((x[i].time : ℕ) : Int) + 1 = (t : Int) := by
      exact_mod_cast (time_of_lbl_tickAllAwake x hl).1
    have h4 : ((x[i].time : ℕ) : Int) ≤ (t : Int) := by
      rw [← h3]; exact Int.le_add_one (le_refl _)
    -- a wake sets the clock to the framework's clock, which is at most `t`
    unfold tickInputState
    split
    · rw [wake_eq]; exact le_trans h2 h4
    · exact le_trans hI.2.2 (le_trans h2 h4)
  exact DREBOutcomesOk.of_run_ok (tick_ok S.C S.P S.X _ (t : Int) hN hle [])

end Execution

end GoldilocksCorrectness.Proofs.Executions
