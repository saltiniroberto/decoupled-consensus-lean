module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Monotone
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Node
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.FGStateDefs

@[expose] public section

/-!
# FinalizedFromChain, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/FinalizedFromChain.lean` over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: `FinalizedFrom` carries
`FinalizedFromChain` from a node state to the next; each step of the node and of the atomic
semantics relates a node state satisfying the model's node invariant to the next by `FinalizedFrom`
(the fields `tick_finalizedFrom` of `F.tk` and `receive_finalizedFrom` of `F.rcv` read the invariant
where the landed routine-level theorems read that the stored chain states are the blocks' own); and
every validator's finalized block is the finalized block of the chain state of a block of its tree,
at every step.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.bind_any DREBPost.dite
  DREBPost.ite DREBPost.of_outcome DREBPost.pure)

open GoldilocksCorrectness.Proofs.Routines (fg_on_attestation_keeps fg_on_block_F_cases
  fg_on_block_eq)

open GoldilocksCorrectness.Proofs.Routines (on_attestation_frame_S on_block_finalizedFrom
  tick_finalizedFrom)

open GoldilocksCorrectness.Proofs.Routines (wake_eq)

open GoldilocksCorrectness.Proofs.Routines (receive_finalizedFrom)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Proofs.Routines (FinalizedFrom)
open GoldilocksCorrectness.Record.Statements.Routines (ChainStatesComputed FinalizedFromChain)

open Goldilocks
open GoldilocksCorrectness.Record.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## The relation -/

section Relation

omit [RootOrder] in
/-- `FinalizedFrom` carries `FinalizedFromChain` from the first node state's FG state to the
second's.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `n`, `n'`: the two node states.

Read aloud: `FinalizedFrom` carries `FinalizedFromChain` forward. -/
theorem finalizedFromChain_of_finalizedFrom (C : Config) {n n' : M.N}
    (h : FinalizedFromChain M C n) (hr : FinalizedFrom M C n n') : FinalizedFromChain M C n' := by
  obtain ⟨B, hB, hBF⟩ := h
  obtain ⟨hT, hF⟩ := hr
  rcases hF with hF | ⟨B', hB', hBF'⟩
  · exact ⟨B, hT hB, hF.trans hBF⟩
  · exact ⟨B', hB', hBF'⟩

end Relation

/-! ## The FG routines -/

section FG

end FG

/-! ## The node -/

section Node

end Node

/-! ## The reactions and the steps -/

section Execution

open Framework.StsMultisetLog (AtomicStep Event TickAllAwakeWake tickAllAwakeUpdate_getElem_react tickAllAwakeUpdate_getElem_st_of_not_react applyNodeStepResult_getElem receive_getElem NodeStepResult View)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks.Sts (Setup)

/-- Every step of the wiring on one event, from a node state whose chain states of its tree are
the blocks' own, relates the node state to the step's state: a tick step is an answer of the
node's tick or keeps the state, a delivery runs the dispatch, a wake writes `awakeSince` only.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `p`: the validator; `r`: the reading; `view`: its view; `n`: the node state;
  `e`: the event; `res`: the step result.

Read aloud: every step of the node relates a node state satisfying the invariant to the next by
`FinalizedFrom`. -/
theorem reaction_finalizedFrom (S : Setup V) (p : V) (r : ℕ) (view : View V (NamedObject V))
    (n : M.N) (e : Event V (NamedObject V) Empty)
    (res : NodeStepResult (M.N) (NamedObject V))
    (hstep : (protocolOf M S).step p r view n e res)
    -- `n` satisfies the model's node invariant
    (hI : M.nodeInv S.C S.P S.X n) :
    FinalizedFrom M S.C n res.state := by
  cases e with
  | tick =>
      rcases ((GoldilocksCorrectness.Record.step_tick_iff M) S p r view n res).1 hstep with ⟨n', sent, hok, rfl⟩ | ⟨-, rfl⟩
      · exact F.tk.tick_finalizedFrom S.C S.P S.X n (r : Int) n' sent hok (F.nd.nodeInv_core hI)
      · exact (GoldilocksCorrectness.Record.Proofs.Routines.finalizedFrom_refl M F) S.C _
  | recv m =>
      rw [((GoldilocksCorrectness.Record.step_recv_iff M) S p r view n m res).1 hstep]
      exact F.rcv.receive_finalizedFrom S.C S.P S.X n m.msg (F.nd.nodeInv_core hI)
  | wake =>
      rw [((GoldilocksCorrectness.Record.step_wake_iff M) S p r view n res).1 hstep]
      exact (GoldilocksCorrectness.Record.Proofs.Routines.finalizedFrom_of_frame M F) S.C
        (F.wk.wake_readers n _).2.2.1 (F.wk.wake_readers n _).2.2.2.1
  | custom ev => exact ev.elim

/-- At every step of a trace of the model, every validator's finalized block is the finalized block of
the chain state of a block of its tree.

Why: by induction on the step; the initial node state satisfies it, and every step relates the node
state before to the node state after, the chain states of the tree before being the blocks' own
(the clock-free part of Lemma 11, from the run's facts alone).

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `x`: the trace; `R`: the run's facts; `i`: the step; `v`: the validator.

Read aloud: at every step, every validator's finalized block is the finalized block of the chain
state of a block of its tree. -/
theorem finalizedFromChain_of_run (S : Setup V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (i : ℕ) (v : V) :
    FinalizedFromChain M S.C (x.st i v) := by
  induction i with
  | zero =>
      rw [R.init v]
      exact (GoldilocksCorrectness.Record.Proofs.Routines.initial_finalizedFromChain M F) S.C v
  | succ i ih =>
      have hI := (lem11_node_invariantCore_of_run M F S x R i v).1
      refine (finalizedFromChain_of_finalizedFrom M F) S.C ih ?_
      by_cases hv : (∃ t, x.lbl i = Event.tick v t) ∨
          (∃ (tR : ℕ) (keep : Bool), x.lbl i = Event.restart v tR keep) ∨
          ∃ sm, x.lbl i = Event.deliver v sm
      · rcases hv with ⟨t, hl⟩ | ⟨tR, keep, hl⟩ | ⟨sm, hl⟩
        · obtain ⟨n', sent, hok, hst, -⟩ := R.tick i v t hl
          rw [hst]
          exact F.tk.tick_finalizedFrom S.C S.P S.X _ (t : Int) n' sent hok hI
        · rw [(R.restart i v tR keep hl).1]
          exact (GoldilocksCorrectness.Record.Proofs.Routines.finalizedFrom_of_frame M F) S.C
            (F.wk.wake_readers _ _).2.2.1 (F.wk.wake_readers _ _).2.2.2.1
        · rw [(R.deliver i v sm hl).2.1]
          exact F.rcv.receive_finalizedFrom S.C S.P S.X _ sm.msg hI
      · push_neg at hv
        rw [R.untouched i v hv.1 hv.2.1 hv.2.2]
        exact (GoldilocksCorrectness.Record.Proofs.Routines.finalizedFrom_refl M F) S.C _

/-- At every step of every execution, every validator's finalized block is the finalized block
of the chain state of a block of its tree. By induction on the step: the initial node state
satisfies it, and every step relates the node state before to the node state after, the chain
states of the tree before being the blocks' own (Lemma 11).

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `i`: the step; `v`: the
  validator.

Read aloud: at every step, every validator's finalized block is the finalized block of the chain
state of a block of its tree. -/
theorem finalizedFromChain_of_exec (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    FinalizedFromChain M S.C (x.st i v) := by
  induction i with
  | zero =>
      rw [R.init v]
      exact (GoldilocksCorrectness.Record.Proofs.Routines.initial_finalizedFromChain M F) S.C v
  | succ i ih =>
      have hI := ((lem11_node_invariantCore_of_run M F) S x R i v).1
      refine (finalizedFromChain_of_finalizedFrom M F) S.C ih ?_
      by_cases hv : (∃ t, x.lbl i = Event.tick v t) ∨
          (∃ (tR : ℕ) (keep : Bool), x.lbl i = Event.restart v tR keep) ∨
          ∃ sm, x.lbl i = Event.deliver v sm
      · rcases hv with ⟨t, hl⟩ | ⟨tR, keep, hl⟩ | ⟨sm, hl⟩
        · obtain ⟨n', sent, hok, hst, -⟩ := R.tick i v t hl
          rw [hst]
          exact F.tk.tick_finalizedFrom S.C S.P S.X _ (t : Int) n' sent hok hI
        · rw [(R.restart i v tR keep hl).1]
          exact (GoldilocksCorrectness.Record.Proofs.Routines.finalizedFrom_of_frame M F) S.C
            (F.wk.wake_readers _ _).2.2.1 (F.wk.wake_readers _ _).2.2.2.1
        · rw [(R.deliver i v sm hl).2.1]
          exact F.rcv.receive_finalizedFrom S.C S.P S.X _ sm.msg hI
      · push_neg at hv
        rw [R.untouched i v hv.1 hv.2.1 hv.2.2]
        exact (GoldilocksCorrectness.Record.Proofs.Routines.finalizedFrom_refl M F) S.C _

end Execution

end GoldilocksCorrectness.Record.Proofs.Executions

