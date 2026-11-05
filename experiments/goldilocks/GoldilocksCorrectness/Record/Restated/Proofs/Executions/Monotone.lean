module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Steps
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Node
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Wiring
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ACStore
public import GoldilocksCorrectness.Record.Wiring
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements

@[expose] public section

/-!
# Monotone, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Monotone.lean` that read an execution, over
a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: a node state only grows
(`TreeGrows`, read through the record's node readers) across each step of the node, from the facts
of the tick (`F.tk.tick_step`), of the receipt (`receive_grows`) and of the wake
(`F.wk.wake_readers`); across each step of the sts framework's atomic semantics; and from any step
to any later one, so that the votes held, the tree, the finalized block's chain and the stamps are
kept. The page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.bind_any DREBPost.dite
  DREBPost.ite DREBPost.liftM DREBPost.of_outcome DREBPost.pure DREPost forIn_yield_inv
  fun_getElem)

open GoldilocksCorrectness.Proofs.Routines (fg_on_attestation_keeps fg_on_block_F fg_on_block_eq)

open GoldilocksCorrectness.Proofs.Routines (ac_on_block_grows ac_on_tick_grows
  on_goldfish_vote_grows)

open GoldilocksCorrectness.Proofs.Routines (on_ac_message_grows on_attestation_grows
  on_block_grows tick_grows)

open GoldilocksCorrectness.Proofs.Routines (wake_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Proofs.Routines (SlotKeyed TreeGrows)

open Goldilocks
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans)

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## The relations -/

section Relations

end Relations

/-! ## The AC routines -/

section AC

variable [RootOrder]

end AC

/-! ## The FG routines -/

section FG

variable [RootOrder]

end FG

/-! ## The node -/

section Node

variable [RootOrder]

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

variable [RootOrder]

/-- Every step of the wiring on one event, from a pool filed by slot, grows the node state: a tick
step is an answer of the node's tick or keeps the state, a delivery runs the dispatch, a wake
writes `awakeSince` only.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `p`: the validator; `r`: the reading; `view`: its view; `n`: the node state;
  `e`: the event; `res`: the step result.

Read aloud: every step of the node grows the node state, from votes filed by slot. -/
theorem reaction_grows (S : Setup V) (p : V) (r : ℕ) (view : View V (NamedObject V))
    (n : M.N) (e : Event V (NamedObject V) Empty)
    (res : NodeStepResult (M.N) (NamedObject V))
    (hstep : (protocolOf M S).step p r view n e res) (hk : SlotKeyed M n) :
    TreeGrows M n res.state := by
  cases e with
  | tick =>
      rcases ((GoldilocksCorrectness.Record.step_tick_iff M) S p r view n res).1 hstep with ⟨n', sent, hok, rfl⟩ | ⟨-, rfl⟩
      · exact (F.tk.tick_step S.C S.P S.X n (r : Int) n' sent hok hk).2.1
      · exact (GoldilocksCorrectness.Record.Proofs.Routines.TreeGrows.refl M F) _
  | recv m =>
      rw [((GoldilocksCorrectness.Record.step_recv_iff M) S p r view n m res).1 hstep]
      exact ((GoldilocksCorrectness.Record.Proofs.Routines.receive_grows M F) S.C S.P S.X n m.msg hk).2
  | wake =>
      rw [((GoldilocksCorrectness.Record.step_wake_iff M) S p r view n res).1 hstep]
      exact GoldilocksCorrectness.Record.Proofs.Routines.TreeGrows.of_wake M F n (r : Int)
  | custom ev => exact ev.elim

variable {S : Setup V} {A : Activity V} (x : Trace V (NamedObject V) M.N)

/-- Along a run of the model, every validator's votes are filed by slot at every step: the initial
state's are, a tick and a delivery keep it (`tick_step`, `receive_step`), and so does a restart.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the trace; `R`: the run's facts; `i`: the step; `v`: the validator.

Read aloud: every validator's votes are filed by slot, at every step. -/
theorem slotKeyed_of_run (R : RunFacts M S x) (i : ℕ) (v : V) : SlotKeyed M (x.st i v) := by
  induction i with
  | zero =>
      rw [R.init v]
      exact (GoldilocksCorrectness.Record.Proofs.Routines.SlotKeyed.of_poolKeyed M F)
        (F.nd.nodeInv_poolKeyed (F.nd.initial_nodeInv S.C S.P S.X v))
  | succ i ih =>
      by_cases hv : (∃ t, x.lbl i = Event.tick v t) ∨
          (∃ (tR : ℕ) (keep : Bool), x.lbl i = Event.restart v tR keep) ∨
          ∃ sm, x.lbl i = Event.deliver v sm
      · rcases hv with ⟨t, hl⟩ | ⟨tR, keep, hl⟩ | ⟨sm, hl⟩
        · obtain ⟨n', sent, hok, hst, -⟩ := R.tick i v t hl
          rw [hst]
          exact (F.tk.tick_step S.C S.P S.X _ (t : Int) n' sent hok ih).1
        · rw [(R.restart i v tR keep hl).1]
          exact (GoldilocksCorrectness.Record.Proofs.Routines.slotKeyed_wake M F) ih
        · rw [(R.deliver i v sm hl).2.1]
          exact (F.rcv.receive_step S.C S.P S.X _ sm.msg ih).1
      · push_neg at hv
        rw [R.untouched i v hv.1 hv.2.1 hv.2.2]
        exact ih

/-- Along a trace of the model, every validator's node
state only grows, from any step to any later one.

Why: the pool is filed by slot at every step (Lemma 11, from the run's facts alone), and every
step of the validator grows its node state.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the trace; `R`: the run's facts; `v`: the validator; `i ≤ j`: the two steps.

Read aloud: from a step to a later one, a validator keeps every block and vote it holds with their
stamps, and its finalized block moves only to a descendant. -/
theorem grows_of_le_of_tickActive (R : RunFacts M S x)
    (v : V) {i j : ℕ} (hij : i ≤ j) : TreeGrows M (x.st i v) (x.st j v) := by
  induction j, hij using Nat.le_induction with
  | base => exact (GoldilocksCorrectness.Record.Proofs.Routines.TreeGrows.refl M F) _
  | succ j _ ih =>
      have hk : SlotKeyed M (x.st j v) := (slotKeyed_of_run M F) x R j v
      refine ih.trans ?_
      by_cases hv : (∃ t, x.lbl j = Event.tick v t) ∨
          (∃ (tR : ℕ) (keep : Bool), x.lbl j = Event.restart v tR keep) ∨
          ∃ sm, x.lbl j = Event.deliver v sm
      · rcases hv with ⟨t, hl⟩ | ⟨tR, keep, hl⟩ | ⟨sm, hl⟩
        · obtain ⟨n', sent, hok, hst, -⟩ := R.tick j v t hl
          rw [hst]
          exact (F.tk.tick_step S.C S.P S.X _ (t : Int) n' sent hok hk).2.1
        · rw [(R.restart j v tR keep hl).1]
          exact GoldilocksCorrectness.Record.Proofs.Routines.TreeGrows.of_wake M F _ _
        · rw [(R.deliver j v sm hl).2.1]
          exact ((GoldilocksCorrectness.Record.Proofs.Routines.receive_grows M F)
            S.C S.P S.X _ sm.msg hk).2
      · push_neg at hv
        rw [R.untouched j v hv.1 hv.2.1 hv.2.2]
        exact (GoldilocksCorrectness.Record.Proofs.Routines.TreeGrows.refl M F) _

/-- Along an execution, every validator's node state only grows, from any step to any later one.
The pool is filed by slot at every step (Lemma 11).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `v`: the validator; `i ≤ j`: the two steps.

Read aloud: from a step to a later one, a validator keeps every block and vote it holds with their
stamps, and its finalized block moves only to a descendant. -/
theorem grows_of_le (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (v : V) {i j : ℕ} (hij : i ≤ j) : TreeGrows M (x.st i v) (x.st j v) := by
  exact (grows_of_le_of_tickActive M F) x R v hij

/-- The node state before a time grows with the time.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `v`: the validator; `t ≤ t'`: the two times.

Read aloud: `v`'s node state before a later time holds every block and vote its node state before
an earlier time holds, with the same stamps. -/
theorem stateBefore_grows (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (v : V) {t t' : ℕ} (h : t ≤ t') :
    TreeGrows M (x.stateBefore t v) (x.stateBefore t' v) :=
  (grows_of_le M F) x R E v ((stepBefore_mono M) x R E h)

/-- A vote of a validator's pool of a slot stays in it at every later step.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `v`: the validator; `i ≤ j`: the two steps; `s`: the slot.

Read aloud: a vote a validator holds under a slot stays held at every later step. -/
theorem pool_mono (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (v : V) {i j : ℕ} (hij : i ≤ j) (s : Slot) :
    M.votesHeldSet (x.st i v) s ⊆ M.votesHeldSet (x.st j v) s := fun _ hv =>
  ((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).2 ((((grows_of_le M F) x R E v hij).2.2.1 s).subset (((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).1 hv))

/-- A block of a validator's tree stays in it at every later step.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `v`: the validator; `i ≤ j`: the two steps.

Read aloud: a block of a validator's tree stays in it at every later step. -/
theorem mem_T_mono (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (v : V) {i j : ℕ} (hij : i ≤ j) : (x.st i v).tree ⊆ (x.st j v).tree :=
  ((grows_of_le M F) x R E v hij).1

/-- Along a trace of the model, a validator's
finalized block at a step is an ancestor of its finalized block at every later step, or that block.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the trace; `R`: the run's facts; `v`: the validator; `i ≤ j`: the two steps.

Read aloud: a validator's finalized block moves only to a descendant. -/
theorem F_ancestorEq_of_le_of_tickActive (R : RunFacts M S x)
    (v : V) {i j : ℕ} (hij : i ≤ j) :
    (x.st i v).finalized.AncestorEq (x.st j v).finalized :=
  ((grows_of_le_of_tickActive M F) x R v hij).2.1

/-- A validator's finalized block at a step is an ancestor of its finalized block at every later
step, or that block.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `v`: the validator; `i ≤ j`: the two steps.

Read aloud: a validator's finalized block moves only to a descendant. -/
theorem F_ancestorEq_of_le (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (v : V) {i j : ℕ} (hij : i ≤ j) :
    (x.st i v).finalized.AncestorEq (x.st j v).finalized := by
  exact ((grows_of_le M F) x R E v hij).2.1

/-- The stamp of a block of a validator's tree is the same at every later step.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `v`: the validator; `i ≤ j`: the two steps; `B`: the block.

Read aloud: the stamp of a block of the tree is kept at every later step. -/
theorem blockStamp_kept (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (v : V) {i j : ℕ} (hij : i ≤ j) {B : Block V}
    (hB : B ∈ (x.st i v).tree) :
    (x.st j v).blockStamp B = (x.st i v).blockStamp B :=
  ((grows_of_le M F) x R E v hij).2.2.2.1 B hB

/-- The stamp of a vote of a validator's pool is the same at every later step.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `v`: the validator; `i ≤ j`: the two steps; `s`: the slot; `vote`: the
  vote.

Read aloud: the stamp of a vote held is kept at every later step. -/
theorem voteStamp_kept (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (v : V) {i j : ℕ} (hij : i ≤ j) {s : Slot} {vote : GoldfishVote V}
    (hv : vote ∈ M.votesHeldSet (x.st i v) s) :
    (x.st j v).voteStamp vote = (x.st i v).voteStamp vote :=
  ((grows_of_le M F) x R E v hij).2.2.2.2 s vote (((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).1 hv)

/-- **Kit fact, a block held after `i` steps is held by the time of step `i`.** When `v` is
outside the adversary set at step `i`, at a time at most `t`, and holds `B` after `i` steps, `B` is
held by `t`: the state step `i`
leaves holds `B` too, since the tree only grows (`mem_T_mono`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the condition on executions; `t`: the bound on
  the time; `i`: the step; `v`: the validator; `B`: the block.

Read aloud: a block an honest validator holds after a step at a time at most `t` is held by `t`. -/
theorem inHonestTreeBy_of_st (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {t : ℝ} {i : ℕ} {v : V} {B : Block V}
    -- `v` is outside the adversary set at step `i`
    (hv : v ∉ A.corrupted i)
    -- step `i` is at a time at most `t`
    (ht : x.time i ≤ t)
    -- `v` holds `B` after `i` steps
    (hB : B ∈ (x.st i v).tree) :
    inHonestTreeBy M A x t B :=
  ⟨i, v, hv, ht, (mem_T_mono M F) x R E v (Nat.le_succ i) hB⟩

/-- **Kit fact, a step leaves every state as it was, or keeps the time and the adversary set.** A
step of the kind `other` is no tick, restart or delivery of any validator, so it leaves every node
state as it was (`RunFacts.untouched`); a tick, a restart or a delivery keeps the time
(`RunFacts.time_keep`) and the adversary set (`corrupted_keep`, a field of the condition on
executions `EnvFactsBy`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the condition on executions; `j`: the step.

Read aloud: step `j` is of the kind `other` and leaves every validator's state as it was, or it
keeps the time and the adversary set. -/
theorem step_succ_cases (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (j : ℕ) :
    (x.lbl j = Event.other ∧ ∀ v : V, x.st (j + 1) v = x.st j v) ∨
      (x.time (j + 1) = x.time j ∧ A.corrupted (j + 1) = A.corrupted j) := by
  by_cases hl : x.lbl j = Event.other
  · refine Or.inl ⟨hl, fun v => ?_⟩
    exact R.untouched j v (fun t h => by rw [hl] at h; cases h)
      (fun t k h => by rw [hl] at h; cases h) (fun sm h => by rw [hl] at h; cases h)
  · exact Or.inr ⟨R.time_keep j hl, E.corrupted_keep j hl⟩

/-- **Kit fact, a block held by `t` is held at some step.** A block an honest validator holds in the
state some step at a time at most `t` leaves (`inHonestTreeBy`) is held by a validator outside the
adversary set after some step (`inHonestTree`): the state step `i` leaves is the one before it, or
the adversary set after step `i` is the one at step `i` (`step_succ_cases`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the condition on executions; `t`: the bound on
  the time; `B`: the block.

Read aloud: a block held by `t` is held by an honest validator at some step. -/
theorem inHonestTree_of_inHonestTreeBy (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {t : ℝ} {B : Block V} (hB : inHonestTreeBy M A x t B) : inHonestTree M A x B := by
  obtain ⟨i, v, hv, -, hBT⟩ := hB
  rcases (step_succ_cases M F) x R E i with ⟨-, h⟩ | ⟨-, hc⟩
  · exact ⟨i, v, hv, by rw [← h v]; exact hBT⟩
  · exact ⟨i + 1, v, show v ∉ A.corrupted (i + 1) by rw [hc]; exact hv, hBT⟩

end Execution

end GoldilocksCorrectness.Record.Proofs.Executions

