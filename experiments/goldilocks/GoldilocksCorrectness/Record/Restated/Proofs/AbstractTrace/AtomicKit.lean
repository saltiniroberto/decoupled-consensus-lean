module
public import GoldilocksCorrectness.Record.Facts
public import GoldilocksCorrectness.Record.Wiring
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.NodeDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.RecordDefs
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.AtomicReaders

@[expose] public section

/-!
# The sts framework's atomic run: the facts `OfAtomic.lean` reads

The theorems over an execution `x` of the model's node `protocolOf M S` under the sts framework's
atomic semantics that `Record/Restated/Proofs/AbstractTrace/OfAtomic.lean` reads to show that the
unfolding `ofAtomic M x` is a run of the model's node: Lemma 11 over the atomic run (every node state
satisfies the node invariant, has its validator, and has a clock at most the framework's), the times
of the tick of every awake validator, and `ticksSucceed_of_exec` (the tick of every honest awake
validator answers). They are the proofs the record execution pages carried over the atomic run
before those pages were stated over a trace (phase D), kept unchanged for the bridges.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.bind_any DREBPost.dite
  DREBPost.ite DREBPost.liftM DREBPost.of_outcome DREBPost.pure DREPost DREPost.bind_any
  DREPost.dite DREPost.ite DREPost.pure ancestors_mem forIn_yield_inv fun_getElem ok_of_bind_eq_ok)

open GoldilocksCorrectness.Proofs.Routines (fg_attest_eq fg_on_attestation_caches
  fg_on_attestation_h_j fg_on_attestation_keeps fg_on_block_eq
  fg_on_block_finalizedAncestorJustified fg_on_block_heightCacheBounds fg_on_block_justification
  fg_on_block_justified update_finality_attestations)

open GoldilocksCorrectness.Proofs.Routines (ac_on_block_timestamp_block ac_on_block_votesInv
  ac_on_tick_votesInv on_goldfish_vote_timestamp_block on_goldfish_vote_votesInv)

open GoldilocksCorrectness.Proofs.Routines (initial_nodeInv on_ac_message_nodeInv
  on_attestation_nodeInv on_block_nodeInv tick_nodeInv wake_nodeInv)
open GoldilocksCorrectness.Statements.Routines (NodeInv)

open GoldilocksCorrectness.Proofs.Routines (initial_eq)

open GoldilocksCorrectness.Proofs.Routines (receive_nodeInv)

namespace GoldilocksCorrectness.Record.Proofs.AbstractTrace.Atomic

open GoldilocksCorrectness.Record.Statements.Routines (LockBelowJustified RecordConsistent)
open Goldilocks
open GoldilocksCorrectness.Record.Statements.AbstractTrace.Atomic (stepBefore stateBefore tickInputState
  TicksSucceed)

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V) (F : Facts M)

section Times

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule atomic_time_stepwise)
open Goldilocks.Sts (Setup)

variable [RootOrder] {S : Setup V} {Sched : Schedule V} (x : AtomicExec (protocolOf M S) Sched)

/-- A step's configuration is at the time of the configuration before it, or later.

The variables:
- `M`: the model;
- `x`: the execution; `i`: the step.

Read aloud: time never goes back from one step to the next. -/
theorem time_le_succ (i : ℕ) : x[i].time ≤ x[i + 1].time := by
  rcases atomic_time_stepwise x i with h | h <;> omega

/-- The tick of every awake validator at `t` is enabled at the time `t − 1` and moves the time to
`t`.

The variables:
- `M`: the model;
- `x`: the execution; `i`: the step; `t`: the time of the tick.

Read aloud: the step that ticks every awake validator at `t` starts at `t − 1` and ends at `t`. -/
theorem time_of_lbl_tickAllAwake {i t : ℕ} (hl : x.lbl i = AtomicAction.tickAllAwake t) :
    x[i].time + 1 = t ∧ x[i + 1].time = t := by
  have hs := x.step i
  rw [hl] at hs
  obtain ⟨hen, w, tk, -, -, hc⟩ := hs
  refine ⟨hen, ?_⟩
  show (x.cfg (i + 1)).time = t
  rw [hc]
  rfl

end Times

include F

section Execution

open Framework.StsMultisetLog (AtomicAction AtomicExec AtomicStep Event Schedule TickAllAwakeWake
  tickAllAwakeUpdate_getElem_react tickAllAwakeUpdate_getElem_st_of_not_react
  tickAllAwakeUpdate_clock_awake tickAllAwakeUpdate_getElem_asleep applyNodeStepResult_getElem
  receive_getElem atomic_clock_le_time NodeStepResult View SignedMsg)
open Goldilocks.Sts (Setup)

variable [RootOrder]

/-- A tick step at a reading `r` no earlier than the node's clock keeps `NodeInv` and the
validator, and leaves a clock at most `r`: an answer of the tick sets the clock to `r`, and the
step that keeps the state keeps it.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `p`: the validator; `r`: the reading; `view`: its view; `n`: the node state;
  `res`: the step result.

Read aloud: a tick step at a reading no earlier than the clock keeps the invariant and the
validator, and leaves a clock at most the reading. -/
theorem reaction_tick_nodeInv (S : Setup V) (p : V) (r : ℕ) (view : View V (NamedObject V))
    (n : M.N) (res : NodeStepResult (M.N) (NamedObject V))
    (hstep : (protocolOf M S).step p r view n .tick res)
    (h : M.nodeInv S.C S.P S.X n) (hr : n.t ≤ (r : Int)) :
    M.nodeInv S.C S.P S.X res.state ∧ res.state.v = n.v ∧ res.state.t ≤ (r : Int) := by
  rcases ((GoldilocksCorrectness.Record.step_tick_iff M) S p r view n res).1 hstep with ⟨n', sent, hok, rfl⟩ | ⟨-, rfl⟩
  · obtain ⟨h1, h2, h3⟩ := F.nd.tick_nodeInv S.C S.P S.X n (r : Int) h hr n' sent hok
    exact ⟨h1, h2, h3.le⟩
  · exact ⟨h, rfl, hr⟩

/-- A wake step at a reading no earlier than the clock keeps `NodeInv` and the validator, and sets
the clock to the reading.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `p`: the validator; `r`: the reading; `view`: its view; `n`: the node state;
  `res`: the step result.

Read aloud: a wake step keeps the invariant and the validator and sets the clock to the reading. -/
theorem reaction_wake_nodeInv (S : Setup V) (p : V) (r : ℕ) (view : View V (NamedObject V))
    (n : M.N) (res : NodeStepResult (M.N) (NamedObject V))
    (hstep : (protocolOf M S).step p r view n .wake res) (h : M.nodeInv S.C S.P S.X n)
    -- the node's clock is at most the reading
    (hr : n.t ≤ (r : Int)) :
    M.nodeInv S.C S.P S.X res.state ∧ res.state.v = n.v ∧ res.state.t = (r : Int) := by
  rw [((GoldilocksCorrectness.Record.step_wake_iff M) S p r view n res).1 hstep]
  exact F.nd.wake_nodeInv S.C S.P S.X n (r : Int) h hr

/-- A delivery step keeps `NodeInv`, the validator and the clock.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `p`: the validator; `r`: the reading; `view`: its view; `n`: the node state;
  `m`: the signed message delivered; `res`: the step result.

Read aloud: a delivery step keeps the invariant, the validator and the clock. -/
theorem reaction_recv_nodeInv (S : Setup V) (p : V) (r : ℕ) (view : View V (NamedObject V))
    (n : M.N) (m : SignedMsg V (NamedObject V))
    (res : NodeStepResult (M.N) (NamedObject V))
    (hstep : (protocolOf M S).step p r view n (.recv m) res) (h : M.nodeInv S.C S.P S.X n) :
    M.nodeInv S.C S.P S.X res.state ∧ res.state.v = n.v ∧ res.state.t = n.t := by
  rw [((GoldilocksCorrectness.Record.step_recv_iff M) S p r view n m res).1 hstep]
  exact F.nd.receive_nodeInv S.C S.P S.X n m.msg h

/-- Every step of the atomic semantics keeps, for each validator `v`, `NodeInv` of its node
state, the node's validator field `v`, and a node clock at most the framework's clock, given the
framework's clock at most the configuration's time. At the tick of every awake validator, a
validator that reacts runs its wake reaction (when it enters the awake set) and its tick reaction
at the new time; a validator that does not react keeps its state, with a clock no earlier. At a
delivery, the receiver runs its reaction to the delivered message. No other action changes a
state.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `Sched`: the schedule; `a`: the action; `c`, `c'`: the configurations before
  and after; `v`: the validator.

Read aloud: every step of the framework keeps, for each validator, the invariant, the validator
field and a node clock at most the framework's. -/
theorem atomicStep_nodeInv {S : Setup V} {Sched : Schedule V}
    {a : AtomicAction V (NamedObject V) Empty}
    {c c' : Framework.StsMultisetLog.Config V (NamedObject V) (M.N)}
    (hstep : AtomicStep (protocolOf M S) Sched a c c') (v : V)
    (h : M.nodeInv S.C S.P S.X c[v].st ∧ (c[v].st).v = v ∧ (c[v].st).t ≤ (c[v].clock : Int))
    -- the framework's clock of `v` is at most the configuration's time
    (hclk : c[v].clock ≤ c.time) :
    M.nodeInv S.C S.P S.X c'[v].st ∧ (c'[v].st).v = v ∧ (c'[v].st).t ≤ (c'[v].clock : Int) := by
  refine AtomicStep.elim (motive := fun _ d d' =>
      (M.nodeInv S.C S.P S.X d[v].st ∧ (d[v].st).v = v ∧ (d[v].st).t ≤ (d[v].clock : Int)) →
      d[v].clock ≤ d.time →
      M.nodeInv S.C S.P S.X d'[v].st ∧ (d'[v].st).v = v ∧ (d'[v].st).t ≤ (d'[v].clock : Int))
    hstep ?_ ?_ ?_ ?_ ?_ h hclk
  · intro d t w tk hen hw htk ⟨hI, hv, ht⟩ hc
    have hlt : d[v].clock < t := by omega
    by_cases hreact : v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int)
    · rw [tickAllAwakeUpdate_getElem_react hreact]
      -- the wake stage keeps the invariant and the validator, with a clock at most the framework's
      have hwv : M.nodeInv S.C S.P S.X (w v).state ∧ (w v).state.v = (d[v].st).v ∧
          (w v).state.t ≤ (d[v].clock : Int) := by
        have hw' := hw v
        unfold TickAllAwakeWake at hw'
        split at hw'
        · obtain ⟨h1, h2, h3⟩ := (reaction_wake_nodeInv M F) S _ _ _ _ _ hw' hI ht
          exact ⟨h1, h2, le_of_eq h3⟩
        · rw [hw']
          exact ⟨hI, rfl, ht⟩
      obtain ⟨hw1, hw2, hw3⟩ := hwv
      have hle : (w v).state.t ≤ (t : Int) :=
        le_trans hw3 (by exact_mod_cast hlt.le)
      obtain ⟨h1, h2, h3⟩ :=
        (reaction_tick_nodeInv M F) S v t _ (w v).state (tk v) (htk v hreact) hw1 hle
      exact ⟨h1, h2.trans (hw2.trans hv), h3⟩
    · have hst := tickAllAwakeUpdate_getElem_st_of_not_react (w := w) (tk := tk) (c := d) hreact
      rw [hst]
      refine ⟨hI, hv, le_trans ht ?_⟩
      by_cases haw : v ∈ Sched.awake (t : Int)
      · rw [tickAllAwakeUpdate_clock_awake haw]
        exact_mod_cast hlt.le
      · rw [tickAllAwakeUpdate_getElem_asleep haw]
  · intro d p m res _ hres ⟨hI, hv, ht⟩ _
    rw [applyNodeStepResult_getElem]
    split
    · rename_i hp
      subst hp
      have hst : (Framework.StsMultisetLog.receive p m d)[p].st = d[p].st := by
        rw [receive_getElem, if_pos rfl]
      have hclk' : (Framework.StsMultisetLog.receive p m d)[p].clock = d[p].clock := by
        rw [receive_getElem, if_pos rfl]
      show M.nodeInv S.C S.P S.X res.state ∧ res.state.v = p ∧
        res.state.t ≤ ((Framework.StsMultisetLog.receive p m d)[p].clock : Int)
      rw [hclk']
      rw [hst] at hres
      obtain ⟨h1, h2, h3⟩ := (reaction_recv_nodeInv M F) S _ _ _ d[p].st m res hres hI
      exact ⟨h1, h2.trans hv, h3 ▸ ht⟩
    · rw [receive_getElem, if_neg (by assumption)]
      exact ⟨hI, hv, ht⟩
  · intro d p ev
    exact ev.elim
  · intro d p m _ h' _
    exact h'
  · intro d p m _ h' _
    exact h'

/-- **Lemma 11, the node invariant.** At every step of every execution, every validator's node
state satisfies `NodeInv`, its validator field is the validator, and its clock is at most the
framework's clock for it.

Why: the initial node state satisfies it (`initial_nodeInv`), and every step keeps it
(`atomicStep_nodeInv`), the framework's clock being at most the configuration's time
(`atomic_clock_le_time`).

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `i`: the step; `v`: the
  validator.

Read aloud: at every step of every execution of the model, every validator's node state satisfies
the model's invariant, has its validator, and has a clock at most the framework's. -/
theorem lem11_node_invariant (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocolOf M S) Sched) (i : ℕ) (v : V) :
    M.nodeInv S.C S.P S.X (x[i][v].st) ∧ (x[i][v].st).v = v ∧
      ((x[i][v].st).t : Int) ≤ (x[i][v].clock : Int) := by
  induction i with
  | zero =>
      obtain ⟨-, hn, -⟩ := x.init
      show M.nodeInv S.C S.P S.X ((x.cfg 0)[v].st) ∧ ((x.cfg 0)[v].st).v = v ∧
        ((x.cfg 0)[v].st).t ≤ ((x.cfg 0)[v].clock : Int)
      rw [hn v]
      exact ⟨F.nd.initial_nodeInv S.C S.P S.X v,
        by show (M.initial S.C v).v = v; exact (F.init.initial_clock S.C v).2,
        by show (M.initial S.C v).t ≤ ((0 : ℕ) : Int); rw [(F.init.initial_clock S.C v).1]
           show (0 : Int) ≤ ((0 : ℕ) : Int); simp⟩
  | succ i ih => exact (atomicStep_nodeInv M F) (x.step i) v ih (atomic_clock_le_time x i v)

end Execution

section NoRaise

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks.Sts (Setup)

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
theorem ticksSucceed_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocolOf M S) Sched) : TicksSucceed M S Sched x := by
  intro i t v hl _ _
  have hI := (lem11_node_invariant M F) S Sched x i v
  have hN : M.nodeInv S.C S.P S.X (tickInputState M x i t v) := by
    unfold tickInputState
    split
    · exact (F.nd.wake_nodeInv S.C S.P S.X _ _ hI.1 hI.2.2).1
    · exact hI.1
  have hle : (tickInputState M x i t v).t ≤ (t : Int) := by
    have h2 : ((x[i][v].clock : ℕ) : Int) ≤ ((x[i].time : ℕ) : Int) := by
      exact_mod_cast Framework.StsMultisetLog.atomic_clock_le_time x i v
    have h3 : ((x[i].time : ℕ) : Int) + 1 = (t : Int) := by
      exact_mod_cast ((time_of_lbl_tickAllAwake M) x hl).1
    have h4 : ((x[i].time : ℕ) : Int) ≤ (t : Int) := by
      rw [← h3]; exact Int.le_add_one (le_refl _)
    -- a wake sets the clock to the framework's clock, which is at most `t`
    unfold tickInputState
    split
    · exact ((F.wk.wake_readers _ _).2.1).trans_le (le_trans h2 h4)
    · exact le_trans hI.2.2 (le_trans h2 h4)
  obtain ⟨⟨r, hr⟩, hne⟩ := F.nd.tick_ok S.C S.P S.X _ (t : Int) hN hle
  refine ⟨fun r' hr' => ?_, ⟨r, hr⟩⟩
  cases r' with
  | ok p => exact ⟨p, rfl⟩
  | error e => exact absurd hr' (hne e)

end NoRaise

end GoldilocksCorrectness.Record.Proofs.AbstractTrace.Atomic
