module
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Proofs.Executions.Steps
public import GoldilocksCorrectness.Proofs.Routines.FGState
public import GoldilocksCorrectness.Proofs.Routines.ACInterface
public import GoldilocksCorrectness.Proofs.Routines.ACStore
public import GoldilocksCorrectness.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Proofs.Routines.RevokeLocks
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.Wiring

@[expose] public section

/-! A Goldilocks node state only
grows in the fields the delivery lemma reads: its tree `S.T` only gains blocks, its finalized
block `S.F` moves only to a descendant, each slot's Goldfish votes `A.gf_votes s` are only
appended to, and the stamp of a block of the tree and of a vote of the pool is never rewritten.
This file proves it for every routine of Goldilocks that writes those fields, then for each
step of the wiring `GoldilocksCorrectness.Wiring.protocol` on one event, then for each step of
the sts framework's atomic semantics, and along an execution.

The stamps are kept because a block already in the tree is refused (`block_admissible`'s test
that no block of the tree has the block's root), and a vote already held is refused
(`on_goldfish_vote`'s test `vote ∈ A.gf_votes[vote.slot]`), so neither map is rewritten where it
is set. The second needs the pool filed by slot (`SlotKeyed`): a vote held under a slot is held
under its own slot, the one the test reads. Lemma 11 supplies it at every step.

## The relations

- `SlotKeyed A`: every vote filed under a slot in `A` has that slot;
- `ACGrows A A'`: every slot's votes of `A` are a prefix of `A'`'s, and the stamp of each vote of
  `A`'s pool is the same in `A'`;
- `TreeGrows n n'`: `n'` holds `n`'s tree, a descendant of `n`'s finalized block (or the block),
  `n`'s votes as prefixes, and `n`'s stamps of the blocks of its tree and of the votes of its pool;
- `ACStampsAt A A' τ`: every vote `A'` holds under a slot and `A` does not is stamped `τ` in `A'`
  (the AC routines carry it for `Clock.lean`, which proves that the time is the step's).

All four are definitions, not structures, so that they transfer to a record literal with the
same fields by unfolding (the `lean-proof-idioms` skill, section 39).

## What is proved

- the AC routines: `on_goldfish_vote_grows`, `ac_on_block_grows`, `revoke_locks_grows`,
  `update_confirmation_grows`, `goldfish_vote_grows`, `ac_on_tick_grows`;
- the FG routines: `update_finality_F`, `fg_on_block_F`;
- the node: `on_block_grows`, `on_ac_message_grows`, `on_attestation_grows`, `receive_grows`,
  `propose_block_grows`, `attest_grows`, `tick_grows`;
- per reaction: `reaction_grows`; per step: `atomicStep_grows`;
- along an execution: `grows_of_le`, `stateBefore_grows`, `pool_mono`, `mem_T_mono`,
  `F_ancestorEq_of_le`, `blockStamp_kept`, `voteStamp_kept`.

No honesty hypothesis is needed anywhere: the atomic semantics changes an adversarial validator's
state at no step.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.bind_any DREBPost.dite
  DREBPost.ite DREBPost.liftM DREBPost.of_outcome DREBPost.pure DREPost forIn_yield_inv fun_getElem)

open GoldilocksCorrectness.Proofs.Routines (fg_on_attestation_keeps fg_on_block_F fg_on_block_eq)

open GoldilocksCorrectness.Proofs.Routines (ACGrows SlotKeyed SlotKeyed.of_poolKeyed
  ac_on_block_grows ac_on_tick_grows on_goldfish_vote_grows)

open GoldilocksCorrectness.Proofs.Routines (mem_pool_iff)

open GoldilocksCorrectness.Proofs.Routines (TreeGrows TreeGrows.refl on_ac_message_grows
  on_attestation_grows on_block_grows tick_grows)

open GoldilocksCorrectness.Proofs.Routines (wake_eq)

open GoldilocksCorrectness.Proofs.Routines (receive_grows)

namespace GoldilocksCorrectness.Proofs.Executions

open Goldilocks
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans)

variable {V : Type} [DecidableEq V] [Fintype V]

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

open Framework.StsMultisetLog (AtomicAction AtomicExec AtomicStep Event Schedule
  TickAllAwakeWake tickAllAwakeUpdate_getElem_react tickAllAwakeUpdate_getElem_st_of_not_react
  applyNodeStepResult_getElem receive_getElem NodeStepResult View)
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol step_tick_iff step_wake_iff step_recv_iff)

variable [RootOrder]

/-- Every step of the wiring on one event, from a pool filed by slot, grows the node state: a tick
step is an answer of the node's tick or keeps the state, a delivery runs the dispatch, a wake
writes `awakeSince` only.

The variables:
- `S`: the setup; `p`: the validator; `r`: the reading; `view`: its view; `n`: the node state;
  `e`: the event; `res`: the step result. -/
theorem reaction_grows (S : Setup V) (p : V) (r : ℕ) (view : View V (NamedObject V))
    (n : NodeState V) (e : Event V (NamedObject V) Empty)
    (res : NodeStepResult (NodeState V) (NamedObject V))
    (hstep : (protocol S).step p r view n e res) (hk : SlotKeyed n.A) :
    TreeGrows n res.state := by
  cases e with
  | tick =>
      rcases (step_tick_iff S p r view n res).1 hstep with ⟨n', sent, hok, rfl⟩ | ⟨-, rfl⟩
      · exact (DREBPost.of_outcome (tick_grows S.C S.P S.X n (r : Int) hk) hok).2
      · exact TreeGrows.refl _
  | recv m =>
      rw [(step_recv_iff S p r view n m res).1 hstep]
      exact (receive_grows S.C S.P S.X n m.msg hk).2
  | wake =>
      rw [(step_wake_iff S p r view n res).1 hstep, wake_eq]
      exact TreeGrows.refl n
  | custom ev => exact ev.elim

/-- Every step of the atomic semantics grows every validator's node state, given its pool filed
by slot. At the tick of every awake validator, a validator that reacts runs its wake reaction
(when it enters the awake set) and its tick reaction; a validator that does not react keeps its
state. At a delivery, the receiver runs its reaction to the delivered message. No other action
changes a state.

The variables:
- `S`: the setup; `Sched`: the schedule; `a`: the action; `c`, `c'`: the configurations before
  and after; `v`: the validator.

Read aloud: across any step, a validator keeps every block and vote it holds with their stamps,
and its finalized block moves only to a descendant. -/
theorem atomicStep_grows {S : Setup V} {Sched : Schedule V}
    {a : AtomicAction V (NamedObject V) Empty}
    {c c' : Framework.StsMultisetLog.Config V (NamedObject V) (NodeState V)}
    (h : AtomicStep (protocol S) Sched a c c') (v : V) (hk : SlotKeyed c[v].st.A) :
    TreeGrows c[v].st c'[v].st := by
  refine AtomicStep.elim (motive := fun _ d d' =>
      SlotKeyed d[v].st.A → TreeGrows d[v].st d'[v].st) h ?_ ?_ ?_ ?_ ?_ hk
  · intro d t w tk _ hw htk hk'
    by_cases hv : v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int)
    · rw [tickAllAwakeUpdate_getElem_react hv]
      -- the wake stage keeps the FG state and the AC state
      have hwv : TreeGrows d[v].st (w v).state ∧ (w v).state.A = d[v].st.A := by
        have hw' := hw v
        unfold TickAllAwakeWake at hw'
        split at hw'
        · rw [(step_wake_iff S _ _ _ _ _).1 hw', wake_eq]
          exact ⟨TreeGrows.refl _, rfl⟩
        · rw [hw']
          exact ⟨TreeGrows.refl _, rfl⟩
      show TreeGrows d[v].st (tk v).state
      exact hwv.1.trans
        (reaction_grows S _ _ _ _ _ _ (htk v hv) (by rw [hwv.2]; exact hk'))
    · rw [tickAllAwakeUpdate_getElem_st_of_not_react hv]
      exact TreeGrows.refl _
  · intro d p m res _ hres hk'
    rw [applyNodeStepResult_getElem]
    split
    · rename_i hp
      subst hp
      have hst : (Framework.StsMultisetLog.receive p m d)[p].st = d[p].st := by
        rw [receive_getElem, if_pos rfl]
      show TreeGrows d[p].st res.state
      rw [hst] at hres
      exact reaction_grows S _ _ _ _ _ _ hres hk'
    · rw [receive_getElem, if_neg (by assumption)]
      exact TreeGrows.refl _
  · intro d p ev
    exact ev.elim
  · intro d p m _ _
    exact TreeGrows.refl _
  · intro d p m _ _
    exact TreeGrows.refl _

variable {S : Setup V} {Sched : Schedule V} (x : AtomicExec (protocol S) Sched)

/-- Along an execution, every validator's node state only grows, from any step to any later one.
The pool is filed by slot at every step (Lemma 11).

The variables:
- `x`: the execution; `v`: the validator; `i ≤ j`: the two steps.

Read aloud: from a step to a later one, a validator keeps every block and vote it holds with their
stamps, and its finalized block moves only to a descendant. -/
theorem grows_of_le (v : V) {i j : ℕ} (hij : i ≤ j) : TreeGrows (x[i][v].st) (x[j][v].st) := by
  induction j, hij using Nat.le_induction with
  | base => exact TreeGrows.refl _
  | succ j _ ih =>
      exact ih.trans (atomicStep_grows (x.step j) v (SlotKeyed.of_poolKeyed
        (GoldilocksCorrectness.Statements.Executions.lem11_node_invariant S Sched x j v).1.1))

/-- The node state before a time grows with the time.

The variables:
- `x`: the execution; `v`: the validator; `t ≤ t'`: the two times.

Read aloud: `v`'s node state before a later time holds every block and vote its node state before
an earlier time holds, with the same stamps. -/
theorem stateBefore_grows (hdiv : TimeDiverges x.toTrace) (v : V) {t t' : ℕ} (h : t ≤ t') :
    TreeGrows (stateBefore x t v) (stateBefore x t' v) :=
  grows_of_le x v (stepBefore_mono x hdiv h)

/-- A vote of a validator's pool of a slot stays in it at every later step.

The variables:
- `x`: the execution; `v`: the validator; `i ≤ j`: the two steps; `s`: the slot. -/
theorem pool_mono (v : V) {i j : ℕ} (hij : i ≤ j) (s : Slot) :
    (x[i][v].st).A.pool s ⊆ (x[j][v].st).A.pool s := fun _ hv =>
  (mem_pool_iff _ _ _).2 (((grows_of_le x v hij).2.2.1 s).subset ((mem_pool_iff _ _ _).1 hv))

/-- A block of a validator's tree stays in it at every later step.

The variables:
- `x`: the execution; `v`: the validator; `i ≤ j`: the two steps. -/
theorem mem_T_mono (v : V) {i j : ℕ} (hij : i ≤ j) : (x[i][v].st).S.T ⊆ (x[j][v].st).S.T :=
  (grows_of_le x v hij).1

/-- A validator's finalized block at a step is an ancestor of its finalized block at every later
step, or that block.

The variables:
- `x`: the execution; `v`: the validator; `i ≤ j`: the two steps. -/
theorem F_ancestorEq_of_le (v : V) {i j : ℕ} (hij : i ≤ j) :
    (x[i][v].st).S.F.AncestorEq (x[j][v].st).S.F :=
  (grows_of_le x v hij).2.1

/-- The stamp of a block of a validator's tree is the same at every later step.

The variables:
- `x`: the execution; `v`: the validator; `i ≤ j`: the two steps; `B`: the block. -/
theorem blockStamp_kept (v : V) {i j : ℕ} (hij : i ≤ j) {B : Block V}
    (hB : B ∈ (x[i][v].st).S.T) :
    (x[j][v].st).A.timestamp_block B = (x[i][v].st).A.timestamp_block B :=
  (grows_of_le x v hij).2.2.2.1 B hB

/-- The stamp of a vote of a validator's pool is the same at every later step.

The variables:
- `x`: the execution; `v`: the validator; `i ≤ j`: the two steps; `s`: the slot; `vote`: the
  vote. -/
theorem voteStamp_kept (v : V) {i j : ℕ} (hij : i ≤ j) {s : Slot} {vote : GoldfishVote V}
    (hv : vote ∈ (x[i][v].st).A.pool s) :
    (x[j][v].st).A.timestamp_vote vote = (x[i][v].st).A.timestamp_vote vote :=
  (grows_of_le x v hij).2.2.2.2 s vote ((mem_pool_iff _ _ _).1 hv)

end Execution

end GoldilocksCorrectness.Proofs.Executions
