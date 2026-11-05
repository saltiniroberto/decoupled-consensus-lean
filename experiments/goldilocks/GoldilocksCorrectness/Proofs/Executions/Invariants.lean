module
public import GoldilocksCorrectness.Statements.Executions.InvariantDefs
public import GoldilocksCorrectness.Proofs.Routines.DREPost
public import GoldilocksCorrectness.Proofs.Routines.Blocks
public import GoldilocksCorrectness.Proofs.Routines.WalkEnd
public import GoldilocksCorrectness.Proofs.Routines.Record
public import GoldilocksCorrectness.Proofs.Executions.ChainState
public import GoldilocksCorrectness.Proofs.Routines.DREPost
public import GoldilocksCorrectness.Proofs.Routines.FGState
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Routines.ACInterface
public import GoldilocksCorrectness.Proofs.Routines.ACStore
public import GoldilocksCorrectness.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Proofs.Routines.RevokeLocks
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.Wiring

@[expose] public section

/-!
# The node invariant (Lemma 11), per routine, per reaction and per step

`NodeInv` holds at every step of every execution, with the node's validator field and a clock at
most the framework's. This file proves it for every routine of Goldilocks that writes a node state,
then for each step of the wiring `GoldilocksCorrectness.Wiring.protocol` on one event, then for
each step of the sts framework's atomic semantics, and along an execution by induction from the initial
configuration. No assumption on the execution is needed: a failed tick keeps the state, a wake
writes `awakeSince` only, and the atomic semantics changes an adversarial validator's state at no
step.

## The relations

- `VotesInv P A t`: the pool of `A` is filed by slot and committee, every pool vote is stamped,
  and every pool vote's stamp is at most `t`;
- `KeepsVotes A A'`: `A'` has `A`'s pool, vote stamps and block stamps.

## What is proved

- the AC routines: `on_goldfish_vote_cases`, `on_goldfish_vote_votesInv`,
  `ac_on_block_timestamp_block`, `ac_on_block_votesInv`, `revoke_locks_keepsVotes`,
  `update_confirmation_keepsVotes`, `goldfish_vote_votesInv`, `ac_on_tick_votesInv`;
- the FG routines: `fg_on_attestation_keeps`, `fg_on_attestations_keeps`,
  `update_finality_keeps`, `fg_on_block_eq`; the pool of attestations: `fg_on_attestation_wf`,
  `fg_on_attestations_wf`, `update_finality_attestations`, `fg_on_block_wf`; the finality caches:
  `fg_on_attestation_caches`, `fg_on_attestations_caches`, `update_finality_h_max`,
  `update_finality_finalizedAncestorJustified`, `fg_on_block_finalizedAncestorJustified`,
  `fg_on_block_heightCacheBounds`; the justification cache: `fg_on_attestation_h_j`,
  `fg_on_attestations_h_j`, `update_finality_F_descends`, `update_finality_justification`,
  `fg_on_block_justification`, `fg_on_block_justified`;
- the tree: `ancestors_mem`; the frame's tree: `mem_fg_to_ac_tree`;
- the record: `create_attestation_lock`, `fg_attest_eq`;
- the node: `block_admissible_facts`, `block_admissible_root_fresh`,
  `block_well_formed_attestations`, `nodeInv_of_frame`,
  `on_block_nodeInv`, `on_ac_message_nodeInv`, `on_attestation_nodeInv`, `receive_nodeInv`,
  `wake_nodeInv`, `record_awake_frame`, `record_awake_keeps_record`, `propose_block_nodeInv`,
  `ac_to_fg_head_mem`, `nodeInv_of_record`, `fg_attest_nodeInv`, `attest_nodeInv`,
  `tick_nodeInv`;
- the initial state and the reactions: `initial_nodeInv`, `reaction_tick_nodeInv`,
  `reaction_wake_nodeInv`, `reaction_recv_nodeInv`;
- the steps: `atomicStep_nodeInv`; along an execution, `lem11_node_invariant`;
- the root of the fork choice: `F_ancestorEq_get_fc_root`.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.bind_any DREBPost.dite
  DREBPost.ite DREBPost.liftM DREBPost.of_outcome DREBPost.pure DREPost DREPost.bind_any
  DREPost.dite DREPost.ite DREPost.pure ancestors_mem chainStateOf_J_spec chainStateOf_height_mono
  create_attestation_lock forIn_yield_inv fun_getElem ok_of_bind_eq_ok)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (fg_attest_eq fg_on_attestation_caches
  fg_on_attestation_h_j fg_on_attestation_keeps fg_on_block_eq
  fg_on_block_finalizedAncestorJustified fg_on_block_heightCacheBounds fg_on_block_justification
  fg_on_block_justified mem_fg_to_ac_tree update_finality_attestations)
open GoldilocksCorrectness.Statements.Routines (AttestationsValid ChainStatesComputed
  FinalizedAncestorJustified HeightCacheBounds JustificationCacheBounds JustifiedHeight
  JustifiedInTree)

open GoldilocksCorrectness.Proofs.Routines (VotesInv VotesInv.mono ac_on_block_timestamp_block
  ac_on_block_votesInv ac_on_tick_votesInv ac_to_fg_head_mem on_goldfish_vote_timestamp_block
  on_goldfish_vote_votesInv)

open GoldilocksCorrectness.Proofs.Routines (initial_nodeInv on_ac_message_nodeInv
  on_attestation_nodeInv on_block_nodeInv tick_nodeInv wake_nodeInv)
open GoldilocksCorrectness.Statements.Routines (LockBelowJustified NodeInv)

open GoldilocksCorrectness.Proofs.Routines (initial_eq)

open GoldilocksCorrectness.Proofs.Routines (receive_nodeInv)

namespace GoldilocksCorrectness.Proofs.Executions

open Goldilocks
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_node_iff
  ancestorEq_genesis_iff ancestorEq_compatible genesis_ancestorEq)
open GoldilocksCorrectness.Statements.Routines (RecordConsistent)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The AC routines -/

section AC

variable [RootOrder]

end AC

/-! ## The FG routines, and the tree -/

section FG

variable [RootOrder]

end FG

section Justification

variable [RootOrder]

end Justification

/-! ## The node -/

section Node

variable [RootOrder]

end Node

/-! ## The initial state, the reactions, the steps -/

section Execution

open Framework.StsMultisetLog (AtomicAction AtomicExec AtomicStep Event Schedule
  TickAllAwakeWake tickAllAwakeUpdate_getElem_react tickAllAwakeUpdate_getElem_st_of_not_react
  tickAllAwakeUpdate_clock_awake tickAllAwakeUpdate_getElem_asleep applyNodeStepResult_getElem
  receive_getElem atomic_clock_le_time NodeStepResult View SignedMsg)
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol step_tick_iff step_wake_iff step_recv_iff)

variable [RootOrder]

/-- A tick step at a reading `r` no earlier than the node's clock keeps `NodeInv` and the
validator, and leaves a clock at most `r`: an answer of the tick sets the clock to `r`, and the
step that keeps the state keeps it.

The variables:
- `S`: the setup; `p`: the validator; `r`: the reading; `view`: its view; `n`: the node state;
  `res`: the step result. -/
theorem reaction_tick_nodeInv (S : Setup V) (p : V) (r : ℕ) (view : View V (NamedObject V))
    (n : NodeState V) (res : NodeStepResult (NodeState V) (NamedObject V))
    (hstep : (protocol S).step p r view n .tick res)
    (h : NodeInv S.C S.P S.X n) (hr : n.t ≤ (r : Int)) :
    NodeInv S.C S.P S.X res.state ∧ res.state.v = n.v ∧ res.state.t ≤ (r : Int) := by
  rcases (step_tick_iff S p r view n res).1 hstep with ⟨n', sent, hok, rfl⟩ | ⟨-, rfl⟩
  · obtain ⟨h1, h2, h3⟩ := DREBPost.of_outcome (tick_nodeInv S.C S.P S.X n (r : Int) h hr) hok
    exact ⟨h1, h2, h3.le⟩
  · exact ⟨h, rfl, hr⟩

/-- A wake step at a reading no earlier than the clock keeps `NodeInv` and the validator, and sets
the clock to the reading.

The variables:
- `S`: the setup; `p`: the validator; `r`: the reading; `view`: its view; `n`: the node state;
  `res`: the step result. -/
theorem reaction_wake_nodeInv (S : Setup V) (p : V) (r : ℕ) (view : View V (NamedObject V))
    (n : NodeState V) (res : NodeStepResult (NodeState V) (NamedObject V))
    (hstep : (protocol S).step p r view n .wake res) (h : NodeInv S.C S.P S.X n)
    -- the node's clock is at most the reading
    (hr : n.t ≤ (r : Int)) :
    NodeInv S.C S.P S.X res.state ∧ res.state.v = n.v ∧ res.state.t = (r : Int) := by
  rw [(step_wake_iff S p r view n res).1 hstep]
  exact wake_nodeInv S.C S.P S.X n (r : Int) h hr

/-- A delivery step keeps `NodeInv`, the validator and the clock.

The variables:
- `S`: the setup; `p`: the validator; `r`: the reading; `view`: its view; `n`: the node state;
  `m`: the signed message delivered; `res`: the step result. -/
theorem reaction_recv_nodeInv (S : Setup V) (p : V) (r : ℕ) (view : View V (NamedObject V))
    (n : NodeState V) (m : SignedMsg V (NamedObject V))
    (res : NodeStepResult (NodeState V) (NamedObject V))
    (hstep : (protocol S).step p r view n (.recv m) res) (h : NodeInv S.C S.P S.X n) :
    NodeInv S.C S.P S.X res.state ∧ res.state.v = n.v ∧ res.state.t = n.t := by
  rw [(step_recv_iff S p r view n m res).1 hstep]
  exact receive_nodeInv S.C S.P S.X n m.msg h

/-- Every step of the atomic semantics keeps, for each validator `v`, `NodeInv` of its node
state, the node's validator field `v`, and a node clock at most the framework's clock, given the
framework's clock at most the configuration's time. At the tick of every awake validator, a
validator that reacts runs its wake reaction (when it enters the awake set) and its tick reaction
at the new time; a validator that does not react keeps its state, with a clock no earlier. At a
delivery, the receiver runs its reaction to the delivered message. No other action changes a
state.

The variables:
- `S`: the setup; `Sched`: the schedule; `a`: the action; `c`, `c'`: the configurations before
  and after; `v`: the validator. -/
theorem atomicStep_nodeInv {S : Setup V} {Sched : Schedule V}
    {a : AtomicAction V (NamedObject V) Empty}
    {c c' : Framework.StsMultisetLog.Config V (NamedObject V) (NodeState V)}
    (hstep : AtomicStep (protocol S) Sched a c c') (v : V)
    (h : NodeInv S.C S.P S.X c[v].st ∧ c[v].st.v = v ∧ c[v].st.t ≤ (c[v].clock : Int))
    -- the framework's clock of `v` is at most the configuration's time
    (hclk : c[v].clock ≤ c.time) :
    NodeInv S.C S.P S.X c'[v].st ∧ c'[v].st.v = v ∧ c'[v].st.t ≤ (c'[v].clock : Int) := by
  refine AtomicStep.elim (motive := fun _ d d' =>
      (NodeInv S.C S.P S.X d[v].st ∧ d[v].st.v = v ∧ d[v].st.t ≤ (d[v].clock : Int)) →
      d[v].clock ≤ d.time →
      NodeInv S.C S.P S.X d'[v].st ∧ d'[v].st.v = v ∧ d'[v].st.t ≤ (d'[v].clock : Int))
    hstep ?_ ?_ ?_ ?_ ?_ h hclk
  · intro d t w tk hen hw htk ⟨hI, hv, ht⟩ hc
    have hlt : d[v].clock < t := by omega
    by_cases hreact : v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int)
    · rw [tickAllAwakeUpdate_getElem_react hreact]
      -- the wake stage keeps the invariant and the validator, with a clock at most the framework's
      have hwv : NodeInv S.C S.P S.X (w v).state ∧ (w v).state.v = d[v].st.v ∧
          (w v).state.t ≤ (d[v].clock : Int) := by
        have hw' := hw v
        unfold TickAllAwakeWake at hw'
        split at hw'
        · obtain ⟨h1, h2, h3⟩ := reaction_wake_nodeInv S _ _ _ _ _ hw' hI ht
          exact ⟨h1, h2, le_of_eq h3⟩
        · rw [hw']
          exact ⟨hI, rfl, ht⟩
      obtain ⟨hw1, hw2, hw3⟩ := hwv
      have hle : (w v).state.t ≤ (t : Int) :=
        le_trans hw3 (by exact_mod_cast hlt.le)
      obtain ⟨h1, h2, h3⟩ :=
        reaction_tick_nodeInv S v t _ (w v).state (tk v) (htk v hreact) hw1 hle
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
      show NodeInv S.C S.P S.X res.state ∧ res.state.v = p ∧
        res.state.t ≤ ((Framework.StsMultisetLog.receive p m d)[p].clock : Int)
      rw [hclk']
      rw [hst] at hres
      obtain ⟨h1, h2, h3⟩ := reaction_recv_nodeInv S _ _ _ d[p].st m res hres hI
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
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `i`: the step; `v`: the
  validator. -/
theorem lem11_node_invariant (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    NodeInv S.C S.P S.X (x[i][v].st) ∧ (x[i][v].st).v = v ∧
      ((x[i][v].st).t : Int) ≤ (x[i][v].clock : Int) := by
  induction i with
  | zero =>
      obtain ⟨-, hn, -⟩ := x.init
      show NodeInv S.C S.P S.X ((x.cfg 0)[v].st) ∧ ((x.cfg 0)[v].st).v = v ∧
        ((x.cfg 0)[v].st).t ≤ ((x.cfg 0)[v].clock : Int)
      rw [hn v]
      exact ⟨initial_nodeInv S.C S.P S.X v, by show (initial S.C v).v = v; rw [initial_eq],
        by show (initial S.C v).t ≤ ((0 : ℕ) : Int); rw [initial_eq]
           show (0 : Int) ≤ ((0 : ℕ) : Int); simp⟩
  | succ i ih => exact atomicStep_nodeInv (x.step i) v ih (atomic_clock_le_time x i v)

end Execution

/-! ## The record's facts, from its consistency and from `LockBelowJustified` -/

omit [DecidableEq V] [Fintype V] in
/-- At a height greater than the cache `h_j`, a node state satisfying `LockBelowJustified` holds no
lock.

The variables:
- `n`: the node state; `H`: the height. -/
theorem lock_none_of_lockBelowJustified (n : NodeState V) (h : LockBelowJustified n) (H : Height)
    -- the cache `h_j` is less than `H`
    (hH : n.S.h_j < H) : n.Λ.lock H = none := by
  cases hl : n.Λ.lock H with
  | none => rfl
  | some T =>
      have := h H T hl
      exact absurd hH (Nat.not_lt.mpr this)

/-- At a height where a consistent record holds a lock, every attestation content it sent names
the locked block: the lock is the block of a finality pair the record sent (`lockRec`), and every
content at that pair's height names its block (`lockKept`).

The variables:
- `Λ`: the record. -/
theorem lockNamesSent_of_consistent {Λ : SigningHistory} (hR : RecordConsistent Λ) :
    LockNamesSent Λ := by
  intro h T hl b hb hbh
  obtain ⟨c, hc, hcfp⟩ := (hR.lockRec h T).1 hl
  exact hR.lockKept c hc ⟨h, T⟩ hcfp b hb hbh

/-- A target a consistent record holds at a height was sent at that height for that block.

The variables:
- `Λ`: the record. -/
theorem target_sent_of_consistent {Λ : SigningHistory} (hR : RecordConsistent Λ) :
    ∀ (h : Height) (T : BlockId), Λ.target h = some T → ∃ b ∈ Λ.sent, b.h = h ∧ b.T = T := by
  intro h T ht
  obtain ⟨c, hc, hch, -, hcT⟩ := (hR.targetRec h T).1 ht
  exact ⟨c, hc, hch, hcT⟩

/-- A target a consistent record sent at a height is recorded there.

The variables:
- `Λ`: the record. -/
theorem sent_target_recorded_of_consistent {Λ : SigningHistory} (hR : RecordConsistent Λ) :
    ∀ b ∈ Λ.sent, b.τ = false → Λ.target b.h ≠ none := by
  intro b hb hτ hnone
  have h' := (hR.targetRec b.h b.T).2 ⟨b, hb, rfl, hτ, rfl⟩
  rw [hnone] at h'
  cases h'

/-- A timeout a consistent record sent at a height is recorded there.

The variables:
- `Λ`: the record. -/
theorem timeout_recorded_of_consistent {Λ : SigningHistory} (hR : RecordConsistent Λ) :
    ∀ b ∈ Λ.sent, b.τ = true → Λ.timeout b.h = true :=
  fun b hb hτ => (hR.timeoutRec b.h).2 ⟨b, hb, rfl, hτ⟩

end GoldilocksCorrectness.Proofs.Executions
