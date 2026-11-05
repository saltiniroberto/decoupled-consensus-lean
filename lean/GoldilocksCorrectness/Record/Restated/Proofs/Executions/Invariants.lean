module
public import GoldilocksCorrectness.Record.Facts
public import GoldilocksCorrectness.Record.Wiring
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.NodeDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.RecordDefs

@[expose] public section

/-!
# Invariants, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Invariants.lean` that read an execution,
over a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: each step of the
node keeps the model's node invariant `M.nodeInv`, the validator and a clock at most the step's
reading (from the fields `tick_nodeInv`, `wake_nodeInv`, `receive_nodeInv` of `F.nd`), each step of
the sts framework's atomic semantics keeps them, and Lemma 11 holds along the execution from
`F.nd.initial_nodeInv`; and the record's facts from its consistency and from `LockBelowJustified`,
read through the record's readers. The page's routine-level theorems are the facts' fields or have
their twins in phase A.
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

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Statements.Routines (LockBelowJustified RecordConsistent)

open Goldilocks
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_node_iff
  ancestorEq_genesis_iff ancestorEq_compatible genesis_ancestorEq)

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V) (F : Facts M)
include F

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

open Framework.StsMultisetLog (AtomicStep Event TickAllAwakeWake tickAllAwakeUpdate_getElem_react tickAllAwakeUpdate_getElem_st_of_not_react tickAllAwakeUpdate_clock_awake tickAllAwakeUpdate_getElem_asleep applyNodeStepResult_getElem receive_getElem atomic_clock_le_time NodeStepResult View SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
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

/-- **Lemma 11, the clock-free part, from the run's facts alone.** At every step of a trace of the
model, every validator's node state satisfies the clock-free part of the model's node invariant and
its validator field is the validator. No hypothesis on the environment: a tick and a restart keep the
clock-free part at any reading, a delivery keeps it.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `x`: the trace; `R`: the run's facts; `i`: the step; `v`: the validator.

Read aloud: at every step of a run of the model, every validator's node state satisfies the
clock-free part of the invariant and has its validator. -/
theorem lem11_node_invariantCore_of_run (S : Setup V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (i : ℕ) (v : V) :
    M.nodeInvCore S.C S.P S.X (x.st i v) ∧ (x.st i v).v = v := by
  induction i with
  | zero =>
      rw [R.init v]
      exact ⟨F.nd.nodeInv_core (F.nd.initial_nodeInv S.C S.P S.X v), (F.init.initial_clock S.C v).2⟩
  | succ i ih =>
      obtain ⟨hinv, hv⟩ := ih
      by_cases hvv : (∃ t, x.lbl i = Event.tick v t) ∨
          (∃ (tR : ℕ) (keep : Bool), x.lbl i = Event.restart v tR keep) ∨
          ∃ sm, x.lbl i = Event.deliver v sm
      · rcases hvv with ⟨t, hl⟩ | ⟨tR, keep, hl⟩ | ⟨sm, hl⟩
        · obtain ⟨n', sent, hok, hst, -⟩ := R.tick i v t hl
          rw [hst]
          obtain ⟨h1, h2, -⟩ := F.nd.tick_nodeInvCore S.C S.P S.X _ (t : Int) hinv n' sent hok
          exact ⟨h1, h2.trans hv⟩
        · rw [(R.restart i v tR keep hl).1]
          obtain ⟨h1, h2, -⟩ := F.nd.wake_nodeInvCore S.C S.P S.X _ (tR : Int) hinv
          exact ⟨h1, h2.trans hv⟩
        · rw [(R.deliver i v sm hl).2.1]
          obtain ⟨h1, h2, -⟩ := F.nd.receive_nodeInvCore S.C S.P S.X _ sm.msg hinv
          exact ⟨h1, h2.trans hv⟩
      · push Not at hvv
        rw [R.untouched i v hvv.1 hvv.2.1 hvv.2.2]
        exact ⟨hinv, hv⟩

/-- **Lemma 11, the node invariant.** At every step of every execution, the node state of every
validator outside the adversary set after that step satisfies `NodeInv`, its validator field is the
validator, and its clock is its clock value after the step.

Why: by induction on the steps. The initial node state satisfies it (`initial_nodeInv`), with the
initial clock `0`. A tick or a restart of `v` keeps it (`tick_nodeInv`, `wake_nodeInv`): they ask
that the new clock value be at least the node's clock, which is `v`'s clock value before the step,
and `clockValue_le_of_set` gives that from the condition on executions `clock_mono` for a validator
outside the adversary set; both set the clock to the step's clock value. A delivery keeps the
invariant and the clock (`receive_nodeInv`). Any other step leaves `v`'s state as it is
(`untouched`). Corruption is permanent (`corrupted_mono`), so `v` is outside the adversary set at
every earlier step too.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `A`: the activity; `x`: the execution; `R`: the run's facts; `E`: the environment's
  facts; `i`: the step; `v`: the validator; `hv`: `v` is outside the adversary set after `i` steps.

Read aloud: at every step of every execution of the model, every validator outside the adversary
set has a node state that satisfies the model's invariant, has its validator, and has as its clock
its clock value `x.clockValue i v`. -/
theorem lem11_node_invariant (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V)
    -- `v` is outside the adversary set after `i` steps
    (hv : v ∉ A.corrupted i) :
    M.nodeInv S.C S.P S.X (x.st i v) ∧ (x.st i v).v = v ∧
      (x.st i v).t = (x.clockValue i v : Int) := by
  have key : M.nodeInv S.C S.P S.X (x.st i v) ∧ (x.st i v).t = (x.clockValue i v : Int) := by
    induction i with
    | zero =>
        rw [R.init v, x.clockValue_zero v]
        exact ⟨F.nd.initial_nodeInv S.C S.P S.X v, by rw [(F.init.initial_clock S.C v).1]; rfl⟩
    | succ i ih =>
        have hvi : v ∉ A.corrupted i := fun h => hv (E.corrupted_mono i (i + 1) (Nat.le_succ i) h)
        obtain ⟨hinv, hclk⟩ := ih hvi
        by_cases ht : ∃ t, x.lbl i = Event.tick v t
        · obtain ⟨t, hl⟩ := ht
          obtain ⟨n', sent, hok, hst, -⟩ := R.tick i v t hl
          have hle : (x.st i v).t ≤ (t : Int) := by
            rw [hclk]; exact_mod_cast E.clockValue_le_of_set hvi (Or.inl hl)
          obtain ⟨h1, -, h3⟩ := F.nd.tick_nodeInv S.C S.P S.X (x.st i v) (t : Int) hinv hle n' sent hok
          rw [hst, x.clockValue_succ_of_tick hl]
          exact ⟨h1, h3⟩
        by_cases hr : ∃ (tR : ℕ) (keep : Bool), x.lbl i = Event.restart v tR keep
        · obtain ⟨tR, keep, hl⟩ := hr
          have hle : (x.st i v).t ≤ (tR : Int) := by
            rw [hclk]; exact_mod_cast E.clockValue_le_of_set hvi (Or.inr ⟨keep, hl⟩)
          obtain ⟨h1, -, h3⟩ := F.nd.wake_nodeInv S.C S.P S.X (x.st i v) (tR : Int) hinv hle
          rw [(R.restart i v tR keep hl).1, x.clockValue_succ_of_restart hl]
          exact ⟨h1, h3⟩
        have ht' : ∀ t, x.lbl i ≠ Event.tick v t := fun t h => ht ⟨t, h⟩
        have hr' : ∀ (tR : ℕ) (keep : Bool), x.lbl i ≠ Event.restart v tR keep :=
          fun tR keep h => hr ⟨tR, keep, h⟩
        rw [x.clockValue_succ_of_not ht' hr']
        by_cases hd : ∃ sm, x.lbl i = Event.deliver v sm
        · obtain ⟨sm, hl⟩ := hd
          obtain ⟨h1, -, h3⟩ := F.nd.receive_nodeInv S.C S.P S.X (x.st i v) sm.msg hinv
          rw [(R.deliver i v sm hl).2.1]
          exact ⟨h1, h3.trans hclk⟩
        · rw [R.untouched i v ht' hr' (fun sm h => hd ⟨sm, h⟩)]
          exact ⟨hinv, hclk⟩
  exact ⟨key.1, ((lem11_node_invariantCore_of_run M F) S x R i v).2, key.2⟩

/-- Every validator's tree is stamped in order at every step, whether or not the validator is in the
adversary set: every block of the tree other than the genesis block is stamped no earlier than its
parent (`StampOrder`).

Why: by induction on the steps. The initial node state satisfies the node invariant. A tick or a
delivery is by a validator active in the configuration it starts from, outside the adversary set
after the step too (`corrupted_keep`), so Lemma 11 gives the node invariant after it. A restart
keeps the tree and the stamps (`wake_readers`), and any other step leaves the state as it is. No
clock is read: a clock set back by a restart of a validator in the adversary set moves no stamp.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `A`: the activity; `x`: the execution; `R`: the run's facts; `E`: the environment's
  facts; `i`: the step; `v`: the validator.

Read aloud: at every step, every validator's tree has each block stamped no earlier than its parent. -/
theorem stampOrder_of_exec (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    GoldilocksCorrectness.Record.Statements.Routines.StampOrder M (x.st i v) := by
  induction i with
  | zero =>
      rw [R.init v]
      exact F.nd.nodeInv_stampOrder (F.nd.initial_nodeInv S.C S.P S.X v)
  | succ i ih =>
      by_cases ht : ∃ t, x.lbl i = Event.tick v t
      · obtain ⟨t, hl⟩ := ht
        exact F.nd.nodeInv_stampOrder
          (lem11_node_invariant M F S A x R E (i + 1) v (E.not_mem_corrupted_succ_of_tick hl)).1
      by_cases hd : ∃ sm, x.lbl i = Event.deliver v sm
      · obtain ⟨sm, hl⟩ := hd
        have hv : v ∉ A.corrupted (i + 1) := by
          rw [E.corrupted_keep i (by rw [hl]; exact nofun)]
          exact Activity.not_mem_corrupted_of_mem_active (E.deliver_active i v sm hl)
        exact F.nd.nodeInv_stampOrder (lem11_node_invariant M F S A x R E (i + 1) v hv).1
      by_cases hr : ∃ (tR : ℕ) (keep : Bool), x.lbl i = Event.restart v tR keep
      · obtain ⟨tR, keep, hl⟩ := hr
        rw [(R.restart i v tR keep hl).1]
        obtain ⟨-, -, hT, -, -, -, -, -, -, hB, -⟩ := F.wk.wake_readers (x.st i v) (tR : Int)
        have hT' : (M.wake (x.st i v) (tR : Int)).tree = (x.st i v).tree := hT
        have hB' : (M.wake (x.st i v) (tR : Int)).blockStamp = (x.st i v).blockStamp := hB
        intro B hBt hg
        rw [hT'] at hBt
        rw [hB']
        exact ih B hBt hg
      · rw [R.untouched i v (fun t h => ht ⟨t, h⟩) (fun tR keep h => hr ⟨tR, keep, h⟩)
          (fun sm h => hd ⟨sm, h⟩)]
        exact ih

/-- Every ancestor of a block of a validator's tree is in the tree, at every step of a trace of the
model: the clock-free part of Lemma 11 holds at every step from the run's facts alone, and it keeps
the tree closed under parents.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `x`: the trace; `R`: the run's facts; `i`: the step; `v`: the validator; `B`: the
  block of the tree; `P'`: an ancestor of `B`, or `B`.

Read aloud: every validator's tree holds every ancestor of each of its blocks, at every step. -/
theorem ancestors_mem_T_of_run (S : Setup V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (i : ℕ) (v : V) (B P' : Block V)
    -- `B` is in the tree
    (hB : B ∈ (x.st i v).tree)
    -- `P'` is an ancestor of `B`, or `B`
    (hP' : P'.AncestorEq B) :
    P' ∈ (x.st i v).tree :=
  GoldilocksCorrectness.Proofs.Routines.ancestors_mem
    (fun B' h1 h2 => ((F.nd.nodeInvCore_treeClosed
      ((lem11_node_invariantCore_of_run M F) S x R i v).1).2 B' h1 h2).1) hB hP'

end Execution

/-! ## The record's facts, from its consistency and from `LockBelowJustified` -/

/-- At a height greater than the cache `h_j`, a node state satisfying `LockBelowJustified` holds no
lock.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `H`: the height.

Read aloud: a node state whose locks are at heights at most its justification height holds no lock
at a greater height. -/
theorem lock_none_of_lockBelowJustified (n : M.N) (h : LockBelowJustified M n) (H : Height)
    -- the cache `h_j` is less than `H`
    (hH : n.justifiedHeight < H) : n.sentLock H = none := by
  cases hl : n.sentLock H with
  | none => rfl
  | some T =>
      have := h H T hl
      exact absurd hH (Nat.not_lt.mpr this)

/-- At a height where a consistent record holds a lock, every attestation content it sent names
the locked block: the lock is the block of a finality pair the record sent (`lockRec`), and every
content at that pair's height names its block (`lockKept`).

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state.

Read aloud: at a height where a consistent record holds a lock, every attestation it sent names the
locked block. -/
theorem lockNamesSent_of_consistent {n : M.N} (hR : RecordConsistent M n) :
    LockNamesSent M n := by
  intro h T hl b hb hbh
  obtain ⟨c, hc, hcfp⟩ := (hR.lockRec h T).1 hl
  exact hR.lockKept c hc ⟨h, T⟩ hcfp b hb hbh

/-- A target a consistent record holds at a height was sent at that height for that block.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state.

Read aloud: a target a consistent record holds was sent. -/
theorem target_sent_of_consistent {n : M.N} (hR : RecordConsistent M n) :
    ∀ (h : Height) (T : BlockId), n.sentTarget h = some T → ∃ b ∈ n.sentAttestations, b.h = h ∧ b.T = T := by
  intro h T ht
  obtain ⟨c, hc, hch, -, hcT⟩ := (hR.targetRec h T).1 ht
  exact ⟨c, hc, hch, hcT⟩

/-- A target a consistent record sent at a height is recorded there.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state.

Read aloud: a target a consistent record sent is recorded. -/
theorem sent_target_recorded_of_consistent {n : M.N} (hR : RecordConsistent M n) :
    ∀ b ∈ n.sentAttestations, b.τ = false → n.sentTarget b.h ≠ none := by
  intro b hb hτ hnone
  have h' := (hR.targetRec b.h b.T).2 ⟨b, hb, rfl, hτ, rfl⟩
  rw [hnone] at h'
  cases h'

/-- A timeout a consistent record sent at a height is recorded there.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state.

Read aloud: a timeout a consistent record sent is recorded. -/
theorem timeout_recorded_of_consistent {n : M.N} (hR : RecordConsistent M n) :
    ∀ b ∈ n.sentAttestations, b.τ = true → n.sentTimeout b.h = true :=
  fun b hb hτ => (hR.timeoutRec b.h).2 ⟨b, hb, rfl, hτ⟩

end GoldilocksCorrectness.Record.Proofs.Executions

