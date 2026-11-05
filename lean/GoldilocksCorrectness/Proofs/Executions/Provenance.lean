module
public import GoldilocksCorrectness.Proofs.Executions.Clock
public import GoldilocksCorrectness.Proofs.Executions.TickSends
public import GoldilocksCorrectness.Proofs.Routines.DREPost
public import GoldilocksCorrectness.Proofs.Routines.Sends
public import GoldilocksCorrectness.Proofs.Routines.ACInterface
public import GoldilocksCorrectness.Proofs.Routines.ACStore
public import GoldilocksCorrectness.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.Wiring

@[expose] public section

/-! A Goldfish vote enters a validator's pool, and a block its tree, only at
a step that puts an object carrying it on the wire, signed by that validator:

- a delivery of the object `o₀` adds to the pool only `o₀`'s vote or a vote of the `votes` of
  `o₀`'s block, and to the tree only `o₀`'s block; the wiring re-sends `o₀` itself
  (`relayedObjects`), signed by the receiver;
- a tick adds to the pool its own vote, which it broadcast, and the votes of its own proposal,
  which it broadcast; it adds to the tree only its own proposal;
- a wake adds nothing.

So every vote of a pool entered the sent log, as a Goldfish vote or inside a block, at an earlier
step; and every non-genesis block of a tree was put on the wire by the tree's own validator at an
earlier step, at which that validator was outside the adversary set and its clock was in a slot
at least the block's (`block_admissible`'s test that the block's slot is not later than the
node's).

## The kit

- `DREBSpec R m`: every answer `a` of the routine `m`, run after any list `sent₀`, has the sent
  list `sent₀ ++ l` with `R a l`; its lemmas for a return, two binds, a lifted routine that may
  fail, an `if`, and `broadcast` followed by a return; `DREBSpec.of_outcome` reads it at an `.ok`
  outcome of the routine.

## The relation

- `Carried o vote`: the object `o` is the Goldfish vote `vote`, or a block whose `votes` holds it;
- `NewObjectsIn C n n' l`: every vote `n'` holds under a slot beyond `n` is carried by an object
  of `l`, and every block of `n'`'s tree beyond `n`'s is an object of `l`, of a slot at most the
  slot of `n'`'s clock.

## What is proved

- per routine: `on_goldfish_vote_new`, `ac_on_block_new_votes`, `block_admissible_slot`,
  `on_block_new`, `receive_new`, `goldfish_vote_prov`, `ac_on_tick_prov`, `propose_block_prov`,
  `attest_prov`, `tick_prov`;
- per step: `delivered_mem_sent`, `step_sent_of_delivery`, `step_sent_of_tick_send`,
  `step_pool_new`, `step_tree_new`;
- along an execution: `pool_vote_sent`, `pool_vote_sent_before`, `tree_block_relayed`,
  `tree_block_relayed_before`; and `PoolCovered`, `TreeCovered` with `poolCovered_sent`,
  `treeCovered_relayed`.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Proofs.Routines (Carried DREBSpec DREBSpec.bind' DREBSpec.bind_liftPost
  DREBSpec.broadcast_pure DREBSpec.dite DREBSpec.ite DREBSpec.of_outcome DREBSpec.pure DREPost.true
  forIn_yield_inv)

open GoldilocksCorrectness.Proofs.Routines (fg_on_block_eq)

open GoldilocksCorrectness.Proofs.Routines (ac_on_block_new_votes ac_on_tick_prov
  on_goldfish_vote_new)

open GoldilocksCorrectness.Proofs.Routines (on_attestation_frame on_block_new tick_prov)

open GoldilocksCorrectness.Proofs.Routines (acState_initial_eq fgState_initial_eq initial_eq
  mem_pool_iff)

open GoldilocksCorrectness.Proofs.Routines (mem_relayedObjects_self receive_new)

namespace GoldilocksCorrectness.Proofs.Executions

open Goldilocks
open GoldilocksCorrectness.Statements.Executions

/-! ## The kit -/

section Kit

variable {V : Type}

end Kit

/-! ## The relation -/

section Relation

variable {V : Type} [DecidableEq V] [Fintype V]

end Relation

/-! ## The routines -/

section Routines

variable {V : Type} [DecidableEq V] [Fintype V]

variable [RootOrder]

end Routines

/-! ## The steps -/

section Steps

open Framework.StsMultisetLog (AtomicAction AtomicExec Schedule SignedMsg TickAllAwakeWake
  nodeStep_iff_exists)
open Goldilocks.Sts (Setup relayedObjects)
open GoldilocksCorrectness.Wiring (protocol step_tick_iff step_wake_iff step_recv_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder] {S : Setup V} {Sched : Schedule V}

/-- A delivered message was in the sent log when it was delivered: the enabling condition of a
delivery.

The variables:
- `x`: the execution; `d`: the step of the delivery; `v`: the receiver; `sm`: the signed
  message. -/
theorem delivered_mem_sent {x : AtomicExec (protocol S) Sched} {d : ℕ} {v : V}
    {sm : SignedMsg V (NamedObject V)}
    -- the step `d` delivers `sm` to `v`
    (hl : x.lbl d = AtomicAction.deliver v sm) : sm ∈ x[d].sent := by
  have hs := x.step d
  rw [hl] at hs
  exact hs.1.1

/-- A delivery to `v` puts on the wire, signed by `v`, every object the wiring re-sends for the
delivered object.

The variables:
- `x`: the execution; `d`: the step of the delivery; `v`: the receiver; `sm`: the signed message;
  `o`: an object re-sent. -/
theorem step_sent_of_delivery {x : AtomicExec (protocol S) Sched} {d : ℕ} {v : V}
    {sm : SignedMsg V (NamedObject V)}
    -- the step `d` delivers `sm` to `v`
    (hl : x.lbl d = AtomicAction.deliver v sm) {o : NamedObject V}
    -- `o` is re-sent for the delivered object
    (ho : o ∈ relayedObjects sm.msg) :
    (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x[d + 1].sent - x[d].sent := by
  have hs := x.step d
  rw [hl] at hs
  obtain ⟨-, hr⟩ := hs
  obtain ⟨res, hp, hc⟩ := (nodeStep_iff_exists _ v (.recv sm) _ _).1 hr
  have hsent : x[d + 1].sent = x[d].sent + res.send.map (SignedMsg.mk v) := by
    show (x.cfg (d + 1)).sent = _
    rw [hc]
    rfl
  rw [hsent, add_tsub_cancel_left, (step_recv_iff S _ _ _ _ _ _).1 hp]
  exact Multiset.mem_map.2 ⟨o, ho, rfl⟩

/-- At the tick of every awake validator at `t`, a validator awake and outside the adversary set
at `t` puts on the wire, signed by itself, every object its tick sends from the node state the
tick starts from.

The variables:
- `x`: the execution; `i`: the step; `t`: the time of the tick; `v`: the validator;
- `n'`, `sent`: an `.ok` outcome of `v`'s tick; `o`: an object of `sent`. -/
theorem step_sent_of_tick_send {x : AtomicExec (protocol S) Sched} {i t : ℕ} {v : V}
    -- the step `i` is the tick of every awake validator at `t`
    (hl : x.lbl i = AtomicAction.tickAllAwake t)
    -- `v` is awake and outside the adversary set at `t`
    (hmem : v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int))
    {n' : NodeState V} {sent : List (NamedObject V)}
    -- `.ok (n', sent)` is an outcome of `v`'s tick
    (hrun : .ok (n', sent) ∈ (tick S.C S.P S.X (tickInputState x i t v) (t : Int)).outcomes)
    {o : NamedObject V} (ho : o ∈ sent) :
    (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent := by
  have hs := x.step i
  rw [hl] at hs
  obtain ⟨-, w, tk, hw, htk, hc⟩ := hs
  have hsent : x[i + 1].sent = x[i].sent + (Sched.awake (t : Int) \ Sched.adv (t : Int)).sum
      (fun q => ((w q).send + (tk q).send).map (SignedMsg.mk q)) := by
    show (x.cfg (i + 1)).sent = _
    rw [hc]
    rfl
  rw [hsent, add_tsub_cancel_left]
  refine Multiset.mem_sum.2 ⟨v, hmem, Multiset.mem_map.2 ⟨o, Multiset.mem_add.2 (Or.inr ?_), rfl⟩⟩
  -- the wake stage leaves the state the tick starts from
  have hwv : (w v).state = tickInputState x i t v := by
    have hw' := hw v
    unfold TickAllAwakeWake at hw'
    unfold tickInputState
    split at hw'
    · rename_i he
      rw [if_pos he, (step_wake_iff S v _ _ _ _).1 hw']
      rfl
    · rename_i he
      rw [if_neg he, hw']
      rfl
  have htk' := (step_tick_iff S v t _ _ _).1 (htk v hmem)
  rw [hwv] at htk'
  rcases htk' with ⟨n'', sent'', hok, hres⟩ | ⟨hno, -⟩
  · -- the deterministic tick has one outcome, so `tk v` sent `sent`
    have heq : (Except.ok (n', sent) : DRE (NodeState V × List (NamedObject V))) =
        .ok (n'', sent'') :=
      (DREB.run_eq_of_mem_outcomes hrun).symm.trans (DREB.run_eq_of_mem_outcomes hok)
    simp only [Except.ok.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [hres]
    exact Multiset.mem_coe.2 ho
  · exact absurd hrun (hno (n', sent))

/-- A Goldfish vote that enters a validator's pool of a slot at a step is carried by an object
that validator put on the wire at that step: its own tick's send, or the re-send of the object
delivered to it.

The variables:
- `x`: the execution; `k`: the step; `v`: the validator; `s`: the slot; `vote`: the vote;
- `o`: the object put on the wire. -/
theorem step_pool_new (x : AtomicExec (protocol S) Sched) {k : ℕ} {v : V} {s : Slot}
    {vote : GoldfishVote V}
    -- `vote` is in `v`'s votes of slot `s` after the step
    (hv : vote ∈ (x[k + 1][v].st).A.gf_votes s)
    -- `vote` is not in `v`'s votes of slot `s` before the step
    (hn : vote ∉ (x[k][v].st).A.gf_votes s) :
    ∃ o : NamedObject V, Carried o vote ∧
      (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent - x[k].sent := by
  rcases step_cases x k v with h | ⟨t, n', sent, hl, hmem, hok, h⟩ | ⟨sm, hl, -, -, h⟩
  · rw [h] at hv
    exact absurd hv hn
  · rw [h] at hv
    obtain ⟨-, hA, -⟩ := tickInputState_frame x k t v
    have hP := DREBSpec.of_outcome (tick_prov S.C S.P S.X _ (t : Int)) hok
    obtain ⟨o, ho, hc⟩ := hP.1.1 s vote hv (by rw [hA]; exact hn)
    exact ⟨o, hc, step_sent_of_tick_send hl hmem hok ho⟩
  · rw [h] at hv
    exact ⟨sm.msg, (receive_new S.C S.P S.X _ sm.msg).1 s vote hv hn,
      step_sent_of_delivery hl (mem_relayedObjects_self sm.msg)⟩

/-- A block that enters a validator's tree at a step was put on the wire by that validator at
that step, as its own proposal or as the re-send of the block delivered to it; the validator was
outside the adversary set at the time the step ends at, and the block's slot is at most the slot
of the validator's clock after the step.

The variables:
- `x`: the execution; `k`: the step; `v`: the validator; `B`: the block. -/
theorem step_tree_new (x : AtomicExec (protocol S) Sched) {k : ℕ} {v : V} {B : Block V}
    -- `B` is in `v`'s tree after the step
    (hB : B ∈ (x[k + 1][v].st).S.T)
    -- `B` is not in `v`'s tree before the step
    (hn : B ∉ (x[k][v].st).S.T) :
    (⟨v, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent - x[k].sent ∧
      v ∉ Sched.adv (x[k + 1].time : Int) ∧ B.slot ≤ S.C.slot (x[k + 1][v].st).t := by
  rcases step_cases x k v with h | ⟨t, n', sent, hl, hmem, hok, h⟩ | ⟨sm, hl, -, hadv, h⟩
  · rw [h] at hB
    exact absurd hB hn
  · rw [(time_of_lbl_tickAllAwake x hl).2, h]
    rw [h] at hB
    obtain ⟨hS, -, -⟩ := tickInputState_frame x k t v
    have hP := DREBSpec.of_outcome (tick_prov S.C S.P S.X _ (t : Int)) hok
    obtain ⟨h1, h2⟩ := hP.1.2 B hB (by rw [hS]; exact hn)
    exact ⟨step_sent_of_tick_send hl hmem hok h1, (Finset.mem_sdiff.1 hmem).2, h2⟩
  · have hnt : ∀ t, x.lbl k ≠ AtomicAction.tickAllAwake t := by
      intro t h'
      rw [hl] at h'
      cases h'
    rw [time_succ_of_not_tickAllAwake x hnt, h]
    rw [h] at hB
    obtain ⟨hmsg, hs⟩ := (receive_new S.C S.P S.X _ sm.msg).2 B hB hn
    refine ⟨step_sent_of_delivery hl ?_, hadv, hs⟩
    rw [hmsg]
    exact mem_relayedObjects_self _

end Steps

/-! ## Along an execution -/

section Execution

open Framework.StsMultisetLog (AtomicExec Schedule SignedMsg)
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder] {S : Setup V} {Sched : Schedule V}

/-- `PoolCovered Q n`: every Goldfish vote of `n`'s pool of every slot satisfies `Q`.

The variables:
- `Q`: the condition; `n`: the node state.

Read aloud: every vote `n` holds satisfies `Q`. -/
def PoolCovered (Q : GoldfishVote V → Prop) (n : NodeState V) : Prop :=
  ∀ s : Slot, ∀ vote ∈ n.A.pool s, Q vote

/-- `TreeCovered Q n`: every block of `n`'s tree other than the genesis block satisfies `Q`.

The variables:
- `Q`: the condition; `n`: the node state.

Read aloud: every non-genesis block `n` holds satisfies `Q`. -/
def TreeCovered (Q : Block V → Prop) (n : NodeState V) : Prop :=
  ∀ B ∈ n.S.T, B ≠ Block.genesis → Q B

/-- Every Goldfish vote of a validator's pool at a step entered the sent log at an earlier step,
as a Goldfish vote or inside a block.

The variables:
- `x`: the execution; `k`: the step; `v`: the validator; `s`: the slot; `vote`: the vote;
- `i`: the step of the send; `sm`: the signed message. -/
theorem pool_vote_sent (x : AtomicExec (protocol S) Sched) {k : ℕ} {v : V} {s : Slot}
    {vote : GoldfishVote V}
    -- `v`'s pool of slot `s` holds `vote` at `k`
    (hv : vote ∈ (x[k][v].st).A.pool s) :
    ∃ i < k, ∃ sm ∈ x[i + 1].sent - x[i].sent, sm.msg = NamedObject.gfVote vote ∨
      ∃ B : Block V, sm.msg = NamedObject.block B ∧ vote ∈ B.votes := by
  induction k with
  | zero =>
      rw [getElem_zero_st, initial_eq, acState_initial_eq] at hv
      exact absurd ((mem_pool_iff _ _ _).1 hv) List.not_mem_nil
  | succ k ih =>
      by_cases hk : vote ∈ (x[k][v].st).A.pool s
      · obtain ⟨i, hi, sm, hsm, hc⟩ := ih hk
        exact ⟨i, by omega, sm, hsm, hc⟩
      · obtain ⟨o, hc, ho⟩ := step_pool_new x ((mem_pool_iff _ _ _).1 hv)
          (fun h => hk ((mem_pool_iff _ _ _).2 h))
        exact ⟨k, by omega, ⟨v, o⟩, ho, hc⟩

/-- Every validator's pool at every step is covered by "entered the sent log at an earlier step,
as a Goldfish vote or inside a block".

The variables:
- `x`: the execution; `k`: the step; `v`: the validator. -/
theorem poolCovered_sent (x : AtomicExec (protocol S) Sched) (k : ℕ) (v : V) :
    PoolCovered (fun vote => ∃ i < k, ∃ sm ∈ x[i + 1].sent - x[i].sent,
      sm.msg = NamedObject.gfVote vote ∨
        ∃ B : Block V, sm.msg = NamedObject.block B ∧ vote ∈ B.votes) (x[k][v].st) :=
  fun _ _ hv => pool_vote_sent x hv

/-- Every Goldfish vote of a validator's pool of a slot before the time `t` entered the sent log,
as a Goldfish vote or inside a block, at a step before `stepBefore x t`.

The variables:
- `x`: the execution; `t`: the time; `v`: the validator; `s`: the slot; `vote`: the vote;
- `i`: the step of the send; `sm`: the signed message.

Read aloud: a vote held before `t` was put on the wire, alone or in a block, before `t`. -/
theorem pool_vote_sent_before {x : AtomicExec (protocol S) Sched}
    {t : ℕ} {v : V} {s : Slot} {vote : GoldfishVote V}
    -- `v`'s pool of slot `s` before `t` holds `vote`
    (hv : vote ∈ (stateBefore x t v).A.pool s) :
    ∃ i < stepBefore x t, ∃ sm ∈ x[i + 1].sent - x[i].sent,
      sm.msg = NamedObject.gfVote vote ∨
        ∃ B : Block V, sm.msg = NamedObject.block B ∧ vote ∈ B.votes :=
  pool_vote_sent x (k := stepBefore x t) hv

/-- Every non-genesis block of a validator's tree at a step was put on the wire by that validator
at an earlier step, at which it was outside the adversary set at the step's end and after which
its clock was in a slot at least the block's.

The variables:
- `x`: the execution; `k`: the step; `v`: the validator; `B`: the block;
- `i`: the step of the send. -/
theorem tree_block_relayed (x : AtomicExec (protocol S) Sched) {k : ℕ} {v : V} {B : Block V}
    -- `v`'s tree holds `B` at `k`
    (hB : B ∈ (x[k][v].st).S.T)
    -- `B` is not the genesis block
    (hg : B ≠ Block.genesis) :
    ∃ i < k, (⟨v, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent ∧
      v ∉ Sched.adv (x[i + 1].time : Int) ∧ B.slot ≤ S.C.slot (x[i + 1][v].st).t := by
  classical
  have hex : ∃ m : ℕ, B ∈ (x[m][v].st).S.T := ⟨k, hB⟩
  have h0 : B ∉ (x[0][v].st).S.T := by
    rw [getElem_zero_st, initial_eq, fgState_initial_eq]
    intro h
    exact hg (Finset.mem_singleton.1 h)
  have hpos : Nat.find hex ≠ 0 := by
    intro h
    exact h0 (h ▸ Nat.find_spec hex)
  have hle : Nat.find hex ≤ k := Nat.find_min' hex hB
  obtain ⟨i, hi⟩ : ∃ i : ℕ, Nat.find hex = i + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hni : B ∉ (x[i][v].st).S.T := Nat.find_min hex (by omega)
  have hi1 : B ∈ (x[i + 1][v].st).S.T := hi ▸ Nat.find_spec hex
  exact ⟨i, by omega, step_tree_new x hi1 hni⟩

/-- Every validator's tree at every step is covered by "put on the wire by the validator at an
earlier step, honest at its end, with its clock after it in a slot at least the block's".

The variables:
- `x`: the execution; `k`: the step; `v`: the validator. -/
theorem treeCovered_relayed (x : AtomicExec (protocol S) Sched) (k : ℕ) (v : V) :
    TreeCovered (fun B => ∃ i < k, (⟨v, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent ∧
      v ∉ Sched.adv (x[i + 1].time : Int) ∧ B.slot ≤ S.C.slot (x[i + 1][v].st).t) (x[k][v].st) :=
  fun _ hB hg => tree_block_relayed x hB hg

/-- A non-genesis block a validator holds before the time `t` was put on the wire by that
validator itself, as a re-send of the delivery that admitted it or as its own proposal, at a step
before `stepBefore x t`; the validator was honest then if it is honest at `t` (corruption is
permanent, `Sched.MonotoneCorruption`); and its clock after that step was in a slot at least the
block's (`block_admissible`'s test that the block's slot is not later than the node's).

The variables:
- `x`: the execution; `t`: the time; `v`: the validator; `B`: the block;
- `i`: the step of the send.

Read aloud: a non-genesis block `v` holds before `t` was put on the wire by `v` itself, at a step
before `t`, honest then if honest at `t`, and with `v`'s clock then in a slot at least the
block's. -/
theorem tree_block_relayed_before {x : AtomicExec (protocol S) Sched}
    -- corruption is permanent
    (hmono : Sched.MonotoneCorruption) {t : ℕ} {v : V} {B : Block V}
    -- `v`'s tree before `t` holds `B`
    (hB : B ∈ (stateBefore x t v).S.T)
    -- `B` is not the genesis block
    (hg : B ≠ Block.genesis) :
    ∃ i < stepBefore x t, (⟨v, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent ∧
      (v ∉ Sched.adv (t : Int) → v ∉ Sched.adv (x[i].time : Int)) ∧
      S.C.slot ((x[i + 1][v].st).t) ≥ B.slot := by
  obtain ⟨i, hi, h1, h2, h3⟩ := tree_block_relayed x (k := stepBefore x t) hB hg
  refine ⟨i, hi, h1, fun _ ha => h2 (hmono _ _ ?_ ha), h3⟩
  exact_mod_cast time_le_succ x i

end Execution

end GoldilocksCorrectness.Proofs.Executions
