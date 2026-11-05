module
public import GoldilocksCorrectness.Statements.Executions.UnforgeabilityDefs
public import GoldilocksCorrectness.Proofs.Executions.Provenance
public import GoldilocksCorrectness.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Statements.Routines.AttestationStatements
public import GoldilocksCorrectness.Statements.Routines.ProposalStatements
public import GoldilocksCorrectness.Proofs.Routines.Record
public import GoldilocksCorrectness.Proofs.Routines.Attestation
public import GoldilocksCorrectness.Proofs.Routines.NodeSends
public import GoldilocksCorrectness.Proofs.Routines.Wiring

@[expose] public section

/-!
# Unforgeability: an object of an honest validator on the wire came from that validator's tick

Under `Unforgeability Vocab.goldilocks Sched x.toTrace`, a message whose object is attributed to a validator outside the
adversary set up to the step, and which that validator signed, entered the sent log first at a
tick: a delivery re-sends under the receiver's signature only objects of a message already on the
wire, which `Unforgeability` puts there under the author's signature already; an adversarial send
is signed by a validator in the adversary set; a forward re-sends a message of a view, already on
the wire. An attestation that a tick sends has its content in the record the tick leaves, and the
record only grows. So:

- the spec lemmas: an attestation on the wire under its own validator's signature, that validator
  outside the adversary set up to the step, came from that validator's tick, and its content is in
  that validator's record after the tick (`attestation_from_own_tick`); a Goldfish vote likewise
  came from its validator's tick (`vote_from_own_tick`);
- `VotesCastByOwner` follows from `Unforgeability` and permanent corruption
  (`votesCastByOwner_of_unforgeability`).

## The kit

- the record: `create_attestation_sent_subset`, `create_attestation_content_mem`,
  `attest_record_grows`, `tick_record_grows`, `receive_Λ`, `step_record_mono`, `record_sent_mono`;
- the sent log and the views: `sent_le_of_le`, `mem_sent_of_le`, `mem_sent_of_mem_sub`,
  `view_subset_sent`;
- the steps, read backwards: `sent_of_delivery_step`, `sent_of_adversarial_step`,
  `sent_of_forward_step`, `mem_relayedObjects_iff`;
- honesty: `honestThrough_of_le`, `honestThrough_of_time_le`;
- `authored_from_own_tick`, the spec lemma generic in the object; `attest_sent_recorded`;
  `own_vote_mem_sent`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Proofs.Routines (create_attestation_content_mem
  create_attestation_sent_subset)
open GoldilocksCorrectness.Statements.Routines (carries)

open GoldilocksCorrectness.Proofs.Routines (ac_on_tick_sends)

open GoldilocksCorrectness.Proofs.Routines (on_block_eq tick_record_grows tick_sends)

open GoldilocksCorrectness.Proofs.Routines (mem_pool_iff wake_eq)

open GoldilocksCorrectness.Proofs.Routines (mem_relayedObjects_iff receive_Λ)

namespace GoldilocksCorrectness.Proofs.Executions

open Goldilocks
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (DREBRel DREBRel.bind DREBRel.pure DREBRel.ite
  DREBRel.liftM DREBRel.broadcast DREBRel.of_emits DREBRel.mono record_awake_Λ on_attestation_Λ
  create_attestation_cases record_attestation_sent mem_record_attestation_sent
  propose_block_Λ_rel)

/-! ## What the routines write into the anti-slashing record -/

section Routines

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

end Routines

/-! ## The sent log, the views and the steps -/

section Steps

open Framework.StsMultisetLog (AtomicAction AtomicExec AtomicStep Schedule SignedMsg
  atomic_sent_mono nodeStep_iff_exists tickAllAwakeUpdate_getElem_view applyNodeStepResult_view
  applyNodeStepResult_sent receive_view_self receive_view_other receive_sent)
open Goldilocks.Sts (Setup relayedObjects)
open GoldilocksCorrectness.Wiring (protocol step_recv_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder] {S : Setup V} {Sched : Schedule V}

/-- The sent log grows along the execution.

The variables:
- `x`: the execution; `i ≤ j`: the two steps. -/
theorem sent_le_of_le (x : AtomicExec (protocol S) Sched) {i j : ℕ} (hij : i ≤ j) :
    x[i].sent ≤ x[j].sent := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
      have hs : AtomicStep (protocol S) Sched (x.lbl j) x[j] x[j + 1] := x.step j
      exact ih.trans (atomic_sent_mono hs)

/-- A message of the sent log after `i` steps is in the sent log after every later step.

The variables:
- `x`: the execution; `i ≤ j`: the two steps; `sm`: the message. -/
theorem mem_sent_of_le (x : AtomicExec (protocol S) Sched) {i j : ℕ}
    {sm : SignedMsg V (NamedObject V)} (hsm : sm ∈ x[i].sent) (hij : i ≤ j) :
    sm ∈ x[j].sent :=
  Multiset.mem_of_le (sent_le_of_le x hij) hsm

/-- A message a step put on the wire is in the sent log after it.

The variables:
- `x`: the execution; `i`: the step; `sm`: the message. -/
theorem mem_sent_of_mem_sub (x : AtomicExec (protocol S) Sched) {i : ℕ}
    {sm : SignedMsg V (NamedObject V)} (hsm : sm ∈ x[i + 1].sent - x[i].sent) :
    sm ∈ x[i + 1].sent :=
  Multiset.mem_of_le (Multiset.sub_le_self _ _) hsm

/-- Every message of a validator's view is in the sent log, at every step: a view grows only by a
delivery, of a message of the sent log.

The variables:
- `x`: the execution; `i`: the step. -/
theorem view_subset_sent (x : AtomicExec (protocol S) Sched) (i : ℕ) :
    ∀ (p : V) (sm : SignedMsg V (NamedObject V)), sm ∈ x[i][p].view → sm ∈ x[i].sent := by
  induction i with
  | zero =>
      intro p sm h
      obtain ⟨-, hn, -⟩ := x.init
      have h' : sm ∈ (x.cfg 0)[p].view := h
      rw [hn p] at h'
      exact absurd h' (Finset.notMem_empty sm)
  | succ i ih =>
      have hs : AtomicStep (protocol S) Sched (x.lbl i) x[i] x[i + 1] := x.step i
      refine Framework.StsMultisetLog.AtomicStep.elim
        (motive := fun _ c c' => (∀ (p : V) (sm : SignedMsg V (NamedObject V)),
          sm ∈ c[p].view → sm ∈ c.sent) →
          ∀ (p : V) (sm : SignedMsg V (NamedObject V)), sm ∈ c'[p].view → sm ∈ c'.sent)
        hs ?_ ?_ ?_ ?_ ?_ ih
      · intro d t w tk _ _ _ hd p sm h
        rw [tickAllAwakeUpdate_getElem_view] at h
        exact Multiset.mem_add.2 (Or.inl (hd p sm h))
      · intro d q m res he _ hd p sm h
        rw [applyNodeStepResult_view] at h
        rw [applyNodeStepResult_sent, receive_sent]
        refine Multiset.mem_add.2 (Or.inl ?_)
        by_cases hpq : p = q
        · subst hpq
          rw [receive_view_self] at h
          rcases Finset.mem_insert.1 h with rfl | h
          · exact he.1
          · exact hd p sm h
        · rw [Framework.StsMultisetLog.receive_getElem, if_neg (Ne.symm hpq)] at h
          exact hd p sm h
      · intro d q ev
        exact ev.elim
      · intro d q m _ hd p sm h
        exact Multiset.mem_cons_of_mem (hd p sm h)
      · intro d q m _ hd p sm h
        exact Multiset.mem_cons_of_mem (hd p sm h)

/-- What a delivery to `p` puts on the wire is signed by `p` and is an object the wiring re-sends
for the delivered object.

The variables:
- `x`: the execution; `k`: the step of the delivery; `p`: the receiver; `m`: the delivered
  message; `p'`, `o`: the signer and the object of a message the step put on the wire. -/
theorem sent_of_delivery_step {x : AtomicExec (protocol S) Sched} {k : ℕ} {p : V}
    {m : SignedMsg V (NamedObject V)}
    -- the step `k` delivers `m` to `p`
    (hl : x.lbl k = AtomicAction.deliver p m) {p' : V} {o : NamedObject V}
    -- the step `k` put `⟨p', o⟩` on the wire
    (hm : (⟨p', o⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent - x[k].sent) :
    p' = p ∧ o ∈ relayedObjects m.msg := by
  have hs := x.step k
  rw [hl] at hs
  obtain ⟨-, hr⟩ := hs
  obtain ⟨res, hp, hc⟩ := (nodeStep_iff_exists _ p (.recv m) _ _).1 hr
  have hres := (step_recv_iff S _ _ _ _ _ _).1 hp
  have hsent : x[k + 1].sent = x[k].sent + res.send.map (SignedMsg.mk p) := by
    show (x.cfg (k + 1)).sent = _
    rw [hc]
    rfl
  rw [hsent, add_tsub_cancel_left, hres] at hm
  obtain ⟨o', ho', heq⟩ := Multiset.mem_map.1 hm
  injection heq with h1 h2
  subst h1 h2
  exact ⟨rfl, ho'⟩

/-- What an adversarial send by `p` puts on the wire is its one message, and `p` is in the
adversary set at the step's time.

The variables:
- `x`: the execution; `k`: the step; `p`: the sender; `m`: the object sent; `sm`: a message the
  step put on the wire. -/
theorem sent_of_adversarial_step {x : AtomicExec (protocol S) Sched} {k : ℕ} {p : V}
    {m : NamedObject V}
    -- the step `k` is `p`'s adversarial send of `m`
    (hl : x.lbl k = AtomicAction.adversarial p m) {sm : SignedMsg V (NamedObject V)}
    -- the step `k` put `sm` on the wire
    (hm : sm ∈ x[k + 1].sent - x[k].sent) :
    sm = ⟨p, m⟩ ∧ p ∈ Sched.adv (x[k].time : Int) := by
  have hs := x.step k
  rw [hl] at hs
  obtain ⟨he, hc⟩ := hs
  have hsent : x[k + 1].sent = ⟨p, m⟩ ::ₘ x[k].sent := by
    show (x.cfg (k + 1)).sent = _
    rw [hc]
    rfl
  rw [hsent, ← Multiset.singleton_add, add_tsub_cancel_right] at hm
  exact ⟨Multiset.mem_singleton.1 hm, he⟩

/-- What a forward by `p` puts on the wire is the forwarded message, which is in `p`'s view.

The variables:
- `x`: the execution; `k`: the step; `p`: the forwarder; `m`: the forwarded message; `sm`: a
  message the step put on the wire. -/
theorem sent_of_forward_step {x : AtomicExec (protocol S) Sched} {k : ℕ} {p : V}
    {m : SignedMsg V (NamedObject V)}
    -- the step `k` is `p`'s forward of `m`
    (hl : x.lbl k = AtomicAction.forward p m) {sm : SignedMsg V (NamedObject V)}
    -- the step `k` put `sm` on the wire
    (hm : sm ∈ x[k + 1].sent - x[k].sent) :
    sm = m ∧ m ∈ x[k][p].view := by
  have hs := x.step k
  rw [hl] at hs
  obtain ⟨he, hc⟩ := hs
  have hsent : x[k + 1].sent = m ::ₘ x[k].sent := by
    show (x.cfg (k + 1)).sent = _
    rw [hc]
    rfl
  rw [hsent, ← Multiset.singleton_add, add_tsub_cancel_right] at hm
  exact ⟨Multiset.mem_singleton.1 hm, he.2.1⟩

/-- Honesty through a later step is honesty through an earlier one.

The variables:
- `x`: the execution; `i ≤ j`: the two steps; `v`: the validator. -/
theorem honestThrough_of_le (x : AtomicExec (protocol S) Sched) {i j : ℕ} {v : V}
    (hij : i ≤ j) (h : HonestThrough x j v) : HonestThrough x i v := by
  intro t' ht'
  refine h t' (le_trans ht' ?_)
  exact_mod_cast time_mono x hij

/-- Honesty through a time is honesty through every step whose time is at most it.

The variables:
- `x`: the execution; `i`: the step; `t`: the time; `v`: the validator. -/
theorem honestThrough_of_time_le (x : AtomicExec (protocol S) Sched) {i : ℕ} {t : Int}
    {v : V} (h : HonestThroughTime Sched t v)
    -- the time after `i` steps is at most `t`
    (hi : (x[i].time : Int) ≤ t) : HonestThrough x i v :=
  fun t' ht' => h t' (le_trans ht' hi)

/-- **The spec lemma, generic in the object.** Under unforgeability, a message on the wire after
`k` steps, signed by the validator `v` its object is attributed to, `v` outside the adversary set
up to the time after `k` steps, entered the wire at an earlier step `k'` that is the tick of every
awake validator at some time `t`.

Why: take the first step after which the message is on the wire. A delivery re-sends, under the
receiver's signature, objects of a message already on the wire, so `Unforgeability` puts the
message there already; an adversarial send is signed by a validator in the adversary set; a
forward re-sends a message of a view, already on the wire.

The variables:
- `x`: the execution; `hU`: unforgeability; `k`: the step; `v`: the validator; `o`: the object;
- `k'`: the step of the first send; `t`: its time. -/
theorem authored_from_own_tick (x : AtomicExec (protocol S) Sched)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) {k : ℕ} {v : V} {o : NamedObject V}
    -- the object is attributed to `v`
    (ho : author o = some v)
    -- `v`'s signed message with the object `o` is on the wire after `k` steps
    (hm : (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x[k].sent)
    (hH : HonestThrough x k v) :
    ∃ k' < k, ∃ t : ℕ, x.lbl k' = AtomicAction.tickAllAwake t ∧
      (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x[k' + 1].sent - x[k'].sent := by
  classical
  have hex : ∃ m : ℕ, (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x[m].sent := ⟨k, hm⟩
  have h0 : (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∉ x[0].sent := by
    obtain ⟨-, -, hs0⟩ := x.init
    show (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∉ (x.cfg 0).sent
    rw [hs0]
    exact Multiset.notMem_zero _
  have hpos : Nat.find hex ≠ 0 := by
    intro h
    exact h0 (h ▸ Nat.find_spec hex)
  have hle : Nat.find hex ≤ k := Nat.find_min' hex hm
  obtain ⟨k', hk'⟩ : ∃ k' : ℕ, Nat.find hex = k' + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hni : (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∉ x[k'].sent := Nat.find_min hex (by omega)
  have hi1 : (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x[k' + 1].sent := hk' ▸ Nat.find_spec hex
  have hdiff : (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x[k' + 1].sent - x[k'].sent := by
    rw [Multiset.mem_sub, Multiset.count_eq_zero.2 hni]
    exact Multiset.count_pos.2 hi1
  have hH' : HonestThrough x k' v := honestThrough_of_le x (by omega) hH
  cases hl : x.lbl k' with
  | tickAllAwake t => exact ⟨k', by omega, t, hl, hdiff⟩
  | deliver p m =>
      exfalso
      obtain ⟨-, hrel⟩ := sent_of_delivery_step hl hdiff
      have hmem : m ∈ x[k'].sent := delivered_mem_sent hl
      rcases mem_relayedObjects_iff.1 hrel with h | hc
      · subst h
        exact hni (hU.unforgeable k' m v hmem ho hH')
      · exact hni (hU.carried k' m o v hmem hc ho hH')
  | custom p ev => exact ev.elim
  | adversarial p m =>
      exfalso
      obtain ⟨heq, hadv⟩ := sent_of_adversarial_step hl hdiff
      injection heq with hpv
      subst hpv
      exact hH' _ le_rfl hadv
  | forward p m =>
      exfalso
      obtain ⟨heq, hview⟩ := sent_of_forward_step hl hdiff
      rw [← heq] at hview
      exact hni (view_subset_sent x k' p _ hview)

/-- An attestation that a tick put on the wire under `v`'s signature has its content in `v`'s
record after that step.

Why: the tick's attestation is the one `create_attestation` builds (Lemma 49), and the tick's
final record is the one `create_attestation` returns, which holds the attestation's content.

The variables:
- `x`: the execution; `i`: the step; `t`: the time of the tick; `v`: the signer; `a`: the
  attestation. -/
theorem attest_sent_recorded (x : AtomicExec (protocol S) Sched) {i t : ℕ} {v : V}
    {a : Attestation V}
    -- the step `i` is the tick of every awake validator at `t`
    (hl : x.lbl i = AtomicAction.tickAllAwake t)
    -- the step `i` put `v`'s signed message with the attestation `a` on the wire
    (hm : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent) :
    a.content ∈ (x[i + 1][v].st).Λ.sent := by
  obtain ⟨-, n', sent, hrun, ho, hst, -⟩ := tick_send_step_outcome hl hm
  obtain ⟨-, fi, source, -, -, hsome, hΛ⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem49_tick_attests S.C S.P S.X _ n' _ sent a hrun ho
  rw [hst, hΛ]
  exact create_attestation_content_mem hsome

/-- A step keeps every content of a validator's record.

The variables:
- `x`: the execution; `i`: the step; `v`: the validator. -/
theorem step_record_mono (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    (x[i][v].st).Λ.sent ⊆ (x[i + 1][v].st).Λ.sent := by
  rcases step_cases x i v with h | ⟨t, n', sent, -, -, hrun, h⟩ | ⟨sm, -, -, -, h⟩
  · rw [h]
  · have hΛ : (tickInputState x i t v).Λ = (x[i][v].st).Λ := by
      unfold tickInputState
      split <;> (try rw [wake_eq]) <;> rfl
    rw [h, ← hΛ]
    exact (tick_record_grows S.C S.P S.X _ _).of_outcome hrun
  · rw [h, receive_Λ]

/-- The contents of a validator's record grow along the execution.

The variables:
- `x`: the execution; `v`: the validator; `i ≤ j`: the two steps. -/
theorem record_sent_mono (x : AtomicExec (protocol S) Sched) (v : V) {i j : ℕ} (hij : i ≤ j) :
    (x[i][v].st).Λ.sent ⊆ (x[j][v].st).Λ.sent := by
  induction j, hij using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ j _ ih => exact ih.trans (step_record_mono x j v)

/-- The spec lemma for attestations, the proof; the audited statement is in
`Statements/Executions/UnforgeabilityStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `k`: the step;
  `a`: the attestation. -/
theorem attestation_from_own_tick (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (k : ℕ) (a : Attestation V)
    -- `a`'s validator's signed message with the attestation `a` is on the wire after `k` steps
    (hm : (⟨a.val_index, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[k].sent)
    (hH : HonestThrough x k a.val_index) :
    ∃ k' < k, ∃ t : ℕ, x.lbl k' = AtomicAction.tickAllAwake t ∧
      (⟨a.val_index, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
        x[k' + 1].sent - x[k'].sent ∧
      a.content ∈ (x[k' + 1][a.val_index].st).Λ.sent := by
  obtain ⟨k', hk', t, hl, hd⟩ := authored_from_own_tick x hU rfl hm hH
  exact ⟨k', hk', t, hl, hd, attest_sent_recorded x hl hd⟩

/-- The spec lemma for Goldfish votes, the proof; the audited statement is in
`Statements/Executions/UnforgeabilityStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `k`: the step;
  `vote`: the Goldfish vote. -/
theorem vote_from_own_tick (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (k : ℕ) (vote : GoldfishVote V)
    -- `vote`'s validator's signed message with the vote is on the wire after `k` steps
    (hm : (⟨vote.val_index, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[k].sent)
    (hH : HonestThrough x k vote.val_index) :
    ∃ k' < k, ∃ t : ℕ, x.lbl k' = AtomicAction.tickAllAwake t ∧
      (⟨vote.val_index, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[k' + 1].sent - x[k'].sent :=
  authored_from_own_tick x hU rfl hm hH

/-- Under unforgeability, a message on the wire after `k` steps that carries the Goldfish vote
`vote`, as its object or in the `votes` of its block, puts `vote`'s own signed message on the wire
by then, when `vote`'s validator is outside the adversary set up to the time after `k` steps.

The variables:
- `x`: the execution; `hU`: unforgeability; `k`: the step; `sm`: the message; `vote`: the vote. -/
theorem own_vote_mem_sent (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    {k : ℕ} {sm : SignedMsg V (NamedObject V)} {vote : GoldfishVote V}
    -- `sm` is on the wire after `k` steps
    (hsm : sm ∈ x[k].sent)
    -- `sm` carries `vote`, as its object or in the `votes` of the block it carries
    (hc : sm.msg = NamedObject.gfVote vote ∨
      ∃ B : Block V, sm.msg = NamedObject.block B ∧ vote ∈ B.votes)
    (hH : HonestThrough x k vote.val_index) :
    (⟨vote.val_index, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[k].sent := by
  rcases hc with hc | ⟨B, hB, hvB⟩
  · have h := hU.unforgeable k sm vote.val_index hsm (by rw [hc]; rfl) hH
    rwa [hc] at h
  · exact hU.carried k sm (.gfVote vote) vote.val_index hsm
      (by rw [hB]; exact Or.inl ⟨vote, hvB, rfl⟩) rfl hH

/-- `VotesCastByOwner` from unforgeability and permanent corruption, the proof; the audited
statement is in `Statements/Executions/UnforgeabilityStatements.lean`.

Why: a vote's validator outside the adversary set at the step's time was outside it at every
earlier time. When the step is not a tick, it keeps the time, so the message it put on the wire
and `vote`'s own signed message are on the wire after it, and `vote` came from its validator's
tick. When it is a tick, the message is the tick's own Goldfish vote, of the ticking validator, or
its proposal, whose votes were in its pool, hence on the wire before the step.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `hMono`:
  permanent corruption. -/
theorem votesCastByOwner_of_unforgeability (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hMono : Sched.MonotoneCorruption) : VotesCastByOwner S Sched x := by
  intro i sm vote hsm hc hadv
  have hH : HonestThrough x i vote.val_index := fun t' ht' ha => hadv (hMono _ _ ht' ha)
  by_cases ht : ∃ t, x.lbl i = AtomicAction.tickAllAwake t
  · obtain ⟨t, hl⟩ := ht
    obtain ⟨p, o⟩ := sm
    obtain ⟨-, n', sent, hrun, ho⟩ := tick_send_of_honestSendAt hl hsm
    rcases hc with hc | ⟨B, hB, hvB⟩
    · -- the tick's own Goldfish vote, of the ticking validator
      dsimp only at hc
      subst hc
      have hv : vote.val_index = (tickInputState x i t p).v :=
        ((tick_sends S.C S.P S.X _ _ hrun).1 vote ho).1
      have hv' : (tickInputState x i t p).v = (x[i][p].st).v := by
        unfold tickInputState
        split <;> (try rw [wake_eq]) <;> rfl
      rw [hv', (lem11_node_invariant S Sched x i p).2.1] at hv
      subst hv
      exact ⟨i, t, le_rfl, hl, hsm⟩
    · -- the tick's proposal, whose votes were in the pool
      dsimp only at hB
      subst hB
      obtain ⟨-, -, -, H, votes, support, hvotes, -, -, hBdef⟩ :=
        GoldilocksCorrectness.Statements.Routines.lem19_tick_proposes S.C S.P S.X _ n' _ sent B
          hrun ho
      rw [hBdef] at hvB
      have hvv : vote ∈ votes := hvB
      rw [hvotes, (tickInputState_frame x i t p).2.1] at hvv
      obtain ⟨i', hi', sm', hsm', hc'⟩ := pool_vote_sent x (k := i) (v := p)
        (s := S.C.slot (t : Int) - 1) ((mem_pool_iff _ _ _).2 hvv)
      have hown := own_vote_mem_sent x hU
        (mem_sent_of_le x (j := i) (mem_sent_of_mem_sub x hsm') (by omega)) hc' hH
      obtain ⟨k', hk', t', hl', hd⟩ := authored_from_own_tick x hU rfl hown hH
      exact ⟨k', t', by omega, hl', hd⟩
  · have hnt : ∀ t, x.lbl i ≠ AtomicAction.tickAllAwake t := fun t h => ht ⟨t, h⟩
    have hH1 : HonestThrough x (i + 1) vote.val_index := by
      unfold HonestThrough
      rw [time_succ_of_not_tickAllAwake x hnt]
      exact hH
    have hown := own_vote_mem_sent x hU (mem_sent_of_mem_sub x hsm) hc hH1
    obtain ⟨k', hk', t', hl', hd⟩ := authored_from_own_tick x hU rfl hown hH1
    exact ⟨k', t', by omega, hl', hd⟩

end Steps

end GoldilocksCorrectness.Proofs.Executions
