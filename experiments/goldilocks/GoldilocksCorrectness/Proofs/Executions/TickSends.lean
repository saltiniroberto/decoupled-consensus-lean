module
public import GoldilocksCorrectness.Proofs.Executions.Steps
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Proofs.Routines.DREPost
public import GoldilocksCorrectness.Proofs.Routines.Sends
public import GoldilocksCorrectness.Proofs.Routines.ACInterface
public import GoldilocksCorrectness.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Proofs.Routines.Node

@[expose] public section

/-! A Goldilocks duty sends by `broadcast`, which appends an object to
the list of objects sent so far (`Goldilocks/Broadcast.lean`). This file says what each duty
appends: the Goldfish vote duty at most one Goldfish vote, of the voter and of the slot of its
time; the tick of the available chain the same, and only at the vote time of its slot; the
proposal one block; the attestation duty at most one attestation. So a tick votes at most once,
as its own validator, for the slot of its time, and only at that slot's vote time. At the
execution level, a signed message that enters the sent log at the tick of every awake validator
is in its sender's tick's list, and two Goldfish votes of one validator for one slot that enter
the sent log at such ticks are the same vote.

## The kit

- `DREBEmits L m`: every answer of the routine `m`, run after any list `sent₀`, has the sent list
  `sent₀ ++ l` with `L l`;
- `DREBSends Q m`: every object `m` appends satisfies `Q`;
- their lemmas for a return, a bind, an `if`, a lifted routine that may fail, and `broadcast`.

## What is proved

- per routine: `goldfish_vote_sends`, `ac_on_tick_sends`, `propose_block_sends`, `attest_sends`,
  `tick_sends`;
- per step: `tick_send_of_honestSendAt`;
- along an execution: `honest_vote_sent_once`.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Proofs.Routines (DREBEmits DREBEmits.bind DREBEmits.bind_nil
  DREBEmits.broadcast_then DREBEmits.dite DREBEmits.ite DREBEmits.liftM DREBEmits.monadLift
  DREBEmits.pure NoVote TickVotes isGfVote noVote_attest_append noVote_block_append noVote_nil
  tickVotes_of_append)

open GoldilocksCorrectness.Proofs.Routines (ac_on_tick_sends)

open GoldilocksCorrectness.Proofs.Routines (tick_sends)

namespace GoldilocksCorrectness.Proofs.Executions

open Goldilocks
open GoldilocksCorrectness.Statements.Executions

/-! ## The kit -/

section Kit

variable {V : Type}

end Kit

/-! ## The routines -/

section Routines

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- A block is not a Goldfish vote. -/
theorem isGfVote_block (B : Block V) : isGfVote (NamedObject.block B) = false := rfl

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- An attestation is not a Goldfish vote. -/
theorem isGfVote_attest (a : Attestation V) : isGfVote (NamedObject.attest a) = false := rfl

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- Two Goldfish votes of a list that holds at most one Goldfish vote are the same vote.

The variables:
- `l`: the list; `vote`, `vote'`: the two votes. -/
theorem eq_of_filter_isGfVote {l : List (NamedObject V)} {vote vote' : GoldfishVote V}
    (hl : (l.filter isGfVote).length ≤ 1) (hv : NamedObject.gfVote vote ∈ l)
    (hv' : NamedObject.gfVote vote' ∈ l) : vote = vote' := by
  have h1 : NamedObject.gfVote vote ∈ l.filter isGfVote := List.mem_filter.mpr ⟨hv, rfl⟩
  have h2 : NamedObject.gfVote vote' ∈ l.filter isGfVote := List.mem_filter.mpr ⟨hv', rfl⟩
  generalize l.filter isGfVote = l' at hl h1 h2
  match l', hl, h1, h2 with
  | [o], _, h1, h2 =>
      rw [List.mem_singleton] at h1 h2
      rw [← h2] at h1
      injection h1

end Routines

/-! ## The steps -/

section Steps

open Framework.StsMultisetLog (AtomicAction AtomicExec Schedule SignedMsg TickAllAwakeWake
  tickAllAwakeUpdate_getElem_react)
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol step_tick_iff step_wake_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder] {S : Setup V} {Sched : Schedule V}

/-- A signed message that enters the sent log at the tick of every awake validator at `t` is
signed by a validator awake and outside the adversary set at `t`; its object is in the list sent
by an `.ok` outcome of that validator's tick, from the node state the tick starts from; the
validator holds that outcome's node state after the step; and every object the step put on the
wire under the validator's signature is in that list. The wake stage sends nothing.

Why: the step gives the validator one reaction of its tick (`step_tick_iff`); what the step puts on
the wire under the validator's signature is that reaction's sends, and the validator's node state
after the step is that reaction's state.

The variables:
- `x`: the execution; `i`: the step; `t`: the time of the tick; `p`: the signer; `o`: the object;
- `n'`, `sent`: the outcome of `p`'s tick, the node state and the objects sent.

Read aloud: what a tick puts on the wire was sent by an honest awake validator's tick, in one
outcome, whose node state the validator then holds and which sent everything the step put on the
wire under its signature. -/
theorem tick_send_step_outcome {x : AtomicExec (protocol S) Sched} {i t : ℕ} {p : V}
    {o : NamedObject V}
    -- the step `i` is the tick of every awake validator at `t`
    (hl : x.lbl i = AtomicAction.tickAllAwake t)
    -- the step `i` put `⟨p, o⟩` on the wire
    (hm : (⟨p, o⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    p ∈ Sched.awake (t : Int) \ Sched.adv (t : Int) ∧
      ∃ (n' : NodeState V) (sent : List (NamedObject V)),
        .ok (n', sent) ∈ (tick S.C S.P S.X (tickInputState x i t p) (t : Int)).outcomes ∧
          o ∈ sent ∧ x[i + 1][p].st = n' ∧
          ∀ o' : NamedObject V,
            (⟨p, o'⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent → o' ∈ sent := by
  have hs := x.step i
  rw [hl] at hs
  obtain ⟨-, w, tk, hw, htk, hc⟩ := hs
  -- the wake stage sends nothing, and leaves the state the tick starts from
  have hwq : ∀ q : V, (w q).send = 0 ∧ (w q).state = tickInputState x i t q := by
    intro q
    have hw' := hw q
    unfold TickAllAwakeWake at hw'
    unfold tickInputState
    split at hw'
    · rename_i he
      rw [if_pos he, (step_wake_iff S q _ _ _ _).1 hw']
      exact ⟨rfl, rfl⟩
    · rename_i he
      rw [if_neg he, hw']
      exact ⟨rfl, rfl⟩
  -- what the step puts on the wire under `q`'s signature is what `q`'s tick reaction sends
  have hput : ∀ (q : V) (o' : NamedObject V),
      (⟨q, o'⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent →
        q ∈ Sched.awake (t : Int) \ Sched.adv (t : Int) ∧ o' ∈ (tk q).send := by
    intro q o' h
    have hsent : x[i + 1].sent = x[i].sent + (Sched.awake (t : Int) \ Sched.adv (t : Int)).sum
        (fun q => ((w q).send + (tk q).send).map (SignedMsg.mk q)) := by
      show (x.cfg (i + 1)).sent = _
      rw [hc]
      rfl
    rw [hsent, add_tsub_cancel_left] at h
    obtain ⟨q', hq', hmq⟩ := Multiset.mem_sum.1 h
    obtain ⟨m', hm', heq⟩ := Multiset.mem_map.1 hmq
    injection heq with hqv hmo
    subst hqv hmo
    rw [(hwq _).1, zero_add] at hm'
    exact ⟨hq', hm'⟩
  obtain ⟨hq, hmo⟩ := hput p o hm
  have hst : x[i + 1][p].st = (tk p).state := by
    show (x.cfg (i + 1))[p].st = _
    rw [hc]
    exact congrArg Framework.StsMultisetLog.Local.st (tickAllAwakeUpdate_getElem_react hq)
  have htk' := (step_tick_iff S p t _ _ _).1 (htk p hq)
  rw [(hwq p).2] at htk'
  refine ⟨hq, ?_⟩
  rcases htk' with ⟨n', sent, hok, hres⟩ | ⟨-, hres⟩
  · rw [hres] at hmo hst
    refine ⟨n', sent, hok, Multiset.mem_coe.1 hmo, hst, fun o' ho' => ?_⟩
    have h' := (hput p o' ho').2
    rw [hres] at h'
    exact Multiset.mem_coe.1 h'
  · rw [hres] at hmo
    simp at hmo

/-- A signed message that enters the sent log at the tick of every awake validator at `t` is
signed by a validator awake and outside the adversary set at `t`, and its object is in the list
sent by an `.ok` outcome of that validator's tick, from the node state the tick starts from. The
wake stage sends nothing.

The variables:
- `x`: the execution; `i`: the step; `t`: the time of the tick; `p`: the signer; `o`: the object;
- `n'`, `sent`: the outcome of `p`'s tick, the node state and the objects sent.

Read aloud: what a tick puts on the wire is what an honest awake validator's tick sent. -/
theorem tick_send_of_honestSendAt {x : AtomicExec (protocol S) Sched} {i t : ℕ} {p : V}
    {o : NamedObject V}
    -- the step `i` is the tick of every awake validator at `t`
    (hl : x.lbl i = AtomicAction.tickAllAwake t)
    -- the step `i` put `⟨p, o⟩` on the wire
    (hm : (⟨p, o⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    p ∈ Sched.awake (t : Int) \ Sched.adv (t : Int) ∧
      ∃ (n' : NodeState V) (sent : List (NamedObject V)),
        .ok (n', sent) ∈ (tick S.C S.P S.X (tickInputState x i t p) (t : Int)).outcomes ∧
          o ∈ sent := by
  obtain ⟨hp, n', sent, hok, ho, -, -⟩ := tick_send_step_outcome hl hm
  exact ⟨hp, n', sent, hok, ho⟩

/-- A validator's Goldfish votes for one slot, each put on the wire by the validator at the tick
of every awake validator at some time, are one vote: each tick's vote is for the slot of its time
and sent only at that slot's vote time, so the two ticks are at the same time, hence the same step
(`tickAllAwake_unique`), and that tick sends at most one Goldfish vote.

The variables:
- `x`: the execution; `i`, `j`: the two steps; `t`, `t'`: their times; `u`: the validator;
  `vote`, `vote'`: the two votes.

Read aloud: an honest validator's ticks put at most one Goldfish vote per slot on the wire. -/
theorem honest_vote_sent_once {x : AtomicExec (protocol S) Sched} {i j t t' : ℕ} {u : V}
    {vote vote' : GoldfishVote V}
    -- the steps `i` and `j` are the ticks of every awake validator at `t` and `t'`
    (hi : x.lbl i = AtomicAction.tickAllAwake t) (hj : x.lbl j = AtomicAction.tickAllAwake t')
    -- `u` put `vote` on the wire at `i`, and `vote'` at `j`
    (hsi : (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent)
    (hsj : (⟨u, NamedObject.gfVote vote'⟩ : SignedMsg V (NamedObject V)) ∈
      x[j + 1].sent - x[j].sent)
    -- the two votes are for the same slot
    (hslot : vote.slot = vote'.slot) : vote = vote' := by
  obtain ⟨-, n₁, sent₁, hrun₁, hm₁⟩ := tick_send_of_honestSendAt hi hsi
  obtain ⟨-, n₂, sent₂, hrun₂, hm₂⟩ := tick_send_of_honestSendAt hj hsj
  obtain ⟨hv₁, -⟩ := tick_sends S.C S.P S.X _ _ hrun₁
  obtain ⟨hv₂, -⟩ := tick_sends S.C S.P S.X _ _ hrun₂
  have hrun₁' := DREB.run_eq_of_mem_outcomes hrun₁
  have hrun₂' := DREB.run_eq_of_mem_outcomes hrun₂
  obtain ⟨-, hs₁, ht₁⟩ := hv₁ vote hm₁
  obtain ⟨-, hs₂, ht₂⟩ := hv₂ vote' hm₂
  have htt : (t : Int) = (t' : Int) := by
    rw [ht₁, ht₂, ← hs₁, ← hs₂, hslot]
  have htt' : t = t' := by exact_mod_cast htt
  subst htt'
  have hij : i = j := tickAllAwake_unique x hi hj
  subst hij
  rw [hrun₁'] at hrun₂'
  have hsent : sent₁ = sent₂ := by
    simp only [Except.ok.injEq, Prod.mk.injEq] at hrun₂'
    exact hrun₂'.2
  subst hsent
  exact eq_of_filter_isGfVote (tick_sends S.C S.P S.X _ _ hrun₁).2 hm₁ hm₂

end Steps

end GoldilocksCorrectness.Proofs.Executions
