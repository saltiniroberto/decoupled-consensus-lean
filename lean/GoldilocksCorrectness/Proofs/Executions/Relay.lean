module
public import GoldilocksCorrectness.Proofs.Executions.VoteDelivery
public import GoldilocksCorrectness.Statements.Routines.ProposalStatements
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.ACInterface
public import GoldilocksCorrectness.Proofs.Routines.ACStore
public import GoldilocksCorrectness.Proofs.Routines.Wiring

@[expose] public section

/-! The wiring re-sends every delivered object, and a block's Goldfish votes each as an
object of its own (`Goldilocks.Sts.relayedObjects`). So a Goldfish vote in an honest validator's
pool, or included in a block of its tree, was put on the wire by that validator itself as a
Goldfish-vote object, at a step at which it was honest, at a time from the start of the vote's
slot on; and such a re-send reaches every validator awake and honest for a delay after it, which
admits the vote or already holds two votes of the vote's validator for its slot. None of this
reads the honesty of the vote's own validator.

## The times

- `viewFreeze_cast`, `viewFreeze_eq`: the view freeze read back as a natural number;
- `slotStart_le_iff`: a time is at least the start of slot `s` exactly when its slot is at least
  `s`.

## The admission's slot

- `on_goldfish_vote_new_slot`, `ac_on_block_new_slot`, `receive_new_slot`: a vote a receipt adds
  to the pool has a slot at most the slot of the node's clock.

## What is proved along an execution

- `pool_vote_relayed`, `pool_vote_relayed_before`: a vote of a validator's pool was re-sent by it;
- `included_vote_relayed_before`: a vote included in a block of a validator's tree was re-sent by
  it;
- `relayed_vote_in_pool_before_add_delay`: such a re-send reaches every validator awake and
  honest for a delay;
- `pool_vote_reaches_before_add_delay`: so a vote of an honest validator's pool before a time `t`
  is, one delay later, in the pool of every validator awake and honest for that delay;
- `relayed_vote_in_pool_before_add_delay_upTo`, `pool_vote_reaches_before_add_delay_upTo`: the
  same two on the delivery premises restricted to the deadlines up to a bound `tR` at least
  `t + Δ S`; the two above are their instances.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_le_iff slot_mono_int voteTime_cast
  voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (Carried DREBSpec.of_outcome forIn_yield_inv)

open GoldilocksCorrectness.Proofs.Routines (ac_on_block_new_slot on_goldfish_vote_new_slot
  receive_gfVote_cases two_votes_of_equivocates)

open GoldilocksCorrectness.Proofs.Routines (on_attestation_frame on_block_eq tick_prov tick_sends)

open GoldilocksCorrectness.Proofs.Routines (gfVote_mem_relayedObjects
  gfVote_mem_relayedObjects_block receive_new receive_new_slot)

open GoldilocksCorrectness.Proofs.Routines (acState_initial_eq block_well_formed_iff
  fgState_initial_eq initial_eq mem_pool_iff on_ac_message_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Goldilocks
open GoldilocksCorrectness.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The times -/

section Times

open Goldilocks.Sts (Setup)

end Times

/-! ## The admission's slot -/

section Admission

variable [RootOrder]

end Admission

/-! ## Along an execution -/

section Relays

open Framework.StsMultisetLog (AtomicAction AtomicExec Schedule SignedMsg)
open Goldilocks.Sts (Setup relayedObjects)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Proofs.Routines (ac_valid_payload_facts)

variable [RootOrder]

/-- A Goldfish vote that enters a validator's pool of slot `s` at the step `k` was put on the wire
by that validator at that step, as a Goldfish-vote object; the validator was honest at the step's
time; and that time is at least the start of slot `s`.

Why: the step is the validator's tick or a delivery to it. A tick adds a vote only as its own
Goldfish vote, sent at the vote time of its slot (a block it proposes holds only votes of its
pool, `lem19_tick_proposes`); a delivery adds only votes the delivered object carries, which the
wiring re-sends each as an object, and admits a vote only up to the current slot.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `k`: the step; `w`: the validator;
  `s`: the slot; `vote`: the vote. -/
theorem step_pool_relayed (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hMono : Sched.MonotoneCorruption)
    {k : ℕ} {w : V} {s : Slot} {vote : GoldfishVote V}
    -- `vote` is in `w`'s votes of slot `s` after the step
    (hv : vote ∈ (x[k + 1][w].st).A.gf_votes s)
    -- `vote` is not in `w`'s votes of slot `s` before the step
    (hn : vote ∉ (x[k][w].st).A.gf_votes s) :
    (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent - x[k].sent ∧
      w ∉ Sched.adv (x[k].time : Int) ∧ slotStart S s ≤ x[k].time := by
  have hslot : vote.slot = s :=
    ((GoldilocksCorrectness.Statements.Executions.lem11_node_invariant S Sched x (k + 1) w).1.1
      s vote hv).1
  rcases step_cases x k w with h | ⟨t, n', sent, hl, hmem, hrun, h⟩ | ⟨sm, hl, -, hadv, h⟩
  · rw [h] at hv
    exact absurd hv hn
  · -- the validator's tick at `t`
    have hkt : x[k].time + 1 = t := (time_of_lbl_tickAllAwake x hl).1
    rw [h] at hv
    obtain ⟨-, hA, -⟩ := tickInputState_frame x k t w
    obtain ⟨hP, -⟩ := DREBSpec.of_outcome (tick_prov S.C S.P S.X _ (t : Int)) hrun
    obtain ⟨o, ho, hc⟩ := hP.1 s vote hv (by rw [hA]; exact hn)
    rcases hc with rfl | ⟨B', rfl, hvB⟩
    · -- the tick's own Goldfish vote, sent at the vote time of its slot
      refine ⟨step_sent_of_tick_send hl hmem hrun ho,
        fun ha => (Finset.mem_sdiff.1 hmem).2 (hMono _ _ (by omega) ha), ?_⟩
      obtain ⟨-, hs, ht⟩ := (tick_sends S.C S.P S.X _ (t : Int) hrun).1 vote ho
      rw [← hs, hslot] at ht
      have hvt : voteTime S s = t := by
        have h1 : ((voteTime S s : ℕ) : Int) = S.C.t_ s + S.C.Δ := voteTime_cast S s
        exact_mod_cast h1.trans ht.symm
      have h2 := voteTime_eq S s
      have h3 := one_le_Δ S
      omega
    · -- a block the tick proposes holds only votes of the pool
      exfalso
      obtain ⟨-, -, -, H, votes, support, hvotes, -, -, hB⟩ :=
        GoldilocksCorrectness.Statements.Routines.lem19_tick_proposes S.C S.P S.X _ n' _ sent B'
          hrun ho
      rw [hB] at hvB
      have hvv : vote ∈ votes := hvB
      rw [hvotes, hA] at hvv
      have hs' : vote.slot = S.C.slot (t : Int) - 1 :=
        ((GoldilocksCorrectness.Statements.Executions.lem11_node_invariant S Sched x k w).1.1
          _ vote hvv).1
      rw [← hs', hslot] at hvv
      exact hn hvv
  · -- a delivery to the validator
    rw [h] at hv
    have hc := (receive_new S.C S.P S.X _ sm.msg).1 s vote hv hn
    have hle := receive_new_slot S.C S.P S.X _ sm.msg s vote hv hn
    rw [(slot_current_at_delivery hl).2, hslot] at hle
    exact ⟨step_sent_of_delivery hl (gfVote_mem_relayedObjects hc), hadv,
      (slotStart_le_iff S s _).2 hle⟩

/-- A Goldfish vote of a validator's pool at a step was put on the wire by that validator, as a
Goldfish-vote object, at an earlier step, at which it was honest, at a time at least the start of
the vote's slot.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `k`: the step; `w`: the validator;
  `s`: the slot; `vote`: the vote; `i`: the step of the re-send.

Read aloud: a vote `w` holds was re-sent by `w`, honest then, after its slot began. -/
theorem pool_vote_relayed (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hMono : Sched.MonotoneCorruption)
    (k : ℕ) (w : V) (s : Slot) (vote : GoldfishVote V)
    (hv : vote ∈ (x[k][w].st).A.pool s) :
    ∃ i < k,
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent ∧
      w ∉ Sched.adv (x[i].time : Int) ∧ slotStart S s ≤ x[i].time := by
  induction k with
  | zero =>
      rw [getElem_zero_st, initial_eq, acState_initial_eq] at hv
      exact absurd ((mem_pool_iff _ _ _).1 hv) List.not_mem_nil
  | succ k ih =>
      by_cases hk : vote ∈ (x[k][w].st).A.pool s
      · obtain ⟨i, hi, h⟩ := ih hk
        exact ⟨i, by omega, h⟩
      · exact ⟨k, by omega, step_pool_relayed S Sched x hMono ((mem_pool_iff _ _ _).1 hv)
          (fun h => hk ((mem_pool_iff _ _ _).2 h))⟩

/-- A Goldfish vote of a validator's pool before the time `t` was put on the wire by that
validator, as a Goldfish-vote object, at a step before `stepBefore x t`, at which it was honest, at
a time at least the start of the vote's slot.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `w`: the validator;
  `s`: the slot; `vote`: the vote; `i`: the step of the re-send.

Read aloud: a vote `w` holds before `t` was re-sent by `w` before `t`. -/
theorem pool_vote_relayed_before (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hMono : Sched.MonotoneCorruption)
    (t : ℕ) (w : V) (s : Slot) (vote : GoldfishVote V)
    (hv : vote ∈ (stateBefore x t w).A.pool s) :
    ∃ i < stepBefore x t,
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent ∧
      w ∉ Sched.adv (x[i].time : Int) ∧ slotStart S s ≤ x[i].time :=
  pool_vote_relayed S Sched x hMono (stepBefore x t) w s vote hv

/-- A Goldfish vote included in a non-genesis block of a validator's tree before the time `t` was
put on the wire by that validator, as a Goldfish-vote object, at a step before `stepBefore x t`, at
which it was honest, at a time at least the start of the vote's slot.

Why: at the step the block entered the tree, the validator either received it, and the wiring
re-sent each of its votes as an object, or proposed it, and its votes were already in its pool,
which the validator re-sent earlier (`pool_vote_relayed`). A received block's votes are of the slot
before the block's, which is at most the slot of the validator's clock.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `w`: the validator;
  `B'`: the block; `vote`: a vote it includes; `i`: the step of the re-send.

Read aloud: a vote included in a block `w` holds before `t` was re-sent by `w` before `t`. -/
theorem included_vote_relayed_before (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hMono : Sched.MonotoneCorruption)
    (t : ℕ) (w : V) (B' : Block V) (vote : GoldfishVote V)
    (hB : B' ∈ (stateBefore x t w).S.T) (hne : B' ≠ Block.genesis) (hvote : vote ∈ B'.votes) :
    ∃ i < stepBefore x t,
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent ∧
      w ∉ Sched.adv (x[i].time : Int) ∧ slotStart S vote.slot ≤ x[i].time := by
  classical
  -- the step at which `B'` entered `w`'s tree
  have hex : ∃ m : ℕ, B' ∈ (x[m][w].st).S.T := ⟨stepBefore x t, hB⟩
  have h0 : B' ∉ (x[0][w].st).S.T := by
    rw [getElem_zero_st, initial_eq, fgState_initial_eq]
    intro h
    exact hne (Finset.mem_singleton.1 h)
  have hpos : Nat.find hex ≠ 0 := by
    intro h
    exact h0 (h ▸ Nat.find_spec hex)
  have hle : Nat.find hex ≤ stepBefore x t := Nat.find_min' hex hB
  obtain ⟨i, hi⟩ : ∃ i : ℕ, Nat.find hex = i + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hni : B' ∉ (x[i][w].st).S.T := Nat.find_min hex (by omega)
  have hi1 : B' ∈ (x[i + 1][w].st).S.T := hi ▸ Nat.find_spec hex
  have hit : i < stepBefore x t := by omega
  rcases step_cases x i w with h | ⟨t', n', sent, hl, hmem, hrun, h⟩ | ⟨sm, hl, -, hadv, h⟩
  · rw [h] at hi1
    exact absurd hi1 hni
  · -- `w` proposed `B'` at its tick: `B'`'s votes were in its pool
    have hBn := hi1
    rw [h] at hBn
    obtain ⟨hS, hA, -⟩ := tickInputState_frame x i t' w
    obtain ⟨hP, -⟩ := DREBSpec.of_outcome (tick_prov S.C S.P S.X _ (t' : Int)) hrun
    obtain ⟨hBs, -⟩ := hP.2 B' hBn (by rw [hS]; exact hni)
    obtain ⟨-, -, -, H, votes, support, hvotes, -, -, hBdef⟩ :=
      GoldilocksCorrectness.Statements.Routines.lem19_tick_proposes S.C S.P S.X _ n' _ sent B'
        hrun hBs
    rw [hBdef] at hvote
    have hvv : vote ∈ votes := hvote
    rw [hvotes, hA] at hvv
    have hs' : vote.slot = S.C.slot (t' : Int) - 1 :=
      ((GoldilocksCorrectness.Statements.Executions.lem11_node_invariant S Sched x i w).1.1
        _ vote hvv).1
    obtain ⟨j, hj, hsend, hhon, hstart⟩ := pool_vote_relayed S Sched x hMono i w
      (S.C.slot (t' : Int) - 1) vote ((mem_pool_iff _ _ _).2 hvv)
    refine ⟨j, by omega, hsend, hhon, ?_⟩
    rw [hs']
    exact hstart
  · -- `w` received `B'`, and re-sent each of its votes
    have hnt : ∀ t'', x.lbl i ≠ AtomicAction.tickAllAwake t'' := by
      intro t'' h'
      rw [hl] at h'
      cases h'
    have hi1' := hi1
    rw [h] at hi1'
    obtain ⟨hmsg, -⟩ := (receive_new S.C S.P S.X _ sm.msg).2 B' hi1' hni
    have hsend : (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent := by
      refine step_sent_of_delivery hl ?_
      rw [hmsg]
      exact gfVote_mem_relayedObjects_block hvote
    -- the slot: `vote.slot = B'.slot - 1 ≤ B'.slot ≤` the slot of `w`'s clock after the step
    have hwf := (((GoldilocksCorrectness.Statements.Executions.lem11_node_invariant S Sched x
      (i + 1) w).1.2.2.1).2 B' hi1 hne)
    have hwf' := hwf.2.1
    rw [block_well_formed_iff] at hwf'
    have hvs : vote.slot = B'.slot - 1 :=
      (ac_valid_payload_facts S.P B' hwf'.1.2).1 vote hvote
    obtain ⟨-, -, hBslot⟩ := step_tree_new x hi1 hni
    have hclock : S.C.slot (x[i + 1][w].st).t ≤ S.C.slot ((x[i].time : ℕ) : Int) := by
      refine slot_mono_int S (le_trans (clock_le_time x (i + 1) w) ?_)
      rw [time_succ_of_not_tickAllAwake x hnt]
    refine ⟨i, hit, hsend, hadv, (slotStart_le_iff S _ _).2 ?_⟩
    rw [hvs]
    exact le_trans (Nat.sub_le _ _) (le_trans hBslot hclock)

/-- A Goldfish vote that a validator `w`, honest at the step `i`, put on the wire there, at a time
at least the start of the vote's slot and at most `t ≥ GST`, with `t + Δ S` strictly before the
start of slot `vote.slot + 2` and the vote's validator in its slot's committee, is in the pool of
every validator `v` awake and honest at every time from `t` to `t + Δ S`, before `t + Δ S`; or `v`
then holds two distinct votes of the vote's validator for the vote's slot.

Why: as `vote_in_pool_before_add_delay`, with `w`'s re-send as the honest send: the network
delivers it to `v` strictly before `t + Δ S`, at a time whose slot is the vote's or the next, so
the admission keeps the vote unless `v` already holds two votes of its validator.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `i`: the step of the re-send; `t`: the time; `w`: the sender; `v`: the
  receiver; `vote`: the vote.

Read aloud: a vote an honest validator re-sent by `t` reaches every validator awake and honest for
a delay from `t`, which admits it or already holds two votes of its validator.

Restated with the delivery premises up to `tR`, the latest deadline being `t + Δ S` (the
re-send reaching `v`), so `htR : t + Δ S ≤ tR`; `relayed_vote_in_pool_before_add_delay` is its
instance. -/
theorem relayed_vote_in_pool_before_add_delay_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption) (GST : ℕ) {tR : ℕ}
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject tR)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject tR)
    (i t : ℕ) (w v : V) (vote : GoldfishVote V)
    -- `w`, honest at the step `i`, put `vote` on the wire there, at a time at least the start of
    -- the vote's slot and at most `t`
    (hsent : (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent)
    (hwh : w ∉ Sched.adv (x[i].time : Int))
    (hlo : slotStart S vote.slot ≤ x[i].time) (hit : x[i + 1].time ≤ t)
    (hGST : GST ≤ t)
    -- the vote's validator is in its slot's committee
    (hcomm : vote.val_index ∈ S.P.committee vote.slot)
    -- `t + Δ S` is strictly before the start of slot `vote.slot + 2`
    (hhi : t + Δ S < slotStart S (vote.slot + 2))
    -- `v` is awake and honest at every time from `t` to `t + Δ S`
    (hv : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ S →
      v ∈ Sched.awake (t' : Int) ∧ v ∉ Sched.adv (t' : Int))
    -- the latest deadline the proof reads is at most the bound
    (htR : t + Δ S ≤ tR) :
    vote ∈ (stateBefore x (t + Δ S) v).A.pool vote.slot ∨
      ∃ v₁ ∈ (stateBefore x (t + Δ S) v).A.pool vote.slot,
        ∃ v₂ ∈ (stateBefore x (t + Δ S) v).A.pool vote.slot,
          v₁ ≠ v₂ ∧ v₁.val_index = vote.val_index ∧ v₂.val_index = vote.val_index := by
  obtain ⟨d, hid, hld, hdt⟩ := delivered_before_of_honest_send_upTo x
    (SynchronyFromWakeUpTo.mono htR hSync) (CatchUpOnWakeUpTo.mono htR hCatch)
    hMono (sm := ⟨w, NamedObject.gfVote vote⟩) ⟨hsent, hwh⟩ trivial hit hGST hv
  have hd : d < stepBefore x (t + Δ S) := deliver_before_of_time x hDiv hld hdt
  obtain ⟨-, -, hstep⟩ := deliver_step_state x hld
  have hclock := (slot_current_at_delivery hld).1
  -- the delivery's time is from the re-send's on and strictly before `t + Δ S`
  have hdlo : x[i].time ≤ x[d].time := time_mono x (le_of_lt hid)
  have hdhi : x[d].time < t + Δ S :=
    lt_of_le_of_lt (time_le_succ x d) ((lt_stepBefore_iff x hDiv).1 hd)
  -- so its slot is the vote's slot or the next
  have hs2 : vote.slot ≤ S.C.slot (x[d][v].st).t := by
    rw [hclock]
    exact (slotStart_le_iff S _ _).1 (le_trans hlo hdlo)
  have hs1 : S.C.slot (x[d][v].st).t ≤ vote.slot + 1 := by
    rw [hclock]
    by_contra hlt
    have h2 : vote.slot + 2 ≤ S.C.slot ((x[d].time : ℕ) : Int) := Nat.lt_of_not_le hlt
    have h3 := (slotStart_le_iff S _ _).2 h2
    omega
  have hA : (x[d + 1][v].st).A =
      on_goldfish_vote S.C S.P (x[d][v].st).A (x[d][v].st).t vote := by
    rw [hstep]
    show (on_ac_message _ _ _ vote).A = _
    rw [on_ac_message_eq]
  rcases receive_gfVote_cases S.C S.P (x[d][v].st).A (x[d][v].st).t vote hs1 hs2 hcomm with
    hin | heqv
  · left
    exact pool_mono x v hd vote.slot (hA ▸ hin)
  · right
    obtain ⟨v₁, h₁, v₂, h₂, hne, hi₁, hi₂⟩ := two_votes_of_equivocates heqv
    exact ⟨v₁, pool_mono x v (le_of_lt hd) _ h₁, v₂, pool_mono x v (le_of_lt hd) _ h₂, hne, hi₁,
      hi₂⟩

/-- A Goldfish vote that a validator `w`, honest at the step `i`, put on the wire there, at a time
at least the start of the vote's slot and at most `t ≥ GST`, with `t + Δ S` strictly before the
start of slot `vote.slot + 2` and the vote's validator in its slot's committee, is in the pool of
every validator `v` awake and honest at every time from `t` to `t + Δ S`, before `t + Δ S`; or `v`
then holds two distinct votes of the vote's validator for the vote's slot.

Why: `relayed_vote_in_pool_before_add_delay_upTo` at the bound `t + Δ S`, with the two premises
restricted to the deadlines up to it.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `i`: the step of the re-send; `t`: the time; `w`: the sender; `v`: the
  receiver; `vote`: the vote.

Read aloud: a vote an honest validator re-sent by `t` reaches every validator awake and honest for
a delay from `t`, which admits it or already holds two votes of its validator. -/
theorem relayed_vote_in_pool_before_add_delay (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption) (GST : ℕ)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (i t : ℕ) (w v : V) (vote : GoldfishVote V)
    -- `w`, honest at the step `i`, put `vote` on the wire there, at a time at least the start of
    -- the vote's slot and at most `t`
    (hsent : (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent)
    (hwh : w ∉ Sched.adv (x[i].time : Int))
    (hlo : slotStart S vote.slot ≤ x[i].time) (hit : x[i + 1].time ≤ t)
    (hGST : GST ≤ t)
    -- the vote's validator is in its slot's committee
    (hcomm : vote.val_index ∈ S.P.committee vote.slot)
    -- `t + Δ S` is strictly before the start of slot `vote.slot + 2`
    (hhi : t + Δ S < slotStart S (vote.slot + 2))
    -- `v` is awake and honest at every time from `t` to `t + Δ S`
    (hv : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ S →
      v ∈ Sched.awake (t' : Int) ∧ v ∉ Sched.adv (t' : Int)) :
    vote ∈ (stateBefore x (t + Δ S) v).A.pool vote.slot ∨
      ∃ v₁ ∈ (stateBefore x (t + Δ S) v).A.pool vote.slot,
        ∃ v₂ ∈ (stateBefore x (t + Δ S) v).A.pool vote.slot,
          v₁ ≠ v₂ ∧ v₁.val_index = vote.val_index ∧ v₂.val_index = vote.val_index :=
  relayed_vote_in_pool_before_add_delay_upTo S Sched x hDiv hMono GST
    (synchronyFromWakeUpTo_of_synchronyFromWake (t + Δ S) hSync)
    (catchUpOnWakeUpTo_of_catchUpOnWake (t + Δ S) hCatch) i t w v vote hsent hwh hlo hit
    hGST hcomm hhi hv le_rfl

/-- A slot-`s` Goldfish vote in `a`'s pool before the time `t` is in `b`'s pool of slot `s`
before `t + Δ S`, or `b`'s pool then holds two distinct votes of the vote's validator, when the
network is synchronous from `t`, `t + Δ S` is strictly before the start of slot `s + 2`, and `b`
is awake and honest at every time from `t` to `t + Δ S`.

Why: `a` re-sent the vote at a step at a time less than `t` (`pool_vote_relayed_before`), and that
re-send reaches `b` before `t + Δ S` (`relayed_vote_in_pool_before_add_delay`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `t`: the time; `s`: the slot of the vote; `a`: the holder; `b`: the
  receiver; `vote`: the vote.

Read aloud: a vote one validator holds is, one delay later, held by every validator awake and
honest for that delay, unless that validator holds two votes of the vote's validator.

Restated with the delivery premises up to `tR`, the latest deadline being `t + Δ S` (`a`'s
re-send reaching `b`), so `htR : t + Δ S ≤ tR`; `pool_vote_reaches_before_add_delay` is its
instance. -/
theorem pool_vote_reaches_before_add_delay_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption) (GST : ℕ) {tR : ℕ}
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject tR)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject tR)
    (t s : ℕ) (a b : V) (vote : GoldfishVote V)
    -- the network is synchronous from `t` on, so the re-send reaches `b` within one delay
    (hGST : GST ≤ t)
    -- `t + Δ S` is strictly before the start of slot `s + 2`, so `b` still admits the vote
    (hhi : t + Δ S < slotStart S (s + 2))
    -- `b` is awake and honest at every time from `t` to `t + Δ S`, to receive the re-send
    (hb : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ S →
      b ∈ Sched.awake (t' : Int) ∧ b ∉ Sched.adv (t' : Int))
    -- `a`'s pool of slot `s` before `t` holds `vote`
    (hvote : vote ∈ (stateBefore x t a).A.pool s)
    -- the latest deadline the proof reads is at most the bound
    (htR : t + Δ S ≤ tR) :
    vote ∈ (stateBefore x (t + Δ S) b).A.pool s ∨
      ∃ v₁ ∈ (stateBefore x (t + Δ S) b).A.pool s,
        ∃ v₂ ∈ (stateBefore x (t + Δ S) b).A.pool s,
          v₁ ≠ v₂ ∧ v₁.val_index = vote.val_index ∧ v₂.val_index = vote.val_index := by
  -- the vote's slot and committee
  have hs' : vote.slot = s := pool_slot_of_stateBefore S Sched x _ a s vote hvote
  have hcomm : vote.val_index ∈ S.P.committee s :=
    pool_committee_of_stateBefore S Sched x _ a s vote hvote
  -- `a`'s re-send, at a time less than `t`
  obtain ⟨j, hj, hsend, hhon, hlo⟩ :=
    pool_vote_relayed_before S Sched x hMono _ a s vote hvote
  have hjt : x[j + 1].time < t := (lt_stepBefore_iff x hDiv).1 hj
  -- its delivery to `b`, before `t + Δ S`
  have hres := relayed_vote_in_pool_before_add_delay_upTo S Sched x hDiv hMono GST hSync hCatch
    j t a b vote hsend hhon (by rw [hs']; exact hlo) (le_of_lt hjt) hGST
    (by rw [hs']; exact hcomm) (by rw [hs']; exact hhi) hb htR
  rw [hs'] at hres
  exact hres

/-- A slot-`s` Goldfish vote in `a`'s pool before the time `t` is in `b`'s pool of slot `s`
before `t + Δ S`, or `b`'s pool then holds two distinct votes of the vote's validator, when the
network is synchronous from `t`, `t + Δ S` is strictly before the start of slot `s + 2`, and `b`
is awake and honest at every time from `t` to `t + Δ S`.

Why: `pool_vote_reaches_before_add_delay_upTo` at the bound `t + Δ S`, with the two premises
restricted to the deadlines up to it.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `t`: the time; `s`: the slot of the vote; `a`: the holder; `b`: the
  receiver; `vote`: the vote.

Read aloud: a vote one validator holds is, one delay later, held by every validator awake and
honest for that delay, unless that validator holds two votes of the vote's validator. -/
theorem pool_vote_reaches_before_add_delay (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption) (GST : ℕ)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (t s : ℕ) (a b : V) (vote : GoldfishVote V)
    -- the network is synchronous from `t` on, so the re-send reaches `b` within one delay
    (hGST : GST ≤ t)
    -- `t + Δ S` is strictly before the start of slot `s + 2`, so `b` still admits the vote
    (hhi : t + Δ S < slotStart S (s + 2))
    -- `b` is awake and honest at every time from `t` to `t + Δ S`, to receive the re-send
    (hb : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ S →
      b ∈ Sched.awake (t' : Int) ∧ b ∉ Sched.adv (t' : Int))
    -- `a`'s pool of slot `s` before `t` holds `vote`
    (hvote : vote ∈ (stateBefore x t a).A.pool s) :
    vote ∈ (stateBefore x (t + Δ S) b).A.pool s ∨
      ∃ v₁ ∈ (stateBefore x (t + Δ S) b).A.pool s,
        ∃ v₂ ∈ (stateBefore x (t + Δ S) b).A.pool s,
          v₁ ≠ v₂ ∧ v₁.val_index = vote.val_index ∧ v₂.val_index = vote.val_index :=
  pool_vote_reaches_before_add_delay_upTo S Sched x hDiv hMono GST
    (synchronyFromWakeUpTo_of_synchronyFromWake (t + Δ S) hSync)
    (catchUpOnWakeUpTo_of_catchUpOnWake (t + Δ S) hCatch) t s a b vote hGST hhi hb hvote
    le_rfl

end Relays

end GoldilocksCorrectness.Proofs.Executions
