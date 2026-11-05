module
public import GoldilocksCorrectness.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Proofs.Routines.ACStore

@[expose] public section

/-! section 6.1,
steps 2 and 4, of the delivery lemma. A Goldfish vote that an honest validator puts on the wire
at its tick at a time `t₁ ≥ GST`, with the vote's slot the slot of `t₁`, is delivered before
`t₁ + Δ` to every validator `w` awake and honest throughout `[t₁, t₁ + Δ]`; the delivery admits it
into `w`'s pool unless `w` already holds it, or already holds two distinct votes of its validator
for its slot (`on_goldfish_vote`'s four tests). And two votes of the same slot from a validator
honest at the time are the same vote, wherever they are held: every copy on the wire descends
from the voter's own tick (`VotesCastByOwner`), and a tick sends one Goldfish vote.

## What is proved

- per routine: `receive_gfVote_cases`, what `on_goldfish_vote` does with a vote of the right slot
  and committee; `two_votes_of_equivocates`;
- along an execution: `vote_in_pool_before_add_delay`, the delivery; `unique_vote_of_owner`, one
  vote per slot of an honest validator in any pool.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slot_mono slot_natCast)

open GoldilocksCorrectness.Proofs.Routines (fun_getElem)

open GoldilocksCorrectness.Proofs.Routines (receive_gfVote_cases two_votes_of_equivocates)

open GoldilocksCorrectness.Proofs.Routines (on_ac_message_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Goldilocks
open GoldilocksCorrectness.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The admission of a Goldfish vote -/

section Admission

end Admission

/-! ## Along an execution -/

section Delivery

open Framework.StsMultisetLog (AtomicAction AtomicExec Schedule SignedMsg)
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable [RootOrder] {S : Setup V} {Sched : Schedule V}

/-- Vote delivery: a Goldfish vote that its validator, honest at `t₁ ≥ GST`, puts on the wire at
its tick at `t₁`, with the vote's slot the slot of `t₁` and its validator in that slot's
committee, is in the pool of every validator `w` awake and honest at every time from `t₁` to
`t₁ + Δ S` before `t₁ + Δ S`, stamped strictly before `t₁ + Δ S`; or `w` holds then two distinct
votes of the vote's validator for the vote's slot.

The variables:
- `x`: the execution; `GST`: the time from which the network is synchronous;
- `i`: the step of the tick; `t₁`: its time; `w`: the receiver; `vote`: the vote. -/
theorem vote_in_pool_before_add_delay {x : AtomicExec (protocol S) Sched}
    (hdiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption) {GST : ℕ}
    -- blocks and Goldfish votes are delivered within `Δ S` after `GST`
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    {i t₁ : ℕ} {w : V} {vote : GoldfishVote V}
    -- the step `i` is the tick at `t₁`, and puts the vote on the wire, signed by its validator
    (hl : x.lbl i = AtomicAction.tickAllAwake t₁)
    (hsent : (⟨vote.val_index, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent)
    (hGST : GST ≤ t₁)
    -- the vote's slot is the slot of `t₁`, and its validator is in that slot's committee
    (hslot : vote.slot = S.C.slot (t₁ : Int))
    (hcomm : vote.val_index ∈ S.P.committee vote.slot)
    -- the vote's validator is honest at `t₁`
    (hu : vote.val_index ∉ Sched.adv (t₁ : Int))
    -- `w` is awake and honest at every time from `t₁` to `t₁ + Δ S`
    (hw : ∀ t' : ℕ, t₁ ≤ t' → t' ≤ t₁ + Δ S →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int)) :
    (vote ∈ (stateBefore x (t₁ + Δ S) w).A.pool vote.slot ∧
        ∃ τ : Stamp, (stateBefore x (t₁ + Δ S) w).A.timestamp_vote vote = some τ ∧
          τ < ((((t₁ + Δ S : ℕ) : Int)) : Stamp)) ∨
      ∃ v₁ ∈ (stateBefore x (t₁ + Δ S) w).A.pool vote.slot,
        ∃ v₂ ∈ (stateBefore x (t₁ + Δ S) w).A.pool vote.slot,
          v₁ ≠ v₂ ∧ v₁.val_index = vote.val_index ∧ v₂.val_index = vote.val_index := by
  obtain ⟨hT1, hT2⟩ := time_of_lbl_tickAllAwake x hl
  have hhon : vote.val_index ∉ Sched.adv (x[i].time : Int) := fun h =>
    hu (hMono _ _ (by omega) h)
  obtain ⟨d, hid, hld, hd⟩ := delivered_before_stepBefore_of_honest_send x hdiv hSync hCatch
    hMono ⟨hsent, hhon⟩ trivial (by omega) hGST hw
  obtain ⟨-, -, hstep⟩ := deliver_step_state x hld
  have hclock := (slot_current_at_delivery hld).1
  -- the delivery's time is from `t₁` on and strictly before `t₁ + Δ S`
  have hlo : t₁ ≤ x[d].time := hT2 ▸ time_mono x hid
  have hhi : x[d].time < t₁ + Δ S :=
    lt_of_le_of_lt (time_le_succ x d) ((lt_stepBefore_iff x hdiv).1 hd)
  -- so its slot is the vote's slot or the next
  have hq : 0 < 4 * Δ S := by have := one_le_Δ S; omega
  have hs2 : vote.slot ≤ S.C.slot (x[d][w].st).t := by
    rw [hclock, hslot]
    exact slot_mono S hlo
  have hs1 : S.C.slot (x[d][w].st).t ≤ vote.slot + 1 := by
    rw [hclock, hslot, slot_natCast, slot_natCast, ← Nat.add_div_right t₁ hq]
    exact Nat.div_le_div_right (by omega)
  have hA : (x[d + 1][w].st).A =
      on_goldfish_vote S.C S.P (x[d][w].st).A (x[d][w].st).t vote := by
    rw [hstep]
    show (on_ac_message _ _ _ vote).A = _
    rw [on_ac_message_eq]
  rcases receive_gfVote_cases S.C S.P (x[d][w].st).A (x[d][w].st).t vote hs1 hs2 hcomm with
    hin | heqv
  · left
    have hv : vote ∈ (stateBefore x (t₁ + Δ S) w).A.pool vote.slot :=
      pool_mono x w hd vote.slot (hA ▸ hin)
    exact ⟨hv, voteStamp_before hdiv hv⟩
  · right
    obtain ⟨v₁, h₁, v₂, h₂, hne, hi₁, hi₂⟩ := two_votes_of_equivocates heqv
    exact ⟨v₁, pool_mono x w (le_of_lt hd) _ h₁, v₂, pool_mono x w (le_of_lt hd) _ h₂, hne, hi₁,
      hi₂⟩

/-- A vote of a validator `u` that a validator's pool holds before `t`, with `u` honest at `t`,
was put on the wire by `u`'s own tick at some step.

The variables:
- `x`: the execution; `t`: the time; `w`: the validator whose pool it is; `u`: the voter;
  `s`: the slot; `vote`: the vote. -/
theorem pool_vote_tick_send {x : AtomicExec (protocol S) Sched}
    (hdiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- nobody votes in an honest validator's name
    (hOwner : VotesCastByOwner S Sched x)
    {t : ℕ} {w u : V} {s : Slot} {vote : GoldfishVote V}
    -- `u` is honest at `t`
    (hu : u ∉ Sched.adv (t : Int))
    -- `w`'s pool of slot `s` before `t` holds `vote`, a vote of `u`
    (hv : vote ∈ (stateBefore x t w).A.pool s) (hi : vote.val_index = u) :
    ∃ k t' : ℕ, x.lbl k = AtomicAction.tickAllAwake t' ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[k + 1].sent - x[k].sent := by
  obtain ⟨i, hi', sm, hsm, hcarry⟩ := pool_vote_sent_before hv
  have hit : x[i].time ≤ t :=
    le_of_lt (lt_of_le_of_lt (time_le_succ x i) ((lt_stepBefore_iff x hdiv).1 hi'))
  have hhon : vote.val_index ∉ Sched.adv (x[i].time : Int) := fun h =>
    hu (hMono _ _ (by exact_mod_cast hit) (hi ▸ h))
  obtain ⟨k, t', -, hlk, hsk⟩ := hOwner i sm vote hsm hcarry hhon
  exact ⟨k, t', hlk, hi ▸ hsk⟩

/-- One vote per slot of an honest validator: two votes of the validator `u`, honest at `t`, that
a validator's pool of slot `s` holds before `t` are the same vote.

The variables:
- `x`: the execution; `t`: the time; `w`: the validator whose pool it is; `u`: the voter;
  `s`: the slot; `v₁`, `v₂`: the two votes. -/
theorem unique_vote_of_owner {x : AtomicExec (protocol S) Sched}
    (hdiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- nobody votes in an honest validator's name
    (hOwner : VotesCastByOwner S Sched x)
    {t : ℕ} {w u : V} {s : Slot} {v₁ v₂ : GoldfishVote V}
    -- `u` is honest at `t`
    (hu : u ∉ Sched.adv (t : Int))
    -- `w`'s pool of slot `s` before `t` holds `v₁` and `v₂`, both votes of `u`
    (h₁ : v₁ ∈ (stateBefore x t w).A.pool s) (h₂ : v₂ ∈ (stateBefore x t w).A.pool s)
    (hi₁ : v₁.val_index = u) (hi₂ : v₂.val_index = u) :
    v₁ = v₂ := by
  obtain ⟨k₁, t₁, hl₁, hs₁⟩ := pool_vote_tick_send hdiv hMono hOwner hu h₁ hi₁
  obtain ⟨k₂, t₂, hl₂, hs₂⟩ := pool_vote_tick_send hdiv hMono hOwner hu h₂ hi₂
  refine honest_vote_sent_once hl₁ hl₂ hs₁ hs₂ ?_
  rw [pool_slot_of_stateBefore S Sched x t w s v₁ h₁, pool_slot_of_stateBefore S Sched x t w s v₂ h₂]

end Delivery

end GoldilocksCorrectness.Proofs.Executions
