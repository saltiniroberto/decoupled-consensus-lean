module
public import GoldilocksCorrectness.Proofs.Executions.VoteDelivery
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Proofs.Executions.NetworkUpTo

@[expose] public section

/-!
# `VoteDelivery.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/VoteDelivery.lean` that name a delivery
premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the deadlines
. The bound of each twin
is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in the twin's
own parameters.

* `vote_in_pool_before_add_delay`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slot_mono slot_natCast)

open GoldilocksCorrectness.Proofs.Routines (receive_gfVote_cases two_votes_of_equivocates)

open GoldilocksCorrectness.Proofs.Routines (on_ac_message_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Goldilocks
open GoldilocksCorrectness.Statements.Executions
variable {V : Type} [DecidableEq V] [Fintype V]

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
- `i`: the step of the tick; `t₁`: its time; `w`: the receiver; `vote`: the vote.

Restated with the delivery premises up to `t₁ + Δ S`: the vote's delivery to `w` is due by then. -/
theorem vote_in_pool_before_add_delay_upTo {x : AtomicExec (protocol S) Sched}
    (hdiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption) {GST : ℕ} {t₁ : ℕ}
    -- blocks and Goldfish votes due by `t₁ + Δ S` are delivered within `Δ S` after `GST`
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (t₁ + Δ S))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (t₁ + Δ S))
    {i : ℕ} {w : V} {vote : GoldfishVote V}
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
  obtain ⟨d, hid, hld, hd⟩ := delivered_before_stepBefore_of_honest_send_upTo x hdiv hSync hCatch
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

end Delivery

end GoldilocksCorrectness.Proofs.Executions

