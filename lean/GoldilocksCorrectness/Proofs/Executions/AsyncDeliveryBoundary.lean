module
public import GoldilocksCorrectness.Proofs.Executions.Lemma12
public import GoldilocksCorrectness.Proofs.Executions.Relay

@[expose] public section

/-! The audited statement is in
`Statements/Executions/AsyncDeliveryBoundaryStatements.lean`.

Lemma 12 (`lem12_honest_vote_delivered_until`) delivers the slot-`s` honest votes on the window
`[voteTime S s, supportCutoff S s]`. Here the window is `[t, t + Δ S]` for any `t` from the vote time
on, with `GST ≤ t` and `t + Δ S` at most the view freeze of `s`. The proof is Lemma 12's with
`voteTime S s` replaced by `t` at the two delivery calls:

- `vote_in_pool_before_add_delay_at`, the copy of `vote_in_pool_before_add_delay` at a later time:
  the delivery is before `t + Δ S`, so in slot `s` itself, and `on_goldfish_vote` admits the vote;
- `mem_T_before_add_delay` at `t`, with the block held by its voter before `t` (it was held before
  the vote time);
- the stamps by `voteStamp_lt_iff`, `blockStamp_lt_iff` at `t + Δ S`, and the uniqueness by
  `unique_vote_of_owner`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime viewFreeze)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem slot_mono
  viewFreeze_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree)

open GoldilocksCorrectness.Proofs.Routines (receive_gfVote_cases two_votes_of_equivocates)

open GoldilocksCorrectness.Proofs.Routines (on_ac_message_eq tau_eq_ok_some)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction AtomicHonest Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  blockWithRoot_eq_ok find?_eq_some dre_bind_ok liftM_some occurrenceBefore_eq_true_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

section Delivery

variable {S : Setup V} {Sched : Schedule V}

/-- Vote delivery at a later time: a Goldfish vote that its validator, honest at `t₁`, puts on the
wire at its tick at `t₁`, with the vote's slot the slot of `t₁` and its validator in that slot's
committee, is in the pool of every validator `w` awake and honest at every time from `t` to
`t + Δ S` before `t + Δ S`, stamped strictly before `t + Δ S`, for any `t ≥ t₁` with `GST ≤ t` and
`t + Δ S` at most the view freeze of the vote's slot; or `w` holds then two distinct votes of the
vote's validator for the vote's slot. The copy of `vote_in_pool_before_add_delay` with the window
`[t, t + Δ S]` in place of `[t₁, t₁ + Δ S]`.

The variables:
- `x`: the execution; `GST`: the time from which the network is synchronous;
- `i`: the step of the tick; `t₁`: its time; `t`: the start of the window; `w`: the receiver;
  `vote`: the vote. -/
theorem vote_in_pool_before_add_delay_at {x : AtomicExec (protocol S) Sched}
    (hdiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption) {GST : ℕ}
    -- blocks and Goldfish votes are delivered within `Δ S` after `GST`
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    {i t₁ t : ℕ} {w : V} {vote : GoldfishVote V}
    -- the step `i` is the tick at `t₁`, and puts the vote on the wire, signed by its validator
    (hl : x.lbl i = AtomicAction.tickAllAwake t₁)
    (hsent : (⟨vote.val_index, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent)
    -- the window starts at or after the tick, and at or after `GST`
    (ht₁ : t₁ ≤ t) (hGST : GST ≤ t)
    -- the vote's slot is the slot of `t₁`, and its validator is in that slot's committee
    (hslot : vote.slot = S.C.slot (t₁ : Int))
    (hcomm : vote.val_index ∈ S.P.committee vote.slot)
    -- the window ends at or before the view freeze of the vote's slot
    (hfz : t + Δ S ≤ viewFreeze S vote.slot)
    -- the vote's validator is honest at `t₁`
    (hu : vote.val_index ∉ Sched.adv (t₁ : Int))
    -- `w` is awake and honest at every time from `t` to `t + Δ S`
    (hw : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ S →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int)) :
    (vote ∈ (stateBefore x (t + Δ S) w).A.pool vote.slot ∧
        ∃ τ : Stamp, (stateBefore x (t + Δ S) w).A.timestamp_vote vote = some τ ∧
          τ < ((((t + Δ S : ℕ) : Int)) : Stamp)) ∨
      ∃ v₁ ∈ (stateBefore x (t + Δ S) w).A.pool vote.slot,
        ∃ v₂ ∈ (stateBefore x (t + Δ S) w).A.pool vote.slot,
          v₁ ≠ v₂ ∧ v₁.val_index = vote.val_index ∧ v₂.val_index = vote.val_index := by
  obtain ⟨hT1, hT2⟩ := time_of_lbl_tickAllAwake x hl
  have hhon : vote.val_index ∉ Sched.adv (x[i].time : Int) := fun h =>
    hu (hMono _ _ (by omega) h)
  obtain ⟨d, hid, hld, hd⟩ := delivered_before_stepBefore_of_honest_send x hdiv hSync hCatch
    hMono ⟨hsent, hhon⟩ trivial (by omega) hGST hw
  obtain ⟨-, -, hstep⟩ := deliver_step_state x hld
  have hclock := (slot_current_at_delivery hld).1
  -- the delivery's time is from `t₁` on and strictly before `t + Δ S`
  have hlo : t₁ ≤ x[d].time := hT2 ▸ time_mono x hid
  have hhi : x[d].time < t + Δ S :=
    lt_of_le_of_lt (time_le_succ x d) ((lt_stepBefore_iff x hdiv).1 hd)
  -- so its slot is the vote's slot
  have hs2 : vote.slot ≤ S.C.slot (x[d][w].st).t := by
    rw [hclock, hslot]
    exact slot_mono S hlo
  have hs1 : S.C.slot (x[d][w].st).t ≤ vote.slot + 1 := by
    have hΔ := one_le_Δ S
    have hf := viewFreeze_eq S vote.slot
    have hss : slotStart S (vote.slot + 1) = slotStart S vote.slot + 4 * Δ S := by
      rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
    have h1 : S.C.slot ((x[d].time : ℕ) : Int) ≤ S.C.slot ((viewFreeze S vote.slot : ℕ) : Int) :=
      slot_mono S (by omega)
    have h2 : S.C.slot ((viewFreeze S vote.slot : ℕ) : Int) = vote.slot :=
      slot_eq_of_mem S (by omega) (by omega)
    rw [hclock]
    exact le_trans (h2 ▸ h1) (Nat.le_succ _)
  have hA : (x[d + 1][w].st).A =
      on_goldfish_vote S.C S.P (x[d][w].st).A (x[d][w].st).t vote := by
    rw [hstep]
    show (on_ac_message _ _ _ vote).A = _
    rw [on_ac_message_eq]
  rcases receive_gfVote_cases S.C S.P (x[d][w].st).A (x[d][w].st).t vote hs1 hs2 hcomm with
    hin | heqv
  · left
    have hv : vote ∈ (stateBefore x (t + Δ S) w).A.pool vote.slot :=
      pool_mono x w hd vote.slot (hA ▸ hin)
    exact ⟨hv, voteStamp_before hdiv hv⟩
  · right
    obtain ⟨v₁, h₁, v₂, h₂, hne, hi₁, hi₂⟩ := two_votes_of_equivocates heqv
    exact ⟨v₁, pool_mono x w (le_of_lt hd) _ h₁, v₂, pool_mono x w (le_of_lt hd) _ h₂, hne, hi₁,
      hi₂⟩

end Delivery

/-- **Lemma 12 by a later delay.** The proof; the audited statement is in
`Statements/Executions/AsyncDeliveryBoundaryStatements.lean`.

Roots name blocks until `t + Δ S`: `mem_T_before_add_delay` at `t`. -/
theorem lem12_honest_vote_delivered_by_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s t t₃ : ℕ) (Hs : Finset V) (H : V → Block V) (w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (t + Δ S))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ t) (htv : voteTime S s ≤ t) (htf : t + Δ S ≤ viewFreeze S s) (ht₃ : t + Δ S ≤ t₃)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (t₃ : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T)
    (hw : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ S → w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    (hF : ∀ u ∈ Hs, (stateBefore x t₃ w).S.F.AncestorEq (H u)) :
    ∀ u ∈ Hs, HeldEarlyVoteAt (stateBefore x t₃ w).A (fg_to_ac (stateBefore x t₃ w).S)
      (((t + Δ S : ℕ) : Int)) s (H u) u := by
  intro u hu
  obtain ⟨hcomm, hhon, ⟨i, hl, hsent⟩, hHT⟩ := hHs u hu
  -- the times
  have hΔ := one_le_Δ S
  have hv₁ : voteTime S s = slotStart S s + Δ S := voteTime_eq S s
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have ht₁ : 1 ≤ t := by omega
  have hslot : S.C.slot (voteTime S s : Int) = s := slot_eq_of_mem S (by omega) (by omega)
  -- honesty along the way
  have hu₁ : u ∉ Sched.adv (voteTime S s : Int) := fun h =>
    hhon (hMono _ _ (by exact_mod_cast (by omega : voteTime S s ≤ t₃)) h)
  have hut : u ∉ Sched.adv (t : Int) := fun h =>
    hhon (hMono _ _ (by exact_mod_cast (by omega : t ≤ t₃)) h)
  have hu₂ : u ∉ Sched.adv ((t + Δ S : ℕ) : Int) := fun h =>
    hhon (hMono _ _ (by exact_mod_cast ht₃) h)
  -- the vote is in `w`'s pool before `t + Δ S`
  have hvote : GoldfishVote.mk u s (H u).root ∈
      (stateBefore x (t + Δ S) w).A.pool s := by
    rcases vote_in_pool_before_add_delay_at (vote := GoldfishVote.mk u s (H u).root) hDiv hMono
        hSync hCatch hl hsent htv hGST hslot.symm hcomm htf hu₁ hw with
      ⟨h, -⟩ | ⟨v₁, h₁, v₂, h₂, hne, hi₁, hi₂⟩
    · exact h
    · exact absurd (unique_vote_of_owner hDiv hMono hOwner hu₂ h₁ h₂ hi₁ hi₂) hne
  -- `H u` is in `w`'s tree before `t + Δ S`
  have hHTt : H u ∈ (stateBefore x t u).S.T := mem_T_mono x u (stepBefore_mono x hDiv htv) hHT
  have hcompat : (stateBefore x (t + Δ S) w).S.F.compatible (H u) = true :=
    (compatible_iff _ _).2 (Or.inl (ancestorEq_trans
      (stateBefore_grows x hDiv w ht₃).2.1 (hF u hu)))
  have hblock : H u ∈ (stateBefore x (t + Δ S) w).S.T :=
    mem_T_before_add_delay hDiv hMono hSync hCatch hRoots hParent ht₁ hGST hut hHTt hw hcompat
  -- from `t + Δ S` to `t₃`
  have hstep := stepBefore_mono x hDiv ht₃
  have hvote₃ : GoldfishVote.mk u s (H u).root ∈
      (stateBefore x t₃ w).A.pool s := pool_mono x w hstep s hvote
  have hblock₃ : H u ∈ (stateBefore x t₃ w).S.T := mem_T_mono x w hstep hblock
  -- the two stamps
  obtain ⟨τv, hτv, hτvlt⟩ := (voteStamp_lt_iff hDiv hvote₃).2 hvote
  obtain ⟨τH, hτH, hτHlt⟩ := (blockStamp_lt_iff hDiv hblock₃).2 hblock
  -- the frame's tree, and its roots
  have hHΦ : H u ∈ (fg_to_ac (stateBefore x t₃ w).S).tree :=
    (mem_fg_to_ac_tree _ _).2 ⟨hblock₃, hF u hu⟩
  have hR : GoldilocksCorrectness.Statements.Routines.RootsNameBlocksIn
      (fg_to_ac (stateBefore x t₃ w).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ w
  have hHslot : (H u).slot ≤ s := hslot ▸ slot_le_of_mem_T_before hDiv hMono hHT
  -- the resolution
  have htau : (stateBefore x t₃ w).A.tau
      (fg_to_ac (stateBefore x t₃ w).S) (GoldfishVote.mk u s (H u).root) =
        .ok (some (max τv τH)) :=
    tau_eq_ok_some hR hHΦ rfl hHslot hτv hτH
  refine ⟨hvote₃, ⟨τv, hτv, hτvlt⟩, hHΦ, ⟨max τv τH, htau, ?_⟩, ?_⟩
  · exact (occurrenceBefore_eq_true_iff _ _).2 ⟨_, rfl, max_lt hτvlt hτHlt⟩
  · intro vote' hv' hi'
    exact unique_vote_of_owner hDiv hMono hOwner hhon hv' hvote₃ hi' rfl

end GoldilocksCorrectness.Proofs.Executions
