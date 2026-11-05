module
public import GoldilocksCorrectness.Proofs.Executions.Provenance
public import GoldilocksCorrectness.Proofs.Executions.Network
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.RootsStatements
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.Wiring

@[expose] public section

/-! section 6.1, step 3,
of the delivery lemma. A block other than the genesis block that an honest validator `u` holds
before a time `t ≥ GST` was put on the wire by `u` itself at an earlier step
(`tree_block_relayed_before`); the network delivers it to every validator `w` awake and honest
throughout `[t, t + Δ]` before `t + Δ` (`delivered_before_stepBefore_of_honest_send`); and at that
delivery `w` either holds the block already, or `block_admissible` answers true, each of its eight
tests passing from what `u`'s tree satisfies (`lem11_node_invariant`), from the network
assumptions, and from `w`'s finalized block being compatible with the block.

## The times

- `Δ_cast`, `one_le_Δ`, `slotStart_cast`, `voteTime_cast`, `supportCutoff_cast`: the spec's times
  read back as natural numbers;
- `slotStart_eq`, `voteTime_eq`, `supportCutoff_eq`, `voteTime_succ`: the times as equations at
  `ℕ`;
- `slot_natCast`, `slot_mono`, `slot_mono_int`, `slot_eq_of_mem`: the slot of a time.

## What is proved

- per routine: `block_admissible_of`, the converse of `block_admissible_facts`;
  `mem_T_receive_block`;
- per step: `deliver_step_state`, what a delivery leaves at its receiver;
- along an execution: `slot_le_of_mem_T_before`, a held block's slot is at most the slot of the
  time; `mem_T_before_add_delay_upTo`, the propagation, on the delivery and roots premises up to
  `t + Δ S`; `mem_T_before_add_delay`, its instance on the two delivery premises.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ)
open GoldilocksCorrectness.Proofs.Routines (slot_mono slot_mono_int)

open GoldilocksCorrectness.Proofs.Routines (fun_getElem)

open GoldilocksCorrectness.Proofs.Routines (fg_on_block_eq)

open GoldilocksCorrectness.Proofs.Routines (block_admissible_of mem_T_receive_block)

namespace GoldilocksCorrectness.Proofs.Executions

open Goldilocks
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans compatible_iff)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The times -/

section Times

open Goldilocks.Sts (Setup)

end Times

/-! ## The test of a block, and its receipt -/

section Admission

variable [RootOrder]

end Admission

/-! ## A delivery step -/

section Steps

open Framework.StsMultisetLog (AtomicAction AtomicExec Schedule SignedMsg
  applyNodeStepResult_getElem receive_getElem nodeStep_iff_exists)
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol step_recv_iff)

variable [RootOrder] {S : Setup V} {Sched : Schedule V}

/-- A step that delivers the signed message `sm` to `v` finds `v` awake and outside the adversary
set at its time, and leaves `v` with the node state `receive` gives on `sm`'s object.

The variables:
- `x`: the execution; `d`: the step; `v`: the receiver; `sm`: the signed message. -/
theorem deliver_step_state (x : AtomicExec (protocol S) Sched) {d : ℕ} {v : V}
    {sm : SignedMsg V (NamedObject V)}
    -- the step `d` delivers `sm` to `v`
    (hl : x.lbl d = AtomicAction.deliver v sm) :
    v ∈ Sched.awake (x[d].time : Int) ∧ v ∉ Sched.adv (x[d].time : Int) ∧
      x[d + 1][v].st = Goldilocks.Sts.receive S.C S.P S.X x[d][v].st sm.msg := by
  have hs := x.step d
  rw [hl] at hs
  obtain ⟨he, hr⟩ := hs
  obtain ⟨res, hp, hc⟩ := (nodeStep_iff_exists _ v (.recv sm) _ _).1 hr
  refine ⟨he.2.1, he.2.2, ?_⟩
  show (x.cfg (d + 1))[v].st = _
  rw [hc, applyNodeStepResult_getElem, if_pos rfl]
  rw [(step_recv_iff S _ _ _ _ _ _).1 hp]
  show Goldilocks.Sts.receive S.C S.P S.X
    (Framework.StsMultisetLog.receive v sm (x.cfg d))[v].st sm.msg = _
  rw [receive_getElem, if_pos rfl]
  rfl

end Steps

/-! ## Along an execution -/

section Propagation

open Framework.StsMultisetLog (AtomicAction AtomicExec Schedule SignedMsg)
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable [RootOrder] {S : Setup V} {Sched : Schedule V}

/-- A block a validator holds before the time `t` has a slot at most the slot of `t`.

The variables:
- `x`: the execution; `t`: the time; `v`: the validator; `B`: the block. -/
theorem slot_le_of_mem_T_before {x : AtomicExec (protocol S) Sched}
    (hdiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption) {t : ℕ} {v : V} {B : Block V}
    -- `v`'s tree before `t` holds `B`
    (hB : B ∈ (stateBefore x t v).S.T) :
    B.slot ≤ S.C.slot (t : Int) := by
  by_cases hg : B = Block.genesis
  · subst hg
    exact Nat.zero_le _
  obtain ⟨i, hi, -, -, hslot⟩ := tree_block_relayed_before hMono hB hg
  have hlt : x[i + 1].time < t := (lt_stepBefore_iff x hdiv).1 hi
  calc B.slot ≤ S.C.slot ((x[i + 1][v].st).t) := hslot
    _ ≤ S.C.slot ((x[i + 1].time : ℕ) : Int) := slot_mono_int S (clock_le_time x (i + 1) v)
    _ ≤ S.C.slot (t : Int) := slot_mono S (le_of_lt hlt)

/-- Block propagation: a block that a validator `u`, honest at `t ≥ GST`, holds before `t` is
held before `t + Δ S` by every validator `w` awake and honest at every time from `t` to
`t + Δ S` whose finalized block before `t + Δ S` is compatible with the block.

The variables:
- `x`: the execution; `GST`: the time from which the network is synchronous; `t`: the time;
- `u`: the validator that holds the block; `w`: the validator it reaches; `B`: the block.

Restated with the delivery and roots premises up to `t + Δ S`, the latest deadline being
`t + Δ S` (`u`'s send of `B` reaching `w`); `mem_T_before_add_delay` is its instance. Roots name
blocks until `t + Δ S`: the proof compares the block `w` holds at the delivery, a step at a time
before `t + Δ S`, with `B`, which `u` holds before `t`. -/
theorem mem_T_before_add_delay_upTo {x : AtomicExec (protocol S) Sched}
    (hdiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption) {GST : ℕ} {t : ℕ}
    -- blocks and Goldfish votes put on the wire early enough to be due by `t + Δ S` are
    -- delivered within `Δ S` after `GST`
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (t + Δ S))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (t + Δ S))
    -- a root names one block among what honest validators hold by `t + Δ S`
    (hRoots : RootsNameBlocksUntil S Sched x (t + Δ S))
    -- a block reaches a validator only once the validator holds its parent
    (hParent : ParentHeldAtDelivery S Sched x)
    {u w : V} {B : Block V}
    -- `t` is a time of a tick, from `GST` on
    (ht : 1 ≤ t) (hGST : GST ≤ t)
    -- `u` is honest at `t`, and holds `B` before `t`
    (hu : u ∉ Sched.adv (t : Int))
    (hB : B ∈ (stateBefore x t u).S.T)
    -- `w` is awake and honest at every time from `t` to `t + Δ S`
    (hw : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ S →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    -- `w`'s finalized block before `t + Δ S` is compatible with `B`
    (hcompat : (stateBefore x (t + Δ S) w).S.F.compatible B = true) :
    B ∈ (stateBefore x (t + Δ S) w).S.T := by
  by_cases hg : B = Block.genesis
  · subst hg
    exact genesis_mem_T_of_exec S Sched x _ w
  rcases (compatible_iff _ _).1 hcompat with hFB | hBF
  swap
  · exact ancestors_mem_T_of_exec S Sched x _ w _ B
      (lem11_node_invariant S Sched x _ w).1.2.2.2.1 hBF
  -- `u`'s own send of `B`, and its delivery to `w`
  obtain ⟨i, hi, hsend, hhon, hslot⟩ := tree_block_relayed_before hMono hB hg
  have hit : x[i + 1].time ≤ t :=
    le_of_lt ((lt_stepBefore_iff x hdiv).1 hi)
  obtain ⟨d, hid, hl, hdt⟩ := delivered_before_of_honest_send_upTo x hSync hCatch
    hMono (sm := ⟨u, NamedObject.block B⟩) ⟨hsend, hhon hu⟩ trivial hit hGST hw
  have hd : d < stepBefore x (t + Δ S) := deliver_before_of_time x hdiv hl hdt
  obtain ⟨-, hwh, hstep⟩ := deliver_step_state x hl
  suffices h : B ∈ (x[d + 1][w].st).S.T from mem_T_mono x w hd h
  by_cases hheld : B ∈ (x[d][w].st).S.T
  · exact mem_T_mono x w (Nat.le_succ d) hheld
  rw [hstep]
  apply mem_T_receive_block
  right
  -- what `u`'s tree satisfies
  have hInvU := (lem11_node_invariant S Sched x (stepBefore x t) u).1
  obtain ⟨hparU, hwf, hprop, hps⟩ := hInvU.2.2.1.2 B hB hg
  have hTu : x[stepBefore x t].time + 1 = t := (stepBefore_spec x hdiv ht).2.1
  have huh : u ∉ Sched.adv (x[stepBefore x t].time : Int) := fun h =>
    hu (hMono _ _ (by omega) h)
  -- `w`'s finalized block at the delivery
  have hFd : (x[d][w].st).S.F.AncestorEq B :=
    ancestorEq_trans (F_ancestorEq_of_le x w (le_of_lt hd)) hFB
  have hpar : B.parent ∈ (x[d][w].st).S.T :=
    hParent d w _ B hl rfl hg ((compatible_iff _ _).2 (Or.inl hFd))
  have hInvW := (lem11_node_invariant S Sched x d w).1
  refine block_admissible_of _ _ _ _ _ hwf ?_ ?_ hpar hFd hprop hps ?_
  · rw [(slot_current_at_delivery hl).1]
    calc B.slot ≤ S.C.slot ((x[i + 1][u].st).t) := hslot
      _ ≤ S.C.slot ((x[i + 1].time : ℕ) : Int) := slot_mono_int S (clock_le_time x (i + 1) u)
      _ ≤ S.C.slot ((x[d].time : ℕ) : Int) := slot_mono S (time_mono x hid)
  · intro B' hB' hr
    have hBB : B' = B := hRoots B' B ⟨d, w, hwh, le_of_lt hdt, hB'⟩
      ⟨stepBefore x t, u, huh, by omega, hB⟩ hr
    exact hheld (hBB ▸ hB')
  · intro a ha
    have h1 := hInvU.2.2.2.2.2.2.1 B hB hg a ha
    rw [hInvU.2.2.2.2.2.1 B.parent hparU] at h1
    rw [hInvW.2.2.2.2.2.1 B.parent hpar]
    exact h1

/-- Block propagation: a block that a validator `u`, honest at `t ≥ GST`, holds before `t` is
held before `t + Δ S` by every validator `w` awake and honest at every time from `t` to
`t + Δ S` whose finalized block before `t + Δ S` is compatible with the block.

The variables:
- `x`: the execution; `GST`: the time from which the network is synchronous; `t`: the time;
- `u`: the validator that holds the block; `w`: the validator it reaches; `B`: the block.

Roots name blocks until `t + Δ S`: the proof compares the block `w` holds at the delivery, a step
at a time before `t + Δ S`, with `B`, which `u` holds before `t`. -/
theorem mem_T_before_add_delay {x : AtomicExec (protocol S) Sched}
    (hdiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption) {GST : ℕ} {t : ℕ}
    -- blocks and Goldfish votes are delivered within `Δ S` after `GST`
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    -- a root names one block among what honest validators hold by `t + Δ S`
    (hRoots : RootsNameBlocksUntil S Sched x (t + Δ S))
    -- a block reaches a validator only once the validator holds its parent
    (hParent : ParentHeldAtDelivery S Sched x)
    {u w : V} {B : Block V}
    -- `t` is a time of a tick, from `GST` on
    (ht : 1 ≤ t) (hGST : GST ≤ t)
    -- `u` is honest at `t`, and holds `B` before `t`
    (hu : u ∉ Sched.adv (t : Int))
    (hB : B ∈ (stateBefore x t u).S.T)
    -- `w` is awake and honest at every time from `t` to `t + Δ S`
    (hw : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ S →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    -- `w`'s finalized block before `t + Δ S` is compatible with `B`
    (hcompat : (stateBefore x (t + Δ S) w).S.F.compatible B = true) :
    B ∈ (stateBefore x (t + Δ S) w).S.T :=
  mem_T_before_add_delay_upTo hdiv hMono (synchronyFromWakeUpTo_of_synchronyFromWake _ hSync)
    (catchUpOnWakeUpTo_of_catchUpOnWake _ hCatch) hRoots hParent ht hGST hu hB hw hcompat

end Propagation

end GoldilocksCorrectness.Proofs.Executions
