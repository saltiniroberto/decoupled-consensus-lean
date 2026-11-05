module
public import GoldilocksCorrectness.Proofs.Executions.ProposalPropagation
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Proofs.Executions.NetworkUpTo

@[expose] public section

/-!
# `ProposalPropagation.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/ProposalPropagation.lean` that name a
delivery premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the
deadlines. The bound of
each twin is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in
the twin's own parameters.

* `mem_T_before_of_send`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ)
open GoldilocksCorrectness.Proofs.Routines (slot_mono slot_mono_int)

open GoldilocksCorrectness.Proofs.Routines (block_admissible_of mem_T_receive_block)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicAction AtomicExec Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans compatible_iff)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- Block propagation from a given send: a block that a validator `u` put on the wire at the step
`i`, holds right after that step, and is honest at that step's end, is held before `t + Δ S` by
every validator `w` awake and honest at every time from `t` to `t + Δ S` whose finalized block
before `t + Δ S` is compatible with the block, when the block is on the wire at or before
`t` (`x[i + 1].time ≤ t`) and `GST ≤ t`.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `GST`: the time from which the
  network is synchronous;
- `i`: the step of the send; `t`: the time; `u`: the sender; `w`: the receiver; `B`: the block.

Read aloud: after `GST`, a block an honest validator sent and holds reaches, within a delay, every
validator awake and honest for that delay whose finalized block is compatible with it.

Roots name blocks until `tR`, at least `t + Δ S`: the proof compares the block `w` holds at the
delivery, a step at a time before `t + Δ S`, with `B`, which `u` holds right after the send.

Restated with the delivery premises up to `b`, at least `t + Δ S`: the send's delivery to `w` is due by then. -/
theorem mem_T_before_of_send_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption) (GST : ℕ) {b : ℕ}
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject b)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject b)
    {tR : ℕ} (hRoots : RootsNameBlocksUntil S Sched x tR)
    (hParent : ParentHeldAtDelivery S Sched x)
    (i t : ℕ) (u w : V) (B : Block V)
    -- `u` put `B` on the wire at the step `i`, holds `B` after it, and is honest at its end
    (hsent : (⟨u, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent)
    (hB : B ∈ (x[i + 1][u].st).S.T)
    (huh : u ∉ Sched.adv (x[i + 1].time : Int))
    (hit : x[i + 1].time ≤ t) (hGST : GST ≤ t)
    (hw : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ S →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    (hcompat : (stateBefore x (t + Δ S) w).S.F.compatible B = true)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : t + Δ S ≤ tR)
    -- the latest deadline the proof reads is at most the bound
    (hb : t + Δ S ≤ b) :
    B ∈ (stateBefore x (t + Δ S) w).S.T := by
  -- the genesis block is in every tree
  by_cases hg : B = Block.genesis
  · subst hg
    exact genesis_mem_T_of_exec S Sched x _ w
  -- an ancestor of `w`'s finalized block is in `w`'s tree
  rcases (compatible_iff _ _).1 hcompat with hFB | hBF
  swap
  · exact ancestors_mem_T_of_exec S Sched x _ w _ B
      (lem11_node_invariant S Sched x _ w).1.2.2.2.1 hBF
  -- the send is honest: `u` is honest at the step's start, corruption being permanent
  have hhon : u ∉ Sched.adv (x[i].time : Int) := fun h =>
    huh (hMono _ _ (by exact_mod_cast time_le_succ x i) h)
  -- the delivery to `w`, strictly before `stepBefore x (t + Δ S)`
  obtain ⟨d, hid, hl, hd⟩ := delivered_before_stepBefore_of_honest_send_upTo x hDiv
    (SynchronyFromWakeUpTo.mono hb hSync) (CatchUpOnWakeUpTo.mono hb hCatch) hMono (sm := ⟨u, NamedObject.block B⟩) ⟨hsent, hhon⟩ trivial hit hGST hw
  obtain ⟨-, hwh, hstep⟩ := deliver_step_state x hl
  suffices h : B ∈ (x[d + 1][w].st).S.T from mem_T_mono x w hd h
  by_cases hheld : B ∈ (x[d][w].st).S.T
  · exact mem_T_mono x w (Nat.le_succ d) hheld
  rw [hstep]
  apply mem_T_receive_block
  right
  -- what `u`'s tree satisfies right after the send
  have hInvU := (lem11_node_invariant S Sched x (i + 1) u).1
  obtain ⟨hparU, hwf, hprop, hps⟩ := hInvU.2.2.1.2 B hB hg
  -- `w`'s finalized block at the delivery
  have hFd : (x[d][w].st).S.F.AncestorEq B :=
    ancestorEq_trans (F_ancestorEq_of_le x w (le_of_lt hd)) hFB
  have hpar : B.parent ∈ (x[d][w].st).S.T :=
    hParent d w _ B hl rfl hg ((compatible_iff _ _).2 (Or.inl hFd))
  have hInvW := (lem11_node_invariant S Sched x d w).1
  refine block_admissible_of _ _ _ _ _ hwf ?_ ?_ hpar hFd hprop hps ?_
  · -- the slot test at the delivery: `u`'s clock after the step that put `B` in its tree
    rw [(slot_current_at_delivery hl).1]
    obtain ⟨i', hi', -, -, hslot⟩ := tree_block_relayed x (k := i + 1) hB hg
    calc B.slot ≤ S.C.slot ((x[i' + 1][u].st).t) := hslot
      _ ≤ S.C.slot ((x[i' + 1].time : ℕ) : Int) := slot_mono_int S (clock_le_time x (i' + 1) u)
      _ ≤ S.C.slot ((x[d].time : ℕ) : Int) := slot_mono S (time_mono x (by omega))
  · -- no block of `w`'s tree has `B`'s root: it would be `B` itself
    intro B' hB' hr
    have hdt : x[d].time < t + Δ S :=
      lt_of_le_of_lt (time_le_succ x d) ((lt_stepBefore_iff x hDiv).1 hd)
    have hBB : B' = B := hRoots B' B ⟨d, w, hwh, by omega, hB'⟩
      ⟨i + 1, u, huh, le_trans (time_mono x (show i + 1 ≤ d by omega)) (by omega), hB⟩ hr
    exact hheld (hBB ▸ hB')
  · -- the attestations, valid against the parent's chain state, computed alike at both
    intro a ha
    have h1 := hInvU.2.2.2.2.2.2.1 B hB hg a ha
    rw [hInvU.2.2.2.2.2.1 B.parent hparU] at h1
    rw [hInvW.2.2.2.2.2.1 B.parent hpar]
    exact h1

end GoldilocksCorrectness.Proofs.Executions

