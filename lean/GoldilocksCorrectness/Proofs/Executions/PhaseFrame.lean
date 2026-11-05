module
public import GoldilocksCorrectness.Statements.Executions.HealedAttestationDefs
public import GoldilocksCorrectness.Statements.Executions.HonestAccountableStatements
public import GoldilocksCorrectness.Statements.Routines.AccountableStatements
public import GoldilocksCorrectness.Statements.Routines.CertificateStatements
public import GoldilocksCorrectness.Statements.Executions.AccountableStatements
public import GoldilocksCorrectness.Statements.Routines.AttestationStatements
public import GoldilocksCorrectness.Statements.Executions.ProposalViabilityStatements
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Proofs.Executions.HonestAccountable
public import GoldilocksCorrectness.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Proofs.Executions.TickSends
public import GoldilocksCorrectness.Proofs.Executions.Clock
public import GoldilocksCorrectness.Proofs.Routines.Record
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders

@[expose] public section

/-!
# The frame facts of the phase

The proofs of the statements of `Statements/Executions/PhaseFrameStatements.lean`:

- `lem68_honest_past_finalized`: the block finalized by the chain state of a block an honest
  validator holds is an ancestor of every block another honest validator holds at a greater
  chain-state height (Lemma 68, with the slashable set and the shared root refuted);
- `lem89b_at`: an honest validator's `h_max` before `t` is at least the height of every honest
  attestation sent at least one delay earlier, when `GST + Δ ≤ t`, fewer than a third of the
  validators have been in the adversary set up to `t`, and the validator is awake and honest from
  `t − Δ` to `t`; on the delivery and roots premises up to a bound `b ≥ t`;
- `lem89b_h_max_ge_attested`: in the phase, an honest validator's `h_max` is at least the height of
  every honest attestation sent at least one delay earlier (the instance of `lem89b_at`);
- `lem89h_threshold`: every honest attestation sent before the action time of the round opening
  at slot `s₀` has height at most the proposal's chain-state height plus one;
- `attested_height_bound`: when every honest attestation of a tick at a time at most the time of
  step `i` has height at most `A`, every block a validator holds after `i` steps has chain-state
  height at most `A + 1`.

## The kit

- `adversaryFewerThanThirdUntil_of_le`: the count of the adversary set up to a time bounds it up to
  every earlier time;
- `mem_T_before_add_delay_of_held`: block propagation from a holder honest at an earlier time,
  and `mem_T_before_add_delay_of_held_upTo`, the same on the delivery and roots premises up to the
  delivery's deadline;
- `tick_attestation_source`: the height of an attestation a tick sends is the chain-state height
  of a block of the sender's tree.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ slotStart supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_mono slot_mono_int
  supportCutoff_eq voteTime_eq Δ_cast)

open GoldilocksCorrectness.Proofs.Routines (lem47_chain_state_heights)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (h_max_le_floor_add_one mem_fg_to_ac_tree)

open GoldilocksCorrectness.Proofs.Routines (block_admissible_of mem_T_receive_block)

open GoldilocksCorrectness.Proofs.Routines (t_eq_mul)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicAction AtomicExec Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (lem68_past_finalized lem49_tick_attests
  lem67_first_advance)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans compatible_iff ac_to_fg_source_mem
  create_attestation_cases)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder] {S : Setup V} {Sched : Schedule V}

/-! ## The kit -/

omit [DecidableEq V] [RootOrder] in
/-- When fewer than a third of the validators have been in the adversary set up to `t'`, the same
holds up to every `t ≤ t'`.

The variables:
- `Sched`: the schedule; `t ≤ t'`: the two times. -/
theorem adversaryFewerThanThirdUntil_of_le {t t' : Int} (htt : t ≤ t')
    (h : AdversaryFewerThanThirdUntil Sched (validator_count V) t') : AdversaryFewerThanThirdUntil Sched (validator_count V) t :=
  fun A hA => h A (fun v hv =>
    let ⟨t'', h1, h2⟩ := hA v hv
    ⟨t'', le_trans h1 htt, h2⟩)

/-- Block propagation from an earlier holder: a block that a validator `u`, honest at `t₁ ≥ 1`,
holds before `t₁` is held before `t + Δ S`, for `t₁ ≤ t` and `GST ≤ t`, by every validator `w`
awake and honest at every time from `t` to `t + Δ S` whose finalized block before `t + Δ S` is
compatible with the block.

Why: `u` put the block on the wire at a step before `t₁`, honest then; the network delivers it to
`w` before `t + Δ S`; and at that delivery `w` holds it already or admits it, each test passing
from what `u`'s tree before `t₁` satisfies.

The variables:
- `x`: the execution; `GST`: the time from which the network is synchronous; `t₁ ≤ t`: the two
  times; `u`: the holder; `w`: the receiver; `B`: the block.

Restated with the delivery and roots premises up to `t + Δ S`, the latest deadline being
`t + Δ S` (`u`'s send of `B` reaching `w`); `mem_T_before_add_delay_of_held` is its instance.
Roots name blocks until `t + Δ S`: the proof compares the block `w` holds at the delivery, a step
at a time before `t + Δ S`, with `B`, which `u` holds before `t₁ ≤ t`. -/
theorem mem_T_before_add_delay_of_held_upTo {x : AtomicExec (protocol S) Sched}
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
    {t₁ : ℕ} {u w : V} {B : Block V}
    -- `t₁` is a time of a tick, at most `t`, and `t` is from `GST` on
    (ht₁ : 1 ≤ t₁) (ht₁t : t₁ ≤ t) (hGST : GST ≤ t)
    -- `u` is honest at `t₁`, and holds `B` before `t₁`
    (hu : u ∉ Sched.adv (t₁ : Int))
    (hB : B ∈ (stateBefore x t₁ u).S.T)
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
    le_trans (le_of_lt ((lt_stepBefore_iff x hdiv).1 hi)) ht₁t
  obtain ⟨d, hid, hl, hdt'⟩ := delivered_before_of_honest_send_upTo x hSync hCatch
    hMono (sm := ⟨u, NamedObject.block B⟩) ⟨hsend, hhon hu⟩ trivial hit hGST hw
  have hd : d < stepBefore x (t + Δ S) := deliver_before_of_time x hdiv hl hdt'
  have hdt : x[d].time ≤ t + Δ S := le_of_lt hdt'
  obtain ⟨-, hwh, hstep⟩ := deliver_step_state x hl
  suffices h : B ∈ (x[d + 1][w].st).S.T from mem_T_mono x w hd h
  by_cases hheld : B ∈ (x[d][w].st).S.T
  · exact mem_T_mono x w (Nat.le_succ d) hheld
  rw [hstep]
  apply mem_T_receive_block
  right
  -- what `u`'s tree satisfies
  have hInvU := (lem11_node_invariant S Sched x (stepBefore x t₁) u).1
  obtain ⟨hparU, hwf, hprop, hps⟩ := hInvU.2.2.1.2 B hB hg
  have hTu : x[stepBefore x t₁].time + 1 = t₁ := (stepBefore_spec x hdiv ht₁).2.1
  have huh : u ∉ Sched.adv (x[stepBefore x t₁].time : Int) := fun h =>
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
    have hBB : B' = B := hRoots B' B ⟨d, w, hwh, hdt, hB'⟩
      ⟨stepBefore x t₁, u, huh, by omega, hB⟩ hr
    exact hheld (hBB ▸ hB')
  · intro a ha
    have h1 := hInvU.2.2.2.2.2.2.1 B hB hg a ha
    rw [hInvU.2.2.2.2.2.1 B.parent hparU] at h1
    rw [hInvW.2.2.2.2.2.1 B.parent hpar]
    exact h1

/-- Block propagation from an earlier holder: a block that a validator `u`, honest at `t₁ ≥ 1`,
holds before `t₁` is held before `t + Δ S`, for `t₁ ≤ t` and `GST ≤ t`, by every validator `w`
awake and honest at every time from `t` to `t + Δ S` whose finalized block before `t + Δ S` is
compatible with the block.

Why: `u` put the block on the wire at a step before `t₁`, honest then; the network delivers it to
`w` before `t + Δ S`; and at that delivery `w` holds it already or admits it, each test passing
from what `u`'s tree before `t₁` satisfies.

The variables:
- `x`: the execution; `GST`: the time from which the network is synchronous; `t₁ ≤ t`: the two
  times; `u`: the holder; `w`: the receiver; `B`: the block.

Roots name blocks until `t + Δ S`: the proof compares the block `w` holds at the delivery, a step
at a time before `t + Δ S`, with `B`, which `u` holds before `t₁ ≤ t`. -/
theorem mem_T_before_add_delay_of_held {x : AtomicExec (protocol S) Sched}
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
    {t₁ : ℕ} {u w : V} {B : Block V}
    -- `t₁` is a time of a tick, at most `t`, and `t` is from `GST` on
    (ht₁ : 1 ≤ t₁) (ht₁t : t₁ ≤ t) (hGST : GST ≤ t)
    -- `u` is honest at `t₁`, and holds `B` before `t₁`
    (hu : u ∉ Sched.adv (t₁ : Int))
    (hB : B ∈ (stateBefore x t₁ u).S.T)
    -- `w` is awake and honest at every time from `t` to `t + Δ S`
    (hw : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ S →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    -- `w`'s finalized block before `t + Δ S` is compatible with `B`
    (hcompat : (stateBefore x (t + Δ S) w).S.F.compatible B = true) :
    B ∈ (stateBefore x (t + Δ S) w).S.T :=
  mem_T_before_add_delay_of_held_upTo hdiv hMono
    (synchronyFromWakeUpTo_of_synchronyFromWake _ hSync)
    (catchUpOnWakeUpTo_of_catchUpOnWake _ hCatch) hRoots hParent ht₁ ht₁t hGST hu hB hw
    hcompat

/-- The attestation a tick sends has the chain-state height of a block of the sender's tree: when
the step `i` is the tick of every awake validator at `t` and puts `u`'s attestation `a` on the
wire, some block `D` of `u`'s tree after `i` steps has `(chainStateOf S.C D).h = a.h`.

Why: the validator client built `a` at the height of the chain state of the source `ac_to_fg`
answered (Lemma 49), a block of the frame's tree, whose chain state is its own (Lemma 11).

The variables:
- `x`: the execution; `i`: the step; `t`: the time of the tick; `u`: the sender; `a`: the
  attestation. -/
theorem tick_attestation_source (x : AtomicExec (protocol S) Sched) {i t : ℕ} {u : V}
    {a : Attestation V}
    -- the step `i` is the tick of every awake validator at `t`
    (hl : x.lbl i = AtomicAction.tickAllAwake t)
    -- the step `i` put `u`'s attestation `a` on the wire
    (hsent : (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent) :
    ∃ D ∈ (x[i][u].st).S.T, (chainStateOf S.C D).h = a.h := by
  obtain ⟨-, n', sent, hrun, ha⟩ := tick_send_of_honestSendAt hl hsent
  obtain ⟨-, fi, D, hfi, hsrc, hca, -⟩ := lem49_tick_attests S.C S.P S.X _ n' _ sent a hrun ha
  have hSeq := (tickInputState_frame x i t u).1
  have hDT : D ∈ (x[i][u].st).S.T := by
    rw [← hSeq]
    exact ((mem_fg_to_ac_tree _ _).1 (ac_to_fg_source_mem hfi hsrc)).1
  have hσ : (x[i][u].st).S.σ D = chainStateOf S.C D :=
    (lem11_node_invariant S Sched x i u).1.2.2.2.2.2.1 D hDT
  refine ⟨D, hDT, ?_⟩
  rcases create_attestation_cases _ _ _ _ _ _ _ with h0 | ⟨τ', fp', -, -, -, h1⟩
  · rw [h0] at hca
    cases hca
  · rw [h1] at hca
    injection hca with hca
    subst hca
    show _ = ((tickInputState x i t u).S.σ D).h
    rw [hSeq, hσ]

/-! ## Lemma 89a -/

/-- **Lemma 89a, Lemma 68's honest corollary.** The proof; the audited statement is in
`Statements/Executions/PhaseFrameStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `hRoots`: roots
  name blocks; `i`, `j`: the two steps; `p`, `w`: the two holders; `B`, `B'`: the two blocks.

Roots name blocks until `tR`, at least `max x[i].time x[j].time`: the proof compares an ancestor of
`B`, held after `i` steps, with an ancestor of `B'`, held after `j` steps. -/
theorem lem68_honest_past_finalized (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) {tR : ℕ}
    (hRoots : RootsNameBlocksUntil S Sched x tR) (i j : ℕ) (p w : V) (B B' : Block V)
    -- fewer than a third of the validators have been in the adversary set up to the later time
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (max (x[i].time : Int) (x[j].time : Int)))
    -- `p` is honest after `i` steps, and `w` after `j` steps
    (hp : p ∉ Sched.adv (x[i].time : Int)) (hw : w ∉ Sched.adv (x[j].time : Int))
    -- `p` holds `B` after `i` steps, and `w` holds `B'` after `j` steps
    (hB : B ∈ (x[i][p].st).S.T) (hB' : B' ∈ (x[j][w].st).S.T)
    -- the chain-state height of `B'` is greater than the finalization height of `B`'s
    (hlt : (chainStateOf S.C B).h_F < (chainStateOf S.C B').h)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : max x[i].time x[j].time ≤ tR) :
    (chainStateOf S.C B).F.AncestorEq B' := by
  rcases lem68_past_finalized S.C B B' hlt with h | ⟨A, hA, hs⟩ | ⟨X, Y, hX, hY, hr, hne⟩
  · exact h
  · exfalso
    obtain ⟨u, huA, hHu⟩ := exists_honestThroughTime_of_card Sched hThird hA
    obtain ⟨a, a', hau, ha'u, ha, ha', hE1⟩ := hs u huA
    have hHk : HonestThrough x (max i j) u := honestThrough_of_time_le x hHu (time_max_le x i j)
    exact (not_slashable_of_held S Sched x hU hHk hau ha'u
      ⟨i, le_max_left i j, p, B, hB, ha⟩ ⟨j, le_max_right i j, w, B', hB', ha'⟩).1 hE1
  · exfalso
    have hmem : ∀ Z : Block V, (Z.AncestorEq B ∨ Z.AncestorEq B') → inHonestTreeBy x tR Z := by
      rintro Z (hZ | hZ)
      · exact ⟨i, p, hp, le_of_max_le_left htR, ancestors_mem_T_of_exec S Sched x i p B Z hB hZ⟩
      · exact ⟨j, w, hw, le_of_max_le_right htR, ancestors_mem_T_of_exec S Sched x j w B' Z hB' hZ⟩
    exact hne (hRoots X Y (hmem X hX) (hmem Y hY) hr)

/-! ## Lemma 89b -/

/-- **Lemma 89b over the reader's time.** The proof; the audited statement is in
`Statements/Executions/PhaseFrameStatements.lean`. It is the proof of Lemma 89b with the four facts
it reads of the phase as hypotheses: `GST + Δ S ≤ t`, the adversary bound at `t`, `t' + Δ S ≤ t`,
and `v` awake and honest at every time from `t − Δ S` to `t`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous;
- `t`: the time `v`'s state is read before; `t'`: the time of `u`'s tick; `i`: its step; `b`: the
  bound on the deadlines;
- `u`: the attester; `v`: the validator whose `h_max` is read; `a`: the attestation.

Restated with the delivery and roots premises up to `b`, the latest deadline being `t` (the
attestation's source block, which `u` holds before `t' ≤ t − Δ S`, reaching `v` by `t`). -/
theorem lem89b_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST t t' i b : ℕ) (u v : V) (a : Attestation V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject b)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject b)
    (hRoots : RootsNameBlocksUntil S Sched x b)
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    -- `t` is at least one delay after `GST`
    (hGST : GST + Δ S ≤ t)
    -- fewer than a third of the validators have been in the adversary set up to `t`
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (t : Int))
    -- `t` is at least one delay after `t'`
    (ht' : t' + Δ S ≤ t)
    -- `v` is awake and honest at every time from `t − Δ S` to `t`
    (hv : ∀ t'' : ℕ, t - Δ S ≤ t'' → t'' ≤ t →
      v ∈ Sched.awake (t'' : Int) ∧ v ∉ Sched.adv (t'' : Int))
    -- the step `i` is `u`'s tick at `t'`, and put `u`'s attestation `a` on the wire
    (hSend : x.lbl i = AtomicAction.tickAllAwake t' ∧
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- the latest deadline the proof reads is at most the bound
    (hb : t ≤ b) :
    a.h ≤ (stateBefore x t v).S.h_max := by
  obtain ⟨hl, hsent⟩ := hSend
  have huH : u ∉ Sched.adv (t' : Int) :=
    (Finset.mem_sdiff.1 (tick_send_of_honestSendAt hl hsent).1).2
  have hΔ := one_le_Δ S
  -- the source of `a`, held by `u` before `t'`
  obtain ⟨D, hDT, hDh⟩ := tick_attestation_source x hl hsent
  have hti : x[i].time + 1 = t' := (time_of_lbl_tickAllAwake x hl).1
  have hDb : D ∈ (stateBefore x t' u).S.T := by
    show D ∈ (x[stepBefore x t'][u].st).S.T
    rw [stepBefore_eq_of_lbl x hl]
    exact hDT
  -- `v`'s state before `t`
  have ht1 : 1 ≤ t := by omega
  have htv : x[stepBefore x t].time + 1 = t := (stepBefore_spec x hDiv ht1).2.1
  have hInvV := (lem11_node_invariant S Sched x (stepBefore x t) v).1
  have hCache := (lem46_finality_caches S Sched x (stepBefore x t) v).2
  -- `D` reaches `v` when it is compatible with `v`'s finalized block
  have hreach : (stateBefore x t v).S.F.compatible D = true → D ∈ (stateBefore x t v).S.T := by
    intro hc
    have e : t - Δ S + Δ S = t := by omega
    have hw : ∀ t'' : ℕ, t - Δ S ≤ t'' → t'' ≤ t - Δ S + Δ S →
        v ∈ Sched.awake (t'' : Int) ∧ v ∉ Sched.adv (t'' : Int) :=
      fun t'' h1 h2 => hv t'' h1 (by omega)
    have h := mem_T_before_add_delay_of_held_upTo hDiv hMono
      (SynchronyFromWakeUpTo.mono (by omega) hSync) (CatchUpOnWakeUpTo.mono (by omega) hCatch)
      (hRoots.mono (by omega)) hParent
      (t₁ := t') (t := t - Δ S) (by omega) (by omega) (by omega) huH hDb hw (by rw [e]; exact hc)
    rw [e] at h
    exact h
  by_contra hcon
  push Not at hcon
  -- `D` is compatible with `v`'s finalized block, by Lemma 89a
  have hcompat : (stateBefore x t v).S.F.compatible D = true := by
    obtain ⟨Bv, hBv, hFv⟩ := finalizedFromChain_of_exec S Sched x (stepBefore x t) v
    have hσv := hInvV.2.2.2.2.2.1 Bv hBv
    have hBvh : (chainStateOf S.C Bv).h ≤ (stateBefore x t v).S.h_max := by
      rw [← hσv]
      exact hCache Bv hBv
    have h47 := (lem47_chain_state_heights S.C Bv Bv).1
    have hc' : (stateBefore x t v).S.h_max < (chainStateOf S.C D).h := by
      rw [hDh]
      exact hcon
    have hlt : (chainStateOf S.C Bv).h_F < (chainStateOf S.C D).h :=
      lt_of_le_of_lt h47.2.2 (lt_trans h47.2.1 (lt_of_le_of_lt hBvh hc'))
    have hThird' : AdversaryFewerThanThirdUntil Sched (validator_count V)
        (max (x[stepBefore x t].time : Int) (x[i].time : Int)) :=
      have h1 : (x[stepBefore x t].time : Int) ≤ (t : Int) := by omega
      have h2 : (x[i].time : Int) ≤ (t : Int) := by omega
      adversaryFewerThanThirdUntil_of_le (max_le h1 h2) hThird
    have hvh : v ∉ Sched.adv (x[stepBefore x t].time : Int) := fun h =>
      (hv t (by omega) le_rfl).2 (hMono _ _ (by omega) h)
    have huh : u ∉ Sched.adv (x[i].time : Int) := fun h => huH (hMono _ _ (by omega) h)
    have hF := lem68_honest_past_finalized S Sched x hU hRoots (stepBefore x t) i v u Bv D hThird'
      hvh huh hBv hDT hlt (max_le (by omega) (by omega))
    show (x[stepBefore x t][v].st).S.F.compatible D = true
    rw [hFv]
    exact (compatible_iff _ _).2 (Or.inl hF)
  have hDv := hreach hcompat
  have hσD := hInvV.2.2.2.2.2.1 D hDv
  have hD := hCache D hDv
  rw [hσD] at hD
  have h1 : (chainStateOf S.C D).h ≤ (stateBefore x t v).S.h_max := hD
  rw [hDh] at h1
  exact absurd h1 (not_le.2 hcon)


/-- **Lemma 89b, the honest `h_max` keeps up with the honest attestations.** The proof; the audited
statement is in `Statements/Executions/PhaseFrameStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST ≤ tGAT ≤ tAwakeEnd`: the phase;
- `t`: the time `v`'s state is read before; `t'`: the time of `u`'s tick; `i`: its step;
- `u`: the attester; `v`: the validator whose `h_max` is read; `a`: the attestation.

Roots name blocks until `t`: `lem89b_at`, which the proof calls with `b := t`, takes blocks as held
up to `t`. -/
theorem lem89b_h_max_ge_attested (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd t t' i : ℕ) (u v : V)
    (a : Attestation V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x t)
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    -- the phase starts from `GST` on
    (hGST : GST ≤ tGAT)
    -- fewer than a third of the validators have been in the adversary set up to the phase's end
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    -- every validator honest at a time of the phase is awake then
    (hAwake : ∀ t'' : ℕ, tGAT ≤ t'' → t'' ≤ tAwakeEnd →
      ∀ w : V, w ∉ Sched.adv (t'' : Int) → w ∈ Sched.awake (t'' : Int))
    -- `t` is at least one delay into the phase, and at least one delay after `t'`
    (ht : tGAT + Δ S ≤ t) (ht' : t' + Δ S ≤ t) (htEnd : t ≤ tAwakeEnd)
    -- `v` is honest at `t`
    (hv : v ∉ Sched.adv (t : Int))
    -- the step `i` is `u`'s tick at `t'`, and put `u`'s attestation `a` on the wire
    (hSend : x.lbl i = AtomicAction.tickAllAwake t' ∧
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    a.h ≤ (stateBefore x t v).S.h_max := by
  have hΔ := one_le_Δ S
  refine lem89b_at S Sched x GST t t' i t u v a hDiv hMono
    (synchronyFromWakeUpTo_of_synchronyFromWake _ hSync)
    (catchUpOnWakeUpTo_of_catchUpOnWake _ hCatch) hRoots hParent hU (by omega)
    (adversaryFewerThanThirdUntil_of_le (by exact_mod_cast htEnd) hThird) ht' ?_ hSend le_rfl
  intro t'' h1 h2
  have hvt : v ∉ Sched.adv (t'' : Int) := fun h => hv (hMono _ _ (by omega) h)
  exact ⟨hAwake t'' (by omega) (by omega) v hvt, hvt⟩

/-! ## Lemma 89h -/

/-- **Lemma 89h, the threshold.** The proof; the audited statement is in
`Statements/Executions/PhaseFrameStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST ≤ tGAT ≤ tAwakeEnd`: the phase;
- `r₀`: the round; `s₀`: its first slot; `B₀`: the proposal; `p₀`: its proposer.

Roots name blocks until `slotStart S s₀`: `lem89b_at`, which the proof calls at `p₀` before the
start of slot `s₀`, takes blocks as held up to that start. -/
theorem lem89h_threshold (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r₀ s₀ : ℕ) (B₀ : Block V) (p₀ : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (slotStart S s₀))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    -- the phase starts from `GST` on
    (hGST : GST ≤ tGAT)
    -- fewer than a third of the validators have been in the adversary set up to the phase's end
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    -- every validator honest at a time of the phase is awake then
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ w : V, w ∉ Sched.adv (t : Int) → w ∈ Sched.awake (t : Int))
    -- `s₀` is the first slot of round `r₀`, and not slot `0`
    (hs₀ : s₀ = r₀ * S.C.R) (hs₁ : 1 ≤ s₀)
    -- slot `s₀` starts at least one delay into the phase, and its round acts inside the phase
    (hFirst : tGAT + Δ S ≤ slotStart S s₀) (hEnd : supportCutoff S (s₀ + 1) ≤ tAwakeEnd)
    -- `p₀` is honest at the start of slot `s₀`
    (hp₀ : p₀ ∉ Sched.adv ((slotStart S s₀ : ℕ) : Int))
    -- `p₀`'s tick at the start of slot `s₀` put `B₀` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s₀) ∧
      (⟨p₀, NamedObject.block B₀⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- `B₀`'s parent is in the viable tree of `p₀`'s frame before the start of slot `s₀`
    (hParentIn : B₀.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S s₀) p₀).S)
      (fg_to_ac (stateBefore x (slotStart S s₀) p₀).S).tree) :
    OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) ((chainStateOf S.C B₀).h + 1) := by
  intro i t v a hl ht _ _ hSent
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  -- the tick at `t` is the action time of a round `r < r₀`
  obtain ⟨-, n', sent, hrun, ha⟩ := tick_send_of_honestSendAt hl hSent
  obtain ⟨hAct, -⟩ := lem49_tick_attests S.C S.P S.X _ n' _ sent a hrun ha
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = S.C.round (S.C.slot (t : Int)) := ⟨_, rfl⟩
  rw [← hr] at hAct
  have htr : t = 4 * Δ S * (r * S.C.R) + 6 * Δ S := by
    have h2 : ((Δ S : ℕ) : Int) = S.C.Δ := Δ_cast S
    have h3 : S.C.a_ r = 4 * S.C.Δ * ((r * S.C.R : ℕ) : Int) + 6 * S.C.Δ := by
      rw [Config.a_, Config.T_, t_eq_mul]
    rw [h3, ← h2] at hAct
    exact_mod_cast hAct
  have hcut : supportCutoff S (s₀ + 1) = 4 * Δ S * s₀ + 6 * Δ S := by
    rw [supportCutoff_eq, voteTime_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
    omega
  have hstart : slotStart S s₀ = 4 * Δ S * s₀ := slotStart_eq S s₀
  have hrR : r * S.C.R < s₀ := by
    rw [htr, hcut] at ht
    have h4 : 4 * Δ S * (r * S.C.R) < 4 * Δ S * s₀ := by omega
    exact Nat.lt_of_mul_lt_mul_left h4
  have hrr : r < r₀ := by
    rw [hs₀] at hrR
    exact Nat.lt_of_mul_lt_mul_right hrR
  have hle : r * S.C.R + 2 ≤ s₀ := by
    have : (r + 1) * S.C.R ≤ r₀ * S.C.R := Nat.mul_le_mul_right _ hrr
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have ht' : t + Δ S ≤ slotStart S s₀ := by
    have h5 : 4 * Δ S * (r * S.C.R + 2) ≤ 4 * Δ S * s₀ := Nat.mul_le_mul_left _ hle
    rw [Nat.mul_add] at h5
    rw [htr, hstart]
    omega
  -- Lemma 89b at `p₀` before the start of slot `s₀`
  have hEnd' : slotStart S s₀ ≤ tAwakeEnd := by omega
  have h89b := lem89b_at S Sched x GST (slotStart S s₀) t i (slotStart S s₀) v p₀ a hDiv hMono
    (synchronyFromWakeUpTo_of_synchronyFromWake _ hSync)
    (catchUpOnWakeUpTo_of_catchUpOnWake _ hCatch) hRoots hParent hU (by omega)
    (adversaryFewerThanThirdUntil_of_le (by exact_mod_cast hEnd') hThird) ht'
    (fun t'' h1 h2 => by
      have hpt : p₀ ∉ Sched.adv (t'' : Int) := fun h => hp₀ (hMono _ _ (by omega) h)
      exact ⟨hAwake t'' (by omega) (by omega) p₀ hpt, hpt⟩)
    ⟨hl, hSent⟩ le_rfl
  -- `head_height_floor` at `p₀` (the least chain-state height a viable block may have) is `h_max` or `h_max − 1`, and at most `B₀`'s height
  have hs : s₀ - 1 + 1 = s₀ := by omega
  have hviable := proposal_viable S Sched x (s₀ - 1) B₀ p₀ (by rw [hs]; exact hPropose)
    (by rw [hs]; exact hParentIn)
  rw [hs] at hviable
  exact le_trans h89b (le_trans (h_max_le_floor_add_one _) (Nat.add_le_add_right hviable 1))

/-! ## The height bound from the old attestations -/

/-- **The height bound from the old attestations.** The proof; the audited statement is in
`Statements/Executions/PhaseFrameStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability;
- `i`: the step; `A`: the bound on the heights of the honest attestations; `v`: the holder;
  `D`: the block. -/
theorem attested_height_bound (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (i A : ℕ) (v : V)
    (D : Block V)
    (hAdv : AdversaryFewerThanThirdUntil Sched (validator_count V) (x[i].time : Int))
    (hOld : OldAttestationsAtMost S Sched x (x[i].time + 1) A)
    (hD : D ∈ (x[i][v].st).S.T) :
    (chainStateOf S.C D).h ≤ A + 1 := by
  by_contra hcon
  have hlt : A + 1 < (chainStateOf S.C D).h := Nat.lt_of_not_le hcon
  -- Lemma 67: an ancestor `Y` of `D` at height `A + 2` carries a certificate at height `A + 1`
  obtain ⟨Y, hYD, -, -, -, -, Q, hQ, hQm⟩ :=
    lem67_first_advance S.C D (A + 1) (Nat.succ_pos A) hlt
  have hY := ancestors_mem_T_of_exec S Sched x i v D Y hD hYD
  -- the certificate's quorum has a member `u` honest through the time of step `i`
  have hcard : Q.card ≤ validator_count V := Finset.card_le_univ Q
  have hQ' : 2 * quorum V - validator_count V ≤ Q.card := by omega
  obtain ⟨u, huQ, hHu⟩ := exists_honestThroughTime_of_card Sched hAdv hQ'
  obtain ⟨b, hbu, hbh, -, hon⟩ := hQm u huQ
  -- `u`'s attestation at height `A + 1` is in its record, so sent by its own tick before step `i`
  have hrec := lem74_honest_attestations_recorded S Sched x hU i v Y b hY hon
    (by rw [hbu]; exact hHu)
  rw [hbu] at hrec
  obtain ⟨j, t', a', hj, hl, hAw, hHon, hsent, -, hcont, -⟩ :=
    record_content_sent_step S Sched x u i b.content hrec
  have ht' : t' < x[i].time + 1 := by
    have h1 := (time_of_lbl_tickAllAwake x hl).2
    have h2 := time_mono x (show j + 1 ≤ i by omega)
    omega
  -- the old attestations are at height at most `A`
  have ha' := hOld j t' u a' hl ht' hAw hHon hsent
  have hab : a'.h = b.h := congrArg AttestationContent.h hcont
  rw [hab, hbh] at ha'
  exact Nat.not_succ_le_self A ha'

end GoldilocksCorrectness.Proofs.Executions
