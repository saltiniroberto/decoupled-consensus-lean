module
public import GoldilocksCorrectness.Proofs.Executions.Lemma80
public import GoldilocksCorrectness.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Proofs.Executions.PhaseChain
public import GoldilocksCorrectness.Proofs.Executions.PhaseKit
public import GoldilocksCorrectness.Proofs.Executions.TickUpdateState
public import GoldilocksCorrectness.Proofs.Executions.Lemma89f
public import GoldilocksCorrectness.Statements.Executions.QuietRoundDefs
public import GoldilocksCorrectness.Statements.Executions.HeightInvariantStatements
public import GoldilocksCorrectness.Proofs.Routines.ForkChoiceFacts

@[expose] public section

/-!
# Lemma 89r: a quiet round of the phase

The proof of `lem89r_quiet_round`, stated in
`GoldilocksCorrectness/Statements/Executions/Lemma89rStatements.lean`, and its kit. Write `s` for
the round's first slot, `B` for its honest proposal by `p`, `anchor_p` for `p`'s anchor at the
start of slot `s`, and `s''` for the next honest round opening slot.

The round reads `QuietRoundOnConfirmations`, `QuietRound` with the members' frames read relative
to every confirmation a member saves from slot `s − 1` on, and the next proposer's fork choice read
before the start of slot `s''` relative to a confirmation of slot `s'' − 2`. No clause of
`QuietRound` gives either reading, and the proof needs both: the chain step carries the invariant
to a confirmation only from frames relative to that confirmation, which may descend from `B`
strictly, and the round theorem reads the next proposer's frame at its proposal, which no reading
one delay earlier fixes.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff dutyWindowStart_mono
  dutyWindowStart_succ_le_slotStart one_le_Δ slotStart_eq slotStart_le_of_le
  slot_add_two_le_of_delivery supportCutoff_eq supportCutoff_le_slotStart_succ voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_J_spec chainStateOf_height_mono
  lem47_chain_state_heights)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (h_max_le_floor_add_one head_height_floor_initial
  mem_fg_to_ac_tree mem_viable_heads_iff)
open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed HeightCacheBounds)

open GoldilocksCorrectness.Proofs.Routines (get_anchor_root_or_viable)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_genesis_h chainStateOf_genesis_T_h
  fc_root_eq mem_viable_tree_iff)

open GoldilocksCorrectness.Proofs.Routines (initial_eq)

open GoldilocksCorrectness.Proofs.Routines (fg_contest_spec fg_contest_true_of
  head_height_floor_of_not_contested)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks CountedVotes ProposalCountedVotes
  FrameShape BoxOne BoxTwo BoxThree frameShape_of_boxOne frameShape_of_boxTwo
  frameShape_of_boxThree lem66_chain_state_certified)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  ancestorEq_compatible genesis_ancestorEq ancestorEq_of_parent?)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## The kit -/

/-- The anchor of `p`'s walk on its state before `t` has a viable head of `p`'s frame among its
descendants: a block `p` holds that is the anchor or a descendant of it, the fork-choice root or a
descendant of it, at a chain-state height at least the `head_height_floor`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `p`: the validator;
- `A`: the AC state the anchor reads; `t'`: the time it reads. -/
theorem anchor_has_viable_head (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (p : V) (A : ACState V) (t' : Time) :
    ∃ W ∈ (stateBefore x t p).S.T,
      (get_anchor A (fg_to_ac (stateBefore x t p).S) t').AncestorEq W ∧
      (get_fc_root (stateBefore x t p).S).AncestorEq W ∧
      head_height_floor (stateBefore x t p).S ≤ (chainStateOf S.C W).h := by
  have hσ : ∀ W ∈ (stateBefore x t p).S.T, (stateBefore x t p).S.σ W = chainStateOf S.C W :=
    fun W hW => (lem11_node_invariant S Sched x (stepBefore x t) p).1.2.2.2.2.2.1 W hW
  have hvh : ∀ W ∈ (fg_to_ac (stateBefore x t p).S).viable_heads,
      W ∈ (stateBefore x t p).S.T ∧ (get_fc_root (stateBefore x t p).S).AncestorEq W ∧
      head_height_floor (stateBefore x t p).S ≤ (chainStateOf S.C W).h := by
    intro W hW
    obtain ⟨hT, -, hR, hfl⟩ := (mem_viable_heads_iff _ _).1 hW
    exact ⟨hT, by rw [← fc_root_eq]; exact hR, by rw [← hσ W hT]; exact hfl⟩
  rcases get_anchor_root_or_viable A (fg_to_ac (stateBefore x t p).S) t' with h | h
  · obtain ⟨W, hW⟩ := frame_has_viable_head S Sched x t p
    obtain ⟨hT, hR, hfl⟩ := hvh W hW
    refine ⟨W, hT, ?_, hR, hfl⟩
    rw [h, fc_root_eq]
    exact hR
  · rw [mem_viable_tree_iff] at h
    obtain ⟨-, -, W, hW, hAW⟩ := h
    obtain ⟨hT, hR, hfl⟩ := hvh W (Finset.mem_inter.1 hW).2
    exact ⟨W, hT, hAW, hR, hfl⟩

/-- A validator awake and honest for one delay after `t` has a `head_height_floor` at least `p`'s
before `t`, under the hypotheses of `floor_le_of_delivery` without its order between `w`'s
finalized block and `p`'s fork-choice root.

Why: as `floor_le_of_delivery`; where that proof reads the order, to make `p`'s contest block and
`p`'s justification witness reach `w`, Lemma 89a gives it, both blocks being at a chain-state
height at least `w`'s `h_max`, greater than the finalization height of `w`'s finalized block's
chain.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `t`: the time `p`'s state is read before; `p`, `w`: the two
  validators.

Roots name blocks until `t + Δ S`: the proof takes `p`'s blocks, held before `t`, as reaching
`w` by `t + Δ S`, and compares `w`'s justified block, held before `t + Δ S`, with `p`'s (Lemma
89a and the uniqueness of roots). -/
theorem floor_le_of_delivery_unordered (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST t : ℕ) (p w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (t + Δ S))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    -- fewer than a third of the validators have been in the adversary set up to `t + Δ`
    (hAdv : AdversaryFewerThanThirdUntil Sched (validator_count V) ((t + Δ S : ℕ) : Int))
    -- `t` is from `GST` on
    (hGST : GST ≤ t)
    -- `p` is honest at `t`
    (hp : p ∉ Sched.adv (t : Int))
    -- `w` is awake and honest at every time from `t` to `t + Δ`
    (hw : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ S →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int)) :
    head_height_floor (stateBefore x t p).S ≤ head_height_floor (stateBefore x (t + Δ S) w).S := by
  rcases Nat.eq_zero_or_pos t with ht0 | ht1
  · subst ht0
    have h0 : (stateBefore x 0 p).S = FGState.initial := by
      unfold stateBefore
      rw [stepBefore_zero]
      obtain ⟨-, hn, -⟩ := x.init
      show ((x.cfg 0)[p].st).S = _
      rw [hn p, show (protocol S).init p = initial S.C p from rfl, initial_eq]
    rw [h0, head_height_floor_initial]
    exact Nat.zero_le _
  have hΔ := one_le_Δ S
  set kp := stepBefore x t with hkp
  set kw := stepBefore x (t + Δ S) with hkw
  have hkpt : x[kp].time ≤ t := time_stepBefore_le x t
  have hkwt : x[kw].time ≤ t + Δ S := time_stepBefore_le x (t + Δ S)
  have hpk : p ∉ Sched.adv (x[kp].time : Int) := fun h =>
    hp (hMono _ _ (by exact_mod_cast hkpt) h)
  have hwk : w ∉ Sched.adv (x[kw].time : Int) := fun h =>
    (hw (t + Δ S) (by omega) le_rfl).2 (hMono _ _ (by exact_mod_cast hkwt) h)
  have hThird : AdversaryFewerThanThirdUntil Sched (validator_count V)
      (max (x[kw].time : Int) (x[kp].time : Int)) :=
    adversaryFewerThanThirdUntil_of_le (max_le (by omega) (by omega)) hAdv
  -- the invariants of the two states
  have hInvP := (lem11_node_invariant S Sched x kp p).1
  have hInvW := (lem11_node_invariant S Sched x kw w).1
  have hCSp : ChainStatesComputed S.C (stateBefore x t p).S := hInvP.2.2.2.2.2.1
  have hCSw : ChainStatesComputed S.C (stateBefore x (t + Δ S) w).S := hInvW.2.2.2.2.2.1
  have hCacheW : HeightCacheBounds (stateBefore x (t + Δ S) w).S :=
    (lem46_finality_caches S Sched x kw w).2
  -- every block `p` holds before `t` that is compatible with `w`'s finalized block reaches `w`
  have hreach : ∀ Y ∈ (stateBefore x t p).S.T,
      (stateBefore x (t + Δ S) w).S.F.compatible Y = true →
      Y ∈ (stateBefore x (t + Δ S) w).S.T := fun Y hY hc =>
    mem_T_before_add_delay_of_held hDiv hMono hSync hCatch hRoots hParent
      (t₁ := t) (t := t) ht1 le_rfl hGST hp hY hw hc
  -- `w`'s finalized block is the finalized block of some held block's chain
  obtain ⟨Bw, hBw, hFw⟩ := finalizedFromChain_of_exec S Sched x kw w
  have hBwh : (chainStateOf S.C Bw).h ≤ (stateBefore x (t + Δ S) w).S.h_max := by
    rw [← hCSw Bw hBw]
    exact hCacheW Bw hBw
  have h47 := (lem47_chain_state_heights S.C Bw Bw).1
  -- a block `p` holds at a chain-state height at least `w`'s `h_max` is on `w`'s finalized
  -- block's chain (Lemma 89a)
  have hpast : ∀ Y ∈ (stateBefore x t p).S.T,
      (stateBefore x (t + Δ S) w).S.h_max ≤ (chainStateOf S.C Y).h →
      (stateBefore x (t + Δ S) w).S.F.AncestorEq Y := by
    intro Y hY hYh
    have hlt : (chainStateOf S.C Bw).h_F < (chainStateOf S.C Y).h :=
      lt_of_le_of_lt h47.2.2 (lt_of_lt_of_le h47.2.1 (le_trans hBwh hYh))
    have hFY := lem68_honest_past_finalized S Sched x hU hRoots kw kp w p Bw Y hThird hwk hpk
      hBw hY hlt (max_le hkwt (by omega))
    show (x[kw][w].st).S.F.AncestorEq Y
    rw [hFw]
    exact hFY
  -- step A: `p`'s `h_max` is at most `w`'s
  obtain ⟨⟨Dp, hDpT, hDpJ, hDpj⟩, ⟨X, hXT, hXh⟩, -⟩ := cachesWitnessed_of_stateBefore S Sched x t p
  obtain ⟨⟨Dw, hDwT, hDwJ, hDwj⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x (t + Δ S) w
  have hm : (stateBefore x t p).S.h_max ≤ (stateBefore x (t + Δ S) w).S.h_max := by
    by_contra hcon
    have hcon' : (stateBefore x (t + Δ S) w).S.h_max < (chainStateOf S.C X).h := by
      rw [hXh]
      exact Nat.lt_of_not_le hcon
    have hFX := hpast X hXT (le_of_lt hcon')
    have hXw := hreach X hXT ((compatible_iff _ _).2 (Or.inl hFX))
    have h1 := hCacheW X hXw
    rw [hCSw X hXw] at h1
    have h2 : (chainStateOf S.C X).h ≤ (stateBefore x (t + Δ S) w).S.h_max := h1
    exact absurd h2 (Nat.not_le.2 hcon')
  have hfw := h_max_le_floor_add_one (stateBefore x (t + Δ S) w).S
  have key1 : ∀ a b c : ℕ, a ≤ b → b ≤ c + 1 → a - 1 ≤ c := by intros; omega
  have key2 : ∀ a b c : ℕ, a < b → b ≤ c + 1 → a ≤ c := by intros; omega
  have key3 : ∀ a m hj bj bh hm : ℕ, a = m - 1 → a ≤ hj → hj = bj → bj < bh → bh ≤ hm →
      hm = m → hj = m - 1 := by intros; omega
  have key4 : ∀ m hj hm : ℕ, hm = m → hj = m - 1 → 1 ≤ m - 1 → hm = hj + 1 := by intros; omega
  -- step B: by `p`'s box
  cases hcp : fg_contest (stateBefore x t p).S with
  | false =>
      have hfloor : head_height_floor (stateBefore x t p).S =
          (stateBefore x t p).S.h_max - 1 := by
        exact head_height_floor_of_not_contested _ hcp
      rw [hfloor]
      exact key1 _ _ _ hm hfw
  | true =>
      obtain ⟨hbox, -, hfloor⟩ := frameShape_of_boxThree _ hcp
      rw [hfloor]
      -- the block that makes `p` contested
      obtain ⟨-, B', hB'T, -, hB'h, hJB'⟩ := fg_contest_spec _ hcp
      rcases Nat.lt_or_ge (stateBefore x t p).S.h_max
          (stateBefore x (t + Δ S) w).S.h_max with hlt | hge
      · exact key2 _ _ _ hlt hfw
      have heq : (stateBefore x (t + Δ S) w).S.h_max = (stateBefore x t p).S.h_max :=
        le_antisymm hge hm
      have hB'h' : (chainStateOf S.C B').h = (stateBefore x t p).S.h_max := by
        rw [← hCSp B' hB'T]
        exact hB'h
      have hFwB' : (stateBefore x (t + Δ S) w).S.F.AncestorEq B' :=
        hpast B' hB'T (by rw [hB'h', heq])
      have hB'w := hreach B' hB'T ((compatible_iff _ _).2 (Or.inl hFwB'))
      -- `p`'s justified block is justified at `h_max − 1 ≥ 1`
      have hjp : (chainStateOf S.C Dp).h_j = (stateBefore x t p).S.h_max - 1 := by
        rw [← hDpj, hbox, Nat.add_sub_cancel]
      have hj1 : 1 ≤ (chainStateOf S.C Dp).h_j := by
        rcases Nat.eq_zero_or_pos (chainStateOf S.C Dp).h_j with h0 | hpos
        · exfalso
          have hg := (chainStateOf_J_spec S.C Dp).2.1 h0
          rw [← hDpJ] at hg
          rw [hg] at hJB'
          exact hJB' (genesis_ancestorEq _)
        · exact hpos
      -- `Dp` reaches `w`, so `w`'s justification height is at least `h_max − 1`
      have hDp47 := (lem47_chain_state_heights S.C Dp Dp).1.2.1
      have hFwDp : (stateBefore x (t + Δ S) w).S.F.AncestorEq Dp :=
        hpast Dp hDpT (by rw [heq]; unfold Height at *; omega)
      have hDpw := hreach Dp hDpT ((compatible_iff _ _).2 (Or.inl hFwDp))
      have hjw1 := h_j_of_mem_T_of_stateBefore S Sched x (t + Δ S) w Dp hDpw hFwDp
      rw [hCSw Dp hDpw] at hjw1
      -- and at most `h_max − 1`
      have hDwh := hCacheW Dw hDwT
      rw [hCSw Dw hDwT] at hDwh
      have h47w := (lem47_chain_state_heights S.C Dw Dw).1.2.1
      have hjw : (stateBefore x (t + Δ S) w).S.h_j = (stateBefore x t p).S.h_max - 1 :=
        key3 _ _ _ _ _ _ hjp hjw1 hDwj h47w hDwh heq
      -- the two justified blocks are one block
      have hcertP := ((lem66_chain_state_certified S.C Dp).1 hj1).1
      have hjj : (chainStateOf S.C Dw).h_j = (chainStateOf S.C Dp).h_j :=
        hDwj.symm.trans (hjw.trans hjp.symm)
      have hj1w : 1 ≤ (chainStateOf S.C Dw).h_j := hjj ▸ hj1
      have hcertW := ((lem66_chain_state_certified S.C Dw).1 hj1w).1
      rw [hjj] at hcertW
      have hroots := lem76_honest_one_justification S Sched x hU kw kp w p hThird Dw Dp hDwT hDpT
        _ _ _ hcertW hcertP
      have hJwT := (lem57_justification_cache_and_record S Sched x kw w).2.2.1
      have hJpT := (lem57_justification_cache_and_record S Sched x kp p).2.2.1
      have hJJ : (stateBefore x (t + Δ S) w).S.J = (stateBefore x t p).S.J := by
        rw [hDwJ, hDpJ]
        refine hRoots _ _ ⟨kw, w, hwk, hkwt, ?_⟩ ⟨kp, p, hpk, by omega, ?_⟩ hroots
        · rw [← hDwJ]
          exact hJwT
        · rw [← hDpJ]
          exact hJpT
      -- `w` is contested by `B'`
      have hcw : fg_contest (stateBefore x (t + Δ S) w).S = true := by
        refine fg_contest_true_of _ B' (key4 _ _ _ heq hjw (hjp ▸ hj1)) hB'w hFwB' ?_ ?_
        · show ((stateBefore x (t + Δ S) w).S.σ B').h = _
          rw [hCSw B' hB'w, heq, ← hCSp B' hB'T]
          exact hB'h
        · rw [hJJ]
          exact hJB'
      obtain ⟨-, -, hfloorw⟩ :=
        GoldilocksCorrectness.Statements.Routines.frameShape_of_boxThree _ hcw
      rw [hfloorw, heq]

/-- Before `t`, when `v`'s fork-choice root is `B` or an ancestor of `B` and its
`head_height_floor` is at most `B`'s chain-state height `H`, `v`'s cache `h_j` is less than `H`, or
its record holds no lock at `H`, or its lock at `H` is the root of the block that took `B`'s chain
into `H`.

Why: in boxes 1 and 3 the cache `h_j` is less than the `head_height_floor`; in box 2 the
`head_height_floor` is `h_j`, and when it equals `H` the lock at `H` is on the justified block
(`lockBox_of_one_justification`), the fork-choice root, which took `B`'s chain into `H`
(`entry_block_of_boxTwo`, or at `H = 1` the genesis block).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `t`: the time;
  `v`: the validator; `B`: the block. -/
theorem lockBox_of_frame (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (t : ℕ) (v : V) (B : Block V)
    -- fewer than a third of the validators have been in the adversary set up to `t`
    (hAdv : AdversaryFewerThanThirdUntil Sched (validator_count V) (t : Int))
    -- `v`'s fork-choice root before `t` is `B` or an ancestor of `B`
    (hRoot : (get_fc_root (stateBefore x t v).S).AncestorEq B)
    -- `v`'s `head_height_floor` before `t` is at most `B`'s chain-state height
    (hFloor : head_height_floor (stateBefore x t v).S ≤ (chainStateOf S.C B).h) :
    (stateBefore x t v).S.h_j < (chainStateOf S.C B).h ∨
    (stateBefore x t v).Λ.lock (chainStateOf S.C B).h = none ∨
    (stateBefore x t v).Λ.lock (chainStateOf S.C B).h = some (chainStateOf S.C B).T_h.root := by
  obtain ⟨⟨D, hDT, hDJ, hDj⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x t v
  have hCS : ChainStatesComputed S.C (stateBefore x t v).S :=
    (lem11_node_invariant S Sched x (stepBefore x t) v).1.2.2.2.2.2.1
  have hCB : HeightCacheBounds (stateBefore x t v).S :=
    (lem46_finality_caches S Sched x (stepBefore x t) v).2
  have hDh : (chainStateOf S.C D).h ≤ (stateBefore x t v).S.h_max := by
    rw [← hCS D hDT]
    exact hCB D hDT
  have hD47 := (lem47_chain_state_heights S.C D D).1.2.1
  have hB47 := (lem47_chain_state_heights S.C B B).1.1
  have hjm : (stateBefore x t v).S.h_j + 1 ≤ (stateBefore x t v).S.h_max := by
    rw [hDj]
    unfold Height at *
    omega
  by_cases hm : (stateBefore x t v).S.h_max = (stateBefore x t v).S.h_j + 1
  · cases hc : fg_contest (stateBefore x t v).S with
    | true =>
        obtain ⟨-, -, hfl⟩ := frameShape_of_boxThree _ hc
        left
        rw [hfl] at hFloor
        unfold Height at *
        omega
    | false =>
        have hBox : BoxTwo (stateBefore x t v).S (stateBefore x t v).S.J := ⟨hm, hc, rfl⟩
        have hSh := frameShape_of_boxTwo _ _ hBox
        rw [hSh.2] at hFloor
        rw [hSh.1] at hRoot
        by_cases hlt : (stateBefore x t v).S.h_j < (chainStateOf S.C B).h
        · exact Or.inl hlt
        right
        have hH : (chainStateOf S.C B).h = (stateBefore x t v).S.h_max - 1 := by
          unfold Height at *
          omega
        cases hl : (stateBefore x t v).Λ.lock (chainStateOf S.C B).h with
        | none => exact Or.inl rfl
        | some T' =>
          right
          have hT' := lockBox_of_one_justification S Sched x hU t v v _ T' hAdv hBox
            (by rw [← hH]; exact hl)
          rw [hT']
          by_cases hJg : (stateBefore x t v).S.J = Block.genesis
          · -- the justified block is the genesis block, so `H = 1`
            have hDJg : (chainStateOf S.C D).J = Block.genesis := by rw [← hDJ]; exact hJg
            have hj1 : 1 ≤ (chainStateOf S.C D).h_j := by
              rcases Nat.eq_zero_or_pos (chainStateOf S.C D).h_j with h0 | hpos
              · exfalso
                unfold Height at *
                omega
              · exact hpos
            have hgh := (chainStateOf_J_spec S.C D).2.2 hj1
            rw [hDJg] at hgh
            have hg1 : (chainStateOf S.C (Block.genesis : Block V)).h = 1 :=
              chainStateOf_genesis_h S.C
            have hHg : (chainStateOf S.C (Block.genesis : Block V)).h = (chainStateOf S.C B).h := by
              unfold Height at *
              omega
            have hTh := (lem47_chain_state_heights S.C Block.genesis B).2.2.2.2
              (genesis_ancestorEq B) hHg
            have hTg : (chainStateOf S.C (Block.genesis : Block V)).T_h = Block.genesis :=
              chainStateOf_genesis_T_h S.C
            rw [hJg, ← hTh, hTg]
          · rw [entry_block_of_boxTwo S Sched x t v B _ hBox hJg hRoot hH]
  · left
    have hb : BoxOne (stateBefore x t v).S := by
      show (stateBefore x t v).S.h_j + 1 < (stateBefore x t v).S.h_max
      unfold Height at *
      omega
    have hSh := (frameShape_of_boxOne _ hb).2
    rw [hSh.2] at hFloor
    unfold Height at *
    omega

omit [RootOrder] in
/-- A set of validators containing every validator outside the adversary set at `t` is a quorum,
when fewer than a third of the validators have been in the adversary set up to `t`.

The variables:
- `Sched`: the schedule; `t`: the time; `Hon`: the set. -/
theorem quorum_le_of_phase_set (Sched : Schedule V) (t : ℕ) (Hon : Finset V)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (t : Int))
    (hSup : Finset.univ \ Sched.adv (t : Int) ⊆ Hon) : quorum V ≤ Hon.card := by
  have h1 := Finset.card_le_card hSup
  have h2 : 3 * (Sched.adv (t : Int)).card < validator_count V :=
    hThird _ (fun v hv => ⟨_, le_rfl, hv⟩)
  rw [Finset.card_univ_sdiff] at h1
  unfold quorum
  unfold validator_count at *
  omega

/-- The honest proposal of slot `s₀ + 1` is on the chain of every block of a family whose blocks
every slot-`s₀` vote of `Hs` extends, when the family holds `p`'s anchor and `p`'s frame has a
viable head on the chain of each of its blocks: every block of the family is `B`'s parent or an
ancestor of it.

Why: a vote of a member of `Hs` extends both a block `C` of the family and `p`'s anchor, so the two
are ordered. When `C` is an ancestor of the anchor, the anchor is an ancestor of `B`'s parent
(the walk starts there). Otherwise `p`'s walk passes `C`
(`proposal_parent_extends_majority_block` with `X := C`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `s₀`: the slot of the votes;
- `Hs`: the voters; `𝓒`: the family; `B`: the proposal of slot `s₀ + 1`; `p`: its proposer.

Roots name blocks until `supportCutoff S s₀`: the proof compares two blocks a member of `Hs`
holds before the vote time of slot `s₀`, and the proposer's walk
(`proposal_parent_extends_majority_block` at slot `s₀`) reads blocks held up to the support
cutoff of slot `s₀`. -/
theorem family_ancestorEq_proposal_parent (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ : ℕ) (Hs : Finset V) (𝓒 : Block V → Prop)
    (B : Block V) (p : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s₀))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s₀)
    -- each member of `Hs` is in the committee of slot `s₀`, honest at the start of slot `s₀ + 1`,
    -- and put a slot-`s₀` vote on the wire at its tick at the vote time of slot `s₀`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s₀ ∧ u ∉ Sched.adv (slotStart S (s₀ + 1) : Int) ∧
      ∃ vote : GoldfishVote V, ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s₀) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- each such vote names a block its voter holds that descends from every block of the family
    (hExt : ∀ C : Block V, 𝓒 C → ∀ u ∈ Hs, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s₀) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S s₀) u).S.T,
        vote = GoldfishVote.mk u s₀ H_u.root ∧ C.AncestorEq H_u)
    -- the validators with a slot-`s₀` vote in `p`'s pool before its proposal are fewer than twice
    -- `Hs`
    (hVotersP : voters_count ((stateBefore x (slotStart S (s₀ + 1)) p).A.pool s₀) < 2 * Hs.card)
    -- `p` is awake and honest from the vote time of slot `s₀` to its support cutoff
    (hp : ∀ t : ℕ, voteTime S s₀ ≤ t → t ≤ supportCutoff S s₀ →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    -- `p` put `B` on the wire at its tick at the start of slot `s₀ + 1`
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s₀ + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- `p`'s frame has a viable head on the chain of every block of the family
    (hFrameP : ∀ C : Block V, 𝓒 C →
      ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S (s₀ + 1)) p).S).tree,
        W ∈ (fg_to_ac (stateBefore x (slotStart S (s₀ + 1)) p).S).viable_heads ∧ C.AncestorEq W)
    -- the family holds `p`'s anchor
    (hAnchor : 𝓒 (get_anchor (stateBefore x (slotStart S (s₀ + 1)) p).A
      (fg_to_ac (stateBefore x (slotStart S (s₀ + 1)) p).S) ((slotStart S (s₀ + 1) : ℕ) : Int))) :
    ∀ C : Block V, 𝓒 C → C.AncestorEq B.parent := by
  intro C hC
  have hΔ := one_le_Δ S
  have hss : slotStart S (s₀ + 1) = slotStart S s₀ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv₀ : voteTime S s₀ = slotStart S s₀ + Δ S := voteTime_eq S s₀
  obtain ⟨i, hl, hsent⟩ := hPropose
  have hAP := get_anchor_ancestorEq_proposal_parent S Sched x (s₀ + 1) i B p hl hsent
  obtain ⟨u₀, hu₀⟩ : Hs.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨-, hu₀adv, vote₀, i₀, hl₀, hs₀⟩ := hHs u₀ hu₀
  obtain ⟨H₁, hH₁T, hv₁, hCH₁⟩ := hExt C hC u₀ hu₀ vote₀ ⟨i₀, hl₀, hs₀⟩
  obtain ⟨H₂, hH₂T, hv₂, hAH₂⟩ := hExt _ hAnchor u₀ hu₀ vote₀ ⟨i₀, hl₀, hs₀⟩
  have hroot : H₁.root = H₂.root := by
    rw [hv₁] at hv₂
    exact (GoldfishVote.mk.inj hv₂).2.2
  have hk := time_stepBefore_le x (voteTime S s₀)
  have hu₀k : u₀ ∉ Sched.adv ((x[stepBefore x (voteTime S s₀)].time : ℕ) : Int) := fun h =>
    hu₀adv (hMono _ _ (by exact_mod_cast (by omega : x[stepBefore x (voteTime S s₀)].time ≤
      slotStart S (s₀ + 1))) h)
  have hkc : x[stepBefore x (voteTime S s₀)].time ≤ supportCutoff S s₀ := by
    have := supportCutoff_eq S s₀
    omega
  have hH : H₁ = H₂ := hRoots _ _ ⟨_, u₀, hu₀k, hkc, hH₁T⟩ ⟨_, u₀, hu₀k, hkc, hH₂T⟩ hroot
  subst hH
  rcases ancestorEq_compatible hCH₁ hAH₂ with hCA | hAC
  · exact ancestorEq_trans hCA hAP
  · have hex : ∀ u ∈ Hs, ∃ H_u : Block V,
        (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s₀) ∧
          (⟨u, NamedObject.gfVote (GoldfishVote.mk u s₀ H_u.root)⟩ :
            SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
        H_u ∈ (stateBefore x (voteTime S s₀) u).S.T ∧ C.AncestorEq H_u := by
      intro u hu
      obtain ⟨-, -, vote, i', hl', hs'⟩ := hHs u hu
      obtain ⟨H_u, hT, hv, hCH⟩ := hExt C hC u hu vote ⟨i', hl', hs'⟩
      subst hv
      exact ⟨H_u, ⟨i', hl', hs'⟩, hT, hCH⟩
    choose Hc hHc using hex
    let Hf : V → Block V := fun u => if h : u ∈ Hs then Hc u h else C
    have hHf : ∀ u (hu : u ∈ Hs), Hf u = Hc u hu := fun u hu => dif_pos hu
    exact (proposal_parent_extends_majority_block S Sched x GST s₀ i Hs Hf C B p hDiv hMono hSync
      hCatch hRoots hParent hOwner hGST
      (fun u hu => by
        rw [hHf u hu]
        exact ⟨(hHs u hu).1, (hHs u hu).2.1, (hHc u hu).1, (hHc u hu).2.1, (hHc u hu).2.2⟩)
      (fun votes_p support_p hP => by rw [hP.1]; exact hVotersP) hp hl hsent (hFrameP C hC)
      hAC).1

/-- **The proposer clause gives `hFrameQ`.** When the round is quiet relative to its own
confirmations and `B` is an ancestor of, or equal to, every confirmation of slot `s'' − 2` that a
member of `Hon (s'' − 2)` saved (the chain invariant relative to `B` at that slot), the next
proposer's fork-choice root before the start of slot `s''` is compatible with `B` and, when it is
`B` or an ancestor of `B`, some viable head of its frame is `B` or a descendant of `B`: the
hypothesis `hFrameQ` of `lem80wq_round_height_advances_steps` at `q := S.P.proposer s''`.

Why: the root and `B` are both ancestors of, or equal to, that confirmation `C`, so they are
comparable; the viable head on `C`'s chain is on `B`'s.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `Hon`: one member set per slot; `B`: the round's proposal;
- `s`: the round's first slot; `s''`: the next honest round opening slot. -/
theorem frameQ_of_quietRoundOnConfirmations (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (Hon : ℕ → Finset V) (B : Block V) (s s'' : ℕ)
    (hQuiet : QuietRoundOnConfirmations S Sched x Hon B s s'')
    -- `B` is an ancestor of, or equal to, every confirmation of slot `s'' − 2` a member of
    -- `Hon (s'' − 2)` saved
    (hChainB : ∀ C : Block V, (∃ v ∈ Hon (s'' - 2),
      (stateBefore x (supportCutoff S (s'' - 1) + 1) v).A.saved_confirmation (s'' - 2) = some C) →
      B.AncestorEq C) :
    (fg_to_ac (stateBefore x (slotStart S s'') (S.P.proposer s'')).S).fc_root.compatible B = true ∧
    ((fg_to_ac (stateBefore x (slotStart S s'') (S.P.proposer s'')).S).fc_root.AncestorEq B →
      ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S s'') (S.P.proposer s'')).S).tree,
        W ∈ (fg_to_ac (stateBefore x (slotStart S s'') (S.P.proposer s'')).S).viable_heads ∧
        B.AncestorEq W) := by
  obtain ⟨C, hCsaved, hroot, W, hWtree, hWviable, hCW⟩ := hQuiet.2.2.2.2
  have hBC : B.AncestorEq C := hChainB C hCsaved
  refine ⟨(compatible_iff _ _).2 (ancestorEq_compatible hroot hBC), fun _ => ?_⟩
  exact ⟨W, hWtree, hWviable, ancestorEq_trans hBC hCW⟩

/-- **The frame of a member at the slot before the round, relative to the proposal.** When `w`
holds the proposal `B` of slot `s₀ + 1` before the vote time of slot `s₀ + 1`, its fork-choice root
then is `B` or an ancestor of `B` with its `head_height_floor` at most the chain-state height of
`B`, and its fork-choice root before the support cutoff of slot `s₀ + 2` is `B` or an ancestor of
`B`, then `StepFrameAt S Sched x B s₀ w` holds.

Why: the root is compatible with `B`; `B` is in `w`'s voter tree of slot `s₀ + 1` (a block of the
frame tree, stamped, of that slot) and is a viable head (its chain state is its own by Lemma 11,
at least the `head_height_floor`); the finalized block is the root or an ancestor of it (Lemma 46),
so it is compatible with `B`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `B`: the proposal; `s₀`: the slot before the proposal's; `w`: the member. -/
theorem stepFrameAt_proposal_of_quiet (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (B : Block V) (s₀ : ℕ) (w : V)
    -- `B` is a block of slot `s₀ + 1` that `w` holds before the vote time of that slot
    (hslot : B.slot = s₀ + 1)
    (hHeld : B ∈ (stateBefore x (voteTime S (s₀ + 1)) w).S.T)
    -- `w`'s fork-choice root before that vote time is `B` or an ancestor of `B`, and its
    -- `head_height_floor` then is at most the chain-state height of `B`
    (hRoot : (get_fc_root (stateBefore x (voteTime S (s₀ + 1)) w).S).AncestorEq B)
    (hFloor : head_height_floor (stateBefore x (voteTime S (s₀ + 1)) w).S ≤
      (chainStateOf S.C B).h)
    -- `w`'s fork-choice root before the support cutoff of slot `s₀ + 2` is `B` or an ancestor of
    -- `B`
    (hRootA : (get_fc_root (stateBefore x (supportCutoff S (s₀ + 2)) w).S).AncestorEq B) :
    StepFrameAt S Sched x B s₀ w := by
  have hF : (stateBefore x (voteTime S (s₀ + 1)) w).S.F.AncestorEq B :=
    ancestorEq_trans (F_ancestorEq_fc_root_of_stateBefore S Sched x _ w) hRoot
  have hσ : (stateBefore x (voteTime S (s₀ + 1)) w).S.σ B = chainStateOf S.C B :=
    (lem11_node_invariant S Sched x (stepBefore x (voteTime S (s₀ + 1))) w).1.2.2.2.2.2.1 B hHeld
  have hBtree : B ∈ (fg_to_ac (stateBefore x (voteTime S (s₀ + 1)) w).S).tree :=
    (mem_fg_to_ac_tree _ _).2 ⟨hHeld, hF⟩
  refine ⟨(compatible_iff _ _).2 (Or.inl (by rw [fc_root_eq]; exact hRoot)), fun hR tree htree => ⟨B, ?_, ?_,
    ancestorEq_refl B⟩, ?_⟩
  · obtain ⟨τ, τ', hτ, -, -⟩ := ancestor_blockStamp_le S Sched x
      (stepBefore x (voteTime S (s₀ + 1))) w B B hHeld (ancestorEq_refl B)
    exact (GoldilocksCorrectness.Proofs.Routines.mem_voter_block_tree_iff S.C _ _ (s₀ + 1) tree
      htree B).2 ⟨hBtree, τ, hτ, Or.inr ⟨B, hBtree, hslot, ancestorEq_refl B⟩⟩
  · refine (mem_viable_heads_iff _ _).2 ⟨hHeld, hF, hR, ?_⟩
    rw [hσ]
    exact hFloor
  · exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans
      (F_ancestorEq_fc_root_of_stateBefore S Sched x _ w) hRootA))

/-! ## Lemma 89r -/

/-- **Lemma 89r, a quiet round of the phase.** The proof; the audited statement is in
`Statements/Executions/Lemma89rStatements.lean`.

Roots name blocks until `supportCutoff S (s'' - 1)`: the round theorem
`lem80wq_round_height_advances_steps` at slot `s''` reads blocks held up to it, and the chain
steps of the slots before `s'' − 1` up to their support cutoffs, at most it. -/
theorem lem89r_quiet_round (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST r s s'' : ℕ) (Hon : ℕ → Finset V)
    (𝓒 : Block V → Prop) (B B' : Block V) (p q : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s'' - 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hs : s = r * S.C.R) (hs1 : 1 ≤ s) (hs'' : supportCutoff S (s + 1) + Δ_F S ≤ slotStart S s'')
    (hGST : GST ≤ voteTime S (s - 1))
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) ((supportCutoff S (s + 1) : ℕ) : Int))
    (hHonMono : ∀ s', s - 1 ≤ s' → s' + 1 < s'' → Hon (s' + 1) ⊆ Hon s')
    (hHon : ∀ s', s - 1 ≤ s' → s' < s'' → ∀ v ∈ Hon s', ∀ t : ℕ,
      dutyWindowStart S s' ≤ t → t ≤ supportCutoff S (s' + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hQuorum : quorum V ≤ (Hon s).card)
    (hCommittees : ∀ s', s - 1 ≤ s' → s' < s'' →
      (S.P.committee s').card < 2 * (S.P.committee s' ∩ Hon s').card)
    (hpAwake : ∀ t : ℕ, voteTime S (s - 1) ≤ t → t ≤ slotStart S s → p ∈ Sched.awake (t : Int))
    (hpHon : HonestThroughTime Sched ((voteTime S s : ℕ) : Int) p)
    (hq : q ∈ Hon (s'' - 1)) (hps : S.P.proposer s = p) (hqProp : S.P.proposer s'' = q)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hQuiet : QuietRoundOnConfirmations S Sched x Hon B s s'')
    (hChain : ChainInvFor S Sched x (Hon (s - 1)) 𝓒 (s - 1))
    (hFamLocks : ∀ w ∈ Hon (s - 1), LiveLocksOnFamilyAt S Sched x 𝓒 (s - 1) w)
    (hAnchor : 𝓒 (get_anchor (stateBefore x (slotStart S s) p).A
      (fg_to_ac (stateBefore x (slotStart S s) p).S) ((slotStart S s : ℕ) : Int)))
    (hFrameP : ∀ C : Block V, 𝓒 C →
      ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S s) p).S).tree,
        W ∈ (fg_to_ac (stateBefore x (slotStart S s) p).S).viable_heads ∧ C.AncestorEq W) :
    (∃ B₁ ∈ (stateBefore x (slotStart S s) p).S.T, B₁.root = B.root) ∨
    (B.AncestorEq B' ∧
    ((chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∨
      ((chainStateOf S.C B').h = (chainStateOf S.C B).h ∧
        B'.slot < (chainStateOf S.C B).T_h.slot + S.C.δt ∧
        ∃ Q : Finset V, quorum V ≤ Q.card ∧ Q ⊆ (chainStateOf S.C B').progress)) ∧
    ((∀ u ∈ Hon s, ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) u).Λ.sent,
        b.h ≠ (chainStateOf S.C B).h) →
      (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∧
        ((chainStateOf S.C B'.parent).h = (chainStateOf S.C B).h →
          (chainStateOf S.C B').J = (chainStateOf S.C B).T_h)) ∧
    (∀ v ∈ Hon s,
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some B) ∧
    ChainInvFor S Sched x (Hon (s'' - 1)) (fun C => 𝓒 C ∨ C = B ∨
      ∃ s', s - 1 ≤ s' ∧ s' + 2 ≤ s'' ∧ ∃ v ∈ Hon s',
        (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C)
      (s'' - 1) ∧
    (∀ w ∈ Hon (s'' - 1), LiveLocksOnFamilyAt S Sched x (fun C => 𝓒 C ∨ C = B ∨
      ∃ s', s - 1 ≤ s' ∧ s' + 2 ≤ s'' ∧ ∃ v ∈ Hon s',
        (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C)
      (s'' - 1) w)) := by
  -- the collision case
  by_cases hColl : ∃ B₁ ∈ (stateBefore x (slotStart S s) p).S.T, B₁.root = B.root
  · exact Or.inl hColl
  right
  have hRootNew : ∀ B₁ ∈ (stateBefore x (slotStart S s) p).S.T, B₁.root ≠ B.root :=
    fun B₁ hB₁ he => hColl ⟨B₁, hB₁, he⟩
  -- the slots: `s = s₀ + 1`, `s'' = s₂ + 2`
  have hR := S.C.R_ge_two
  have hs2 := slot_add_two_le_of_delivery S hs''
  obtain ⟨s₀, rfl⟩ : ∃ s₀, s = s₀ + 1 := ⟨s - 1, by omega⟩
  obtain ⟨s₂, rfl⟩ : ∃ s₂, s'' = s₂ + 2 := ⟨s'' - 2, by omega⟩
  simp only [Nat.add_sub_cancel] at hGST hHonMono hHon hCommittees hpAwake hChain hFamLocks ⊢
  simp only [show s₂ + 2 - 1 = s₂ + 1 by omega] at hq ⊢
  -- the clause of the quiet round relative to the confirmations, at the slots `s₀` to `s₂`
  have hQ4 : ∀ s', s₀ ≤ s' → s' ≤ s₂ → ∀ σ, s₀ ≤ σ → σ ≤ s' → ∀ v ∈ Hon σ,
      ∀ C : Block V,
        (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some C →
      ∀ w ∈ Hon (s' + 1), StepFrameAt S Sched x C s' w :=
    fun s' h1 h2 σ h3 h4 => hQuiet.2.2.2.1 s' (by omega) (by omega) σ (by omega) h4
  -- the times
  have hΔ := one_le_Δ S
  have hss : ∀ k, slotStart S (k + 1) = slotStart S k + 4 * Δ S := fun k => by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv : ∀ k, voteTime S k = slotStart S k + Δ S := voteTime_eq S
  have hc : ∀ k, supportCutoff S k = voteTime S k + Δ S := supportCutoff_eq S
  have hdw : ∀ k, dutyWindowStart S (k + 1) ≤ slotStart S k := dutyWindowStart_succ_le_slotStart S
  have hdwm : ∀ a b : ℕ, a ≤ b → dutyWindowStart S a ≤ dutyWindowStart S b :=
    fun a b h => dutyWindowStart_mono S h
  have hscm : ∀ a b : ℕ, a ≤ b → supportCutoff S a ≤ supportCutoff S b := by
    intro a b h
    have := slotStart_le_of_le S h
    rw [hc, hc, hv, hv]
    omega
  have hdwv : ∀ k, dutyWindowStart S k ≤ voteTime S k := by
    intro k
    have h1 := hdwm k (k + 1) (by omega)
    have h2 := hdw k
    have h3 := hv k
    omega
  have hvc : ∀ k, voteTime S k ≤ supportCutoff S (k + 1) := by
    intro k
    have h1 := hc (k + 1)
    have h2 := hv (k + 1)
    have h3 := hv k
    have h4 := hss k
    omega
  have hThirdAt : ∀ t : ℕ, t ≤ supportCutoff S (s₀ + 1 + 1) →
      AdversaryFewerThanThirdUntil Sched (validator_count V) (t : Int) :=
    fun t ht => adversaryFewerThanThirdUntil_of_le (by exact_mod_cast ht) hThird
  -- the voters of each slot: the committee members in the slot's set, each of whom votes
  set Hs : ℕ → Finset V := fun s' => S.P.committee s' ∩ Hon s' with hHsDef
  have hVotes : ∀ s', s₀ ≤ s' → s' < s₂ + 2 → ∀ u ∈ Hs s', u ∈ Hon s' ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent := by
    intro s' h1 h2 u hu
    obtain ⟨hk, huH⟩ := Finset.mem_inter.1 hu
    have hd := hdwv s'
    have hvc' := hvc s'
    obtain ⟨i, vote, hl, hvi, hvs, hsent⟩ := honest_votes_of_window S Sched x s' u hDiv hMono
      (fun t h1' h2' => (hHon s' h1 h2 u huH t h1' (by omega)).1)
      (hHon s' h1 h2 u huH _ hd hvc').2 hk
    exact ⟨huH, hk, vote, hvi, hvs, i, hl, hsent⟩
  have hCnt := fun s' (h1 : s₀ ≤ s') (h2 : s' < s₂ + 2) (t : ℕ) (v : V) =>
    counting_of_committee_majority S Sched x s' t (Hon s') v (hCommittees s' h1 h2)
  -- the proposer
  have hp' : ∀ t : ℕ, voteTime S s₀ ≤ t → t ≤ slotStart S (s₀ + 1) →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int) := by
    intro t h1 h2
    have h3 := hv (s₀ + 1)
    exact ⟨hpAwake t h1 h2, hpHon (t : Int) (by exact_mod_cast (by omega : t ≤ voteTime S (s₀ + 1)))⟩
  obtain ⟨iB, hlB, hsentB⟩ := id hPropose
  obtain ⟨hBslot, -, hBpar?, -⟩ := proposal_parent_walk_end S Sched x s₀ iB B p hlB hsentB
  have hPB : B.parent.AncestorEq B := ancestorEq_of_parent? hBpar?
  -- every block of the family is `B`'s parent or an ancestor of it
  have hFamPar : ∀ C : Block V, 𝓒 C → C.AncestorEq B.parent := by
    refine family_ancestorEq_proposal_parent S Sched x GST s₀ (Hs s₀) 𝓒 B p hDiv hMono hSync
      hCatch (hRoots.mono (hscm _ _ (by omega))) hParent hOwner hGST ?_ ?_ ?_ ?_ hPropose
      hFrameP hAnchor
    · intro u hu
      obtain ⟨huH, hk, vote, -, -, i, hl, hsent⟩ := hVotes s₀ le_rfl (by omega) u hu
      have h1 := hss s₀
      have h2 := hc (s₀ + 1)
      have h3 := hv (s₀ + 1)
      have h4 := hdwv s₀
      have h5 := hv s₀
      exact ⟨hk, (hHon s₀ le_rfl (by omega) u huH (slotStart S (s₀ + 1)) (by omega)
        (by omega)).2, vote, i, hl, hsent⟩
    · intro C hC u hu vote hsend
      exact (hChain C hC).1 u (Finset.mem_inter.1 hu).2 vote hsend
    · exact (hCnt s₀ le_rfl (by omega) (slotStart S (s₀ + 1)) p).2.1
    · intro t h1 h2
      have h3 := supportCutoff_le_slotStart_succ S s₀
      exact hp' t h1 (by omega)
  -- the anchor and the votes of slot `s₀`
  set anchor := get_anchor (stateBefore x (slotStart S (s₀ + 1)) p).A
    (fg_to_ac (stateBefore x (slotStart S (s₀ + 1)) p).S) ((slotStart S (s₀ + 1) : ℕ) : Int)
    with hanchor
  have hex : ∀ u ∈ Hs s₀, ∃ H_u : Block V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s₀) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s₀ H_u.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H_u ∈ (stateBefore x (voteTime S s₀) u).S.T ∧ anchor.AncestorEq H_u := by
    intro u hu
    obtain ⟨huH, -, vote, -, -, i, hl, hsent⟩ := hVotes s₀ le_rfl (by omega) u hu
    obtain ⟨H_u, hT, hvt, hAH⟩ := (hChain anchor hAnchor).1 u huH vote ⟨i, hl, hsent⟩
    subst hvt
    exact ⟨H_u, ⟨i, hl, hsent⟩, hT, hAH⟩
  choose Hc hHc using hex
  let H : V → Block V := fun u => if h : u ∈ Hs s₀ then Hc u h else B
  have hH : ∀ u (hu : u ∈ Hs s₀), H u = Hc u hu := fun u hu => dif_pos hu
  have hHsPrev : ∀ u ∈ Hs s₀, u ∈ S.P.committee s₀ ∧
      u ∉ Sched.adv (voteTime S (s₀ + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s₀) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s₀ (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s₀) u).S.T ∧ anchor.AncestorEq (H u) := by
    intro u hu
    obtain ⟨huH, hk, -⟩ := hVotes s₀ le_rfl (by omega) u hu
    have h1 := hc (s₀ + 1)
    have h2 := hdwv s₀
    have h3 := hvc s₀
    have h4 := hv (s₀ + 1)
    have h5 := hss s₀
    have h6 := hv s₀
    rw [hH u hu]
    exact ⟨hk, (hHon s₀ le_rfl (by omega) u huH (voteTime S (s₀ + 1)) (by omega)
      (by omega)).2, (hHc u hu).1,
      (hHc u hu).2.1, (hHc u hu).2.2⟩
  have hVotersPrev : ∀ w ∈ Hon (s₀ + 1), ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S (s₀ + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s₀ + 1)) w).S) (s₀ + 1) votes support_votes →
      voters_count votes < 2 * (Hs s₀).card :=
    fun w _ => (hCnt s₀ le_rfl (by omega) (voteTime S (s₀ + 1)) w).2.2
  -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
  have hLocksW : ∀ w ∈ Hon (s₀ + 1), ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s₀ + 1)) w).A
        ((voteTime S (s₀ + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s₀ + 1)) w).S)
        ((voteTime S (s₀ + 1) : ℕ) : Int) (s₀ + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s₀ + 1)) w).S)
          ((voteTime S (s₀ + 1) : ℕ) : Int) e = true → e.B.AncestorEq B.parent := by
    intro w hw A' hR e he hl
    obtain ⟨D, hD, heD⟩ := hFamLocks w (hHonMono s₀ le_rfl (by omega) hw) A' hR e he hl
    exact ancestorEq_trans heD (hFamPar D hD)
  have hOnly : ∀ w ∈ Hon (s₀ + 1), ∀ B₁ ∈ (stateBefore x (voteTime S (s₀ + 1)) w).S.T,
      B₁.slot = s₀ + 1 → B₁ = B :=
    fun w _ B₁ hB₁ hslot => only_block_of_unforgeability S Sched x hU (s₀ + 1)
      (voteTime S (s₀ + 1)) B B₁ p w hpHon hps hPropose hB₁ hslot
  -- the frames at the three reading points
  have hFloorW : ∀ w ∈ Hon (s₀ + 1),
      head_height_floor (stateBefore x (slotStart S (s₀ + 1)) p).S ≤
        head_height_floor (stateBefore x (voteTime S (s₀ + 1)) w).S ∧
      head_height_floor (stateBefore x (voteTime S (s₀ + 1)) w).S ≤
        (chainStateOf S.C B.parent).h := by
    intro w hw
    refine ⟨?_, (hQuiet.1 w hw).2⟩
    have h1 := hv (s₀ + 1)
    have h2 := hdw s₀
    have h3 := hss s₀
    have h4 := hvc (s₀ + 1)
    have h6 := hv s₀
    have hvR : slotStart S (s₀ + 1) + Δ S ≤ supportCutoff S (s₀ + 1 + 1) := by omega
    have hfl := floor_le_of_delivery_unordered S Sched x GST (slotStart S (s₀ + 1)) p w hDiv hMono
      hSync hCatch (hRoots.mono (le_trans hvR (hscm _ _ (by omega)))) hParent hU
      (hThirdAt _ (by omega)) (by omega)
      (hp' _ (by omega) le_rfl).2
      (fun t' h1' h2' => hHon (s₀ + 1) (by omega) (by omega) w hw t' (by omega) (by omega))
    rw [← hv (s₀ + 1)] at hfl
    exact hfl
  have hHeadP := anchor_has_viable_head S Sched x (slotStart S (s₀ + 1)) p
    (stateBefore x (slotStart S (s₀ + 1)) p).A ((slotStart S (s₀ + 1) : ℕ) : Int)
  -- the windows and counts as the round theorem reads them
  have hHonMono' : ∀ s', s₀ + 1 ≤ s' → s' + 1 < s₂ + 2 → Hon (s' + 1) ⊆ Hon s' :=
    fun s' h1 h2 => hHonMono s' (by omega) h2
  have hHon' : ∀ s', s₀ + 1 ≤ s' → s' < s₂ + 2 → ∀ v ∈ Hon s', ∀ t : ℕ,
      dutyWindowStart S s' ≤ t → t ≤ supportCutoff S (s' + 1) → t ≤ slotStart S (s₂ + 2) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int) :=
    fun s' h1 h2 v hv' t ht1 ht2 _ => hHon s' (by omega) h2 v hv' t ht1 ht2
  have hHs' : ∀ s', s₀ + 1 ≤ s' → s' < s₂ + 2 → ∀ u ∈ Hs s', u ∈ Hon s' ∧
      u ∈ S.P.committee s' ∧ ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent :=
    fun s' h1 h2 => hVotes s' (by omega) h2
  have hVoters' : ∀ s', s₀ + 1 ≤ s' → s' < s₂ + 2 → ∀ v ∈ Hon s',
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) v).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) v).S) (s' + 1) votes support_votes →
        voters_count votes < 2 * (Hs s').card) ∧
      voters_count ((stateBefore x (supportCutoff S (s' + 1)) v).A.pool s') < 2 * (Hs s').card :=
    fun s' h1 h2 v _ => ⟨(hCnt s' (by omega) h2 (voteTime S (s' + 1)) v).2.2,
      (hCnt s' (by omega) h2 (supportCutoff S (s' + 1)) v).2.1⟩
  have hStep : ∀ s', s₀ + 1 ≤ s' → s' + 3 ≤ s₂ + 2 → ∀ w ∈ Hon (s' + 1),
      StepFrameAt S Sched x B s' w :=
    fun s' h1 h2 w hw => hQuiet.2.2.1 s' h1 (by omega) w hw
  have hStepLast := fun w (hw : w ∈ Hon (s₂ + 1)) =>
    And.intro (hQuiet.2.2.1 s₂ (by omega) le_rfl w hw).1 (hQuiet.2.2.1 s₂ (by omega) le_rfl w hw).2.1
  have hLockBox : ∀ v ∈ Hon (s₀ + 1),
      (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).S.h_j < (chainStateOf S.C B).h ∨
      (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
      (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).Λ.lock (chainStateOf S.C B).h =
        some (chainStateOf S.C B).T_h.root :=
    fun v hv' => lockBox_of_frame S Sched x hU _ v B (hThirdAt _ le_rfl)
      (hQuiet.2.1 v hv').1 (hQuiet.2.1 v hv').2
  -- the base of the round
  obtain ⟨hHeld, hBase, hUpd⟩ := round_base_steps S Sched x GST (s₀ + 1) (Hon (s₀ + 1))
    (Hs (s₀ + 1)) (Hs s₀) H anchor B p _
    (fun w => head_height_floor (stateBefore x (voteTime S (s₀ + 1)) w).S)
    (fun v => head_height_floor (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).S)
    (get_fc_root (stateBefore x (slotStart S (s₀ + 1)) p).S)
    (fun w => get_fc_root (stateBefore x (voteTime S (s₀ + 1)) w).S)
    (fun v => get_fc_root (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).S)
    hDiv hMono hSync hCatch (hRoots.mono (hscm _ _ (by omega))) hParent hOwner (by omega)
    hGST
    (fun v hv' t h1 h2 => hHon (s₀ + 1) (by omega) (by omega) v hv' t h1 h2) hp' hPropose hHsPrev
    hVotersPrev (ancestorEq_refl _) hLocksW hOnly hRootNew (hHs' (s₀ + 1) le_rfl (by omega))
    (fun v hv' => (hVoters' (s₀ + 1) le_rfl (by omega) v hv').2)
    (hCnt (s₀ + 1) (by omega) (by omega) 0 p).1 ⟨rfl, rfl⟩ (fun _ _ => ⟨rfl, rfl⟩)
    (fun _ _ => ⟨rfl, rfl⟩) hFloorW (fun w hw => (hQuiet.1 w hw).1)
    (fun v hv' => (hQuiet.2.1 v hv').1) hHeadP
  -- the chain invariant relative to `B` at the slots `s₂` and `s₂ + 1`
  have hg1 := hv s₀
  have hg2 := hss s₀
  have hg3 := hv (s₀ + 1)
  have hg4 := hv s₂
  have hg5 := slotStart_le_of_le S (show s₀ ≤ s₂ by omega)
  have hGST₁ : GST ≤ voteTime S (s₀ + 1) := by omega
  have hGST₂ : GST ≤ voteTime S s₂ := by omega
  obtain ⟨hInv, -⟩ := round_honestChainExtends_steps S Sched x GST (s₀ + 1) s₂ Hon Hs B hDiv
    hMono hSync hCatch (hRoots.mono (hscm _ _ (by omega))) hParent hOwner hGST₁ (by omega)
    hHonMono' hHon' hHs'
    hVoters' hStep hStepLast hBase
  have hInv' := lem79_step_sets S Sched x GST s₂ (Hon s₂) (Hon (s₂ + 1)) Hs B hDiv hMono hSync
    hCatch (hRoots.mono (hscm _ _ (by omega))) hParent hOwner hGST₂ hInv
    (hHonMono s₂ (by omega) (by omega))
    (fun v hv' t ht1 ht2 => hHon s₂ (by omega) (by omega) v hv' t ht1 ht2)
    (fun v hv' t ht1 ht2 => hHon (s₂ + 1) (by omega) (by omega) v hv' t ht1 ht2)
    (hVotes s₂ (by omega) (by omega)) (hVotes (s₂ + 1) (by omega) (by omega))
    (fun w _ => (hCnt s₂ (by omega) (by omega) (voteTime S (s₂ + 1)) w).2.2)
    (fun v _ => (hCnt (s₂ + 1) (by omega) (by omega) (supportCutoff S (s₂ + 2)) v).2.1)
    (fun w hw => (hQuiet.2.2.1 s₂ (by omega) le_rfl w hw).1)
    (fun w hw => (hQuiet.2.2.1 s₂ (by omega) le_rfl w hw).2.1)
    (fun w hw => (hQuiet.2.2.1 s₂ (by omega) le_rfl w hw).2.2)
  -- the next proposer's frame on `B`'s chain, from the proposer clause and the chain invariant
  -- relative to `B` at slot `s₂`
  have hChainB : ∀ C : Block V, (∃ v ∈ Hon s₂,
      (stateBefore x (supportCutoff S (s₂ + 1) + 1) v).A.saved_confirmation s₂ = some C) →
      B.AncestorEq C := by
    rintro C ⟨v, hv', hC⟩
    exact hInv.2.2 v hv' C hC
  have hFrameQ := frameQ_of_quietRoundOnConfirmations S Sched x Hon B (s₀ + 1) (s₂ + 2) hQuiet
    hChainB
  rw [hqProp] at hFrameQ
  -- the round theorem
  obtain ⟨h80a, h80b, h80c⟩ :=
    GoldilocksCorrectness.Proofs.Executions.lem80wq_round_height_advances_steps S Sched x GST r
    (s₀ + 1) (s₂ + 2) Hon (Hon (s₀ + 1)) Hs H anchor B B' p q _
    (fun w => head_height_floor (stateBefore x (voteTime S (s₀ + 1)) w).S)
    (fun v => head_height_floor (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).S)
    (get_fc_root (stateBefore x (slotStart S (s₀ + 1)) p).S)
    (fun w => get_fc_root (stateBefore x (voteTime S (s₀ + 1)) w).S)
    (fun v => get_fc_root (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).S)
    hDiv hMono hSync hCatch hRoots hParent hOwner hSyncF hCatchF hs hs1 hs'' hGST
    hHonMono' hHon' hp' hPropose hHsPrev hVotersPrev (ancestorEq_refl _) hLocksW hOnly hRootNew
    hHs' hVoters'
    (fun votes sv hP => by
      rw [hP.1]
      exact (hCnt (s₂ + 1) (by omega) (by omega) (slotStart S (s₂ + 2)) q).2.1)
    (hCnt (s₀ + 1) (by omega) (by omega) 0 p).1 ⟨rfl, rfl⟩ (fun _ _ => ⟨rfl, rfl⟩)
    (fun _ _ => ⟨rfl, rfl⟩) hFloorW (fun v hv' => (hQuiet.2.1 v hv').2)
    (fun w hw => (hQuiet.1 w hw).1) (fun v hv' => (hQuiet.2.1 v hv').1) hHeadP hStep hStepLast
    (Finset.Subset.refl _) hQuorum hLockBox hq hFrameQ hPropose'
  -- the frame of every member of `Hon s` at slot `s₀` relative to `B`
  have hStepB₀ : ∀ w ∈ Hon (s₀ + 1), StepFrameAt S Sched x B s₀ w := fun w hw =>
    stepFrameAt_proposal_of_quiet S Sched x B s₀ w hBslot (hHeld w hw)
      (ancestorEq_trans (hQuiet.1 w hw).1 hPB)
      (le_trans (hQuiet.1 w hw).2 (chainStateOf_height_mono S.C hPB)) (hQuiet.2.1 w hw).1
  -- both invariants carried by the chain step `lem89s_chain_step` (the voters `Hon σ`, the members
  -- `Hon (σ + 1)`, the updaters `Hon σ`) and the lock invariant's step from slot `s₀` to slot
  -- `s₀ + n`, for `𝓒` and the ancestors of the confirmations of the slots from `s₀` to
  -- `s₀ + n − 1` saved by the members of each slot's own set
  have hIter : ∀ n, s₀ + n ≤ s₂ + 1 →
      ChainInvFor S Sched x (Hon (s₀ + n)) (fun C => 𝓒 C ∨ ∃ σ, s₀ ≤ σ ∧ σ < s₀ + n ∧
        ∃ v ∈ Hon σ, ∃ C' : Block V,
          (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some C' ∧
          C.AncestorEq C') (s₀ + n) ∧
      ∀ u ∈ Hon (s₀ + n), LiveLocksOnFamilyAt S Sched x (fun C => 𝓒 C ∨ ∃ σ, s₀ ≤ σ ∧
        σ < s₀ + n ∧ ∃ v ∈ Hon σ, ∃ C' : Block V,
          (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some C' ∧
          C.AncestorEq C') (s₀ + n) u := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · intro C hC
        rcases hC with hC | ⟨σ, h1, h2, -⟩
        · exact hChain C hC
        · omega
      · intro u hu A' hR' e he hl
        obtain ⟨D, hD, heD⟩ := hFamLocks u hu A' hR' e he hl
        exact ⟨D, Or.inl hD, heD⟩
    | succ n ih =>
      intro hn
      obtain ⟨hI, hL⟩ := ih (by omega)
      have hGSTn : GST ≤ voteTime S (s₀ + n) := by
        have h1 := slotStart_le_of_le S (show s₀ ≤ s₀ + n by omega)
        have h2 := hv (s₀ + n)
        omega
      -- the three sets of the chain step: the voters `Hon (s₀ + n)`, the members
      -- `Hon (s₀ + n + 1)`, the updaters `Hon (s₀ + n)`
      have hcN : supportCutoff S (s₀ + n + 1 + 1) = voteTime S (s₀ + n + 2) + Δ S :=
        supportCutoff_eq S _
      have hd0 : dutyWindowStart S (s₀ + n) ≤ supportCutoff S (s₀ + n + 1) :=
        dutyWindowStart_le_supportCutoff S (by omega)
      have hd1 : dutyWindowStart S (s₀ + n + 1) ≤ supportCutoff S (s₀ + n + 1) :=
        dutyWindowStart_le_supportCutoff S (by omega)
      have hd2 : dutyWindowStart S (s₀ + n + 1) ≤ supportCutoff S (s₀ + n + 1 + 1) :=
        dutyWindowStart_le_supportCutoff S (by omega)
      have hdd : dutyWindowStart S (s₀ + n) ≤ dutyWindowStart S (s₀ + n + 1) :=
        hdwm (s₀ + n) (s₀ + n + 1) (by omega)
      have hHonN := fun v hv' t ht1 ht2 => hHon (s₀ + n) (by omega) (by omega) v hv' t ht1 ht2
      have hHonN' := fun v hv' t ht1 ht2 =>
        hHon (s₀ + n + 1) (by omega) (by omega) v hv' t ht1 ht2
      have hHonA : Hon (s₀ + n) ⊆ honestActiveAt S Sched (s₀ + n) := by
        intro u hu
        unfold honestActiveAt activeAt
        rw [Finset.mem_sdiff]
        exact ⟨mem_awakeThroughout_of_forall (fun t h1 h2 => (hHonN u hu t h1 h2).1),
          (hHonN u hu _ hd0 le_rfl).2⟩
      have hHon'A : Hon (s₀ + n + 1) ⊆ honestActiveAt S Sched (s₀ + n + 1) := by
        intro u hu
        unfold honestActiveAt activeAt
        rw [Finset.mem_sdiff]
        exact ⟨mem_awakeThroughout_of_forall (fun t h1 h2 => (hHonN' u hu t h1 h2).1),
          (hHonN' u hu _ hd2 le_rfl).2⟩
      have hUpdN : Hon (s₀ + n) ⊆ updaterAt S Sched (s₀ + n) := by
        intro u hu
        unfold updaterAt
        rw [Finset.mem_sdiff]
        exact ⟨mem_awakeThroughout_of_forall (fun t h1 h2 =>
            (hHonN u hu t (le_trans hdd h1) h2).1),
          (hHonN u hu _ (le_trans hdd hd1) le_rfl).2⟩
      have hSubN : Hon (s₀ + n + 1) ⊆ Hon (s₀ + n) := hHonMono (s₀ + n) (by omega) (by omega)
      have hStepN : ∀ C : Block V, ((fun C => 𝓒 C ∨ ∃ σ, s₀ ≤ σ ∧ σ < s₀ + n ∧
          ∃ v ∈ Hon σ, ∃ C' : Block V,
            (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some C' ∧
            C.AncestorEq C') C ∨ ∃ v ∈ Hon (s₀ + n),
          (stateBefore x (supportCutoff S (s₀ + n + 1) + 1) v).A.saved_confirmation (s₀ + n) =
            some C) →
          ∀ w ∈ Hon (s₀ + n + 1), StepFrameAt S Sched x C (s₀ + n) w := by
        -- the frame conditions of the step at slot `s₀ + n`
        intro C hC w hw
        rcases hC with (hC | ⟨σ, h1, h2, v, hv', C', hC', hCC'⟩) | ⟨v, hv', hC⟩
        · -- a block of `𝓒`: `B`'s parent or an ancestor of it
          refine stepFrameAt_of_ancestorEq S Sched x B C (s₀ + n) w
            (ancestorEq_trans (hFamPar C hC) hPB) ?_
          rcases Nat.eq_zero_or_pos n with rfl | hn0
          · exact hStepB₀ w hw
          · exact hQuiet.2.2.1 (s₀ + n) (by omega) (by omega) w hw
        · -- an ancestor of a member's confirmation of an earlier slot of the window
          exact stepFrameAt_of_ancestorEq S Sched x C' C (s₀ + n) w hCC'
            (hQ4 (s₀ + n) (by omega) (by omega) σ h1 (by omega) v hv' C' hC' w hw)
        · -- a member's confirmation of slot `s₀ + n`
          exact hQ4 (s₀ + n) (by omega) (by omega) (s₀ + n) (by omega) le_rfl v hv' C hC w hw
      have hP1 := lem89s_chain_step S Sched x GST (s₀ + n) (Hon (s₀ + n)) (Hon (s₀ + n + 1))
        (Hon (s₀ + n)) _ hDiv hMono hSync hCatch (hRoots.mono (hscm _ _ (by omega))) hParent
        hOwner hGSTn hHonA hHon'A
        hUpdN hSubN (hCommittees (s₀ + n) (by omega) (by omega))
        (hCommittees (s₀ + n + 1) (by omega) (by omega)) hI (fun u hu => Or.inl (hSubN hu)) hL
        (fun C hC v hv C' hC' => (hI C hC).2.2 v hv C' hC') hStepN
      -- the lock invariant at every member of `Hon (s₀ + n + 1)`, its own confirmation joining
      -- the family since it is a member of `Hon (s₀ + n)`
      have hP2 : ∀ u ∈ Hon (s₀ + n + 1), LiveLocksOnFamilyAt S Sched x (fun C => (𝓒 C ∨
          ∃ σ, s₀ ≤ σ ∧ σ < s₀ + n ∧ ∃ v ∈ Hon σ, ∃ C' : Block V,
            (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some C' ∧
            C.AncestorEq C') ∨ ∃ v ∈ Hon (s₀ + n), ∃ C' : Block V,
          (stateBefore x (supportCutoff S (s₀ + n + 1) + 1) v).A.saved_confirmation (s₀ + n) =
            some C' ∧ C.AncestorEq C') (s₀ + n + 1) u :=
        fun u hu => liveLocksOnFamilyAt_step S Sched x _ _ (s₀ + n) u hDiv
          (fun t h1 h2 => hHonN' u hu t (le_trans (dutyWindowStart_mono S (by omega)) h1) (by omega)) (fun C hC => Or.inl hC)
          (fun C hC => Or.inr ⟨u, hSubN hu, C, hC, ancestorEq_refl C⟩) (hL u (hSubN hu))
      have hP := And.intro hP1 hP2
      · refine ⟨?_, ?_⟩
        · intro C hC
          refine hP.1 C ?_
          rcases hC with hC | ⟨σ, h1, h2, v, hv', C', hC', hCC'⟩
          · exact Or.inl (Or.inl hC)
          · rcases Nat.lt_or_ge σ (s₀ + n) with hlt | hge
            · exact Or.inl (Or.inr ⟨σ, h1, hlt, v, hv', C', hC', hCC'⟩)
            · obtain rfl : σ = s₀ + n := by omega
              exact Or.inr ⟨v, hv', C', hC', hCC'⟩
        · intro u hu A' hR' e he hl
          obtain ⟨D, hD, heD⟩ := hP.2 u hu A' hR' e he hl
          refine ⟨D, ?_, heD⟩
          rcases hD with (hD | ⟨σ, h1, h2, v, hv', C', hC', hDC'⟩) | ⟨v, hv', C', hC', hDC'⟩
          · exact Or.inl hD
          · exact Or.inr ⟨σ, h1, by omega, v, hv', C', hC', hDC'⟩
          · exact Or.inr ⟨s₀ + n, by omega, by omega, v, hv', C', hC', hDC'⟩
  have hFinal := hIter (s₂ + 1 - s₀) (by omega)
  rw [show s₀ + (s₂ + 1 - s₀) = s₂ + 1 by omega] at hFinal
  refine ⟨h80a, ?_, h80c, ?_, ?_, ?_⟩
  · rcases h80b with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h3, Hon (s₀ + 1), hQuorum, h2⟩
  · -- every member saves `B` as the confirmation of slot `s`
    intro v hv'
    obtain ⟨A', hA', hsave, -⟩ := hUpd v hv'
    have h1 := hdwm (s₀ + 1) (s₀ + 1 + 1) (by omega)
    have h2 := hdwv (s₀ + 1 + 1)
    have h3 := hc (s₀ + 1 + 1)
    have hva := hHon (s₀ + 1) (by omega) (by omega) v hv' (supportCutoff S (s₀ + 1 + 1))
      (by omega) le_rfl
    have hAw := awakeSince_le_dutyWindowStart_b S Sched x (s₀ + 1 + 1)
      (supportCutoff S (s₀ + 1 + 1)) v hDiv hMono (by omega)
      (fun t h1' h2' => (hHon (s₀ + 1) (by omega) (by omega) v hv' t (by omega) h2').1) hva.2
    obtain ⟨A'', hA'', hsave', -, -, -⟩ :=
      update_state_of_duty S Sched x (s₀ + 1) v hDiv hva hAw
    have hAA : A' = A'' := by
      rw [hA'] at hA''
      injection hA''
    rw [hsave', ← hAA]
    exact hsave
  · -- the chain invariant at slot `s'' − 1`
    intro C hC
    rcases hC with hC | rfl | ⟨σ, h1, h2, v, hv', hC⟩
    · exact hFinal.1 C (Or.inl hC)
    · exact hInv'
    · exact hFinal.1 C (Or.inr ⟨σ, h1, by omega, v, hv', C, hC, ancestorEq_refl C⟩)
  · -- the lock invariant at slot `s'' − 1`
    intro w hw A' hR' e he hl
    obtain ⟨D, hD, heD⟩ := hFinal.2 w hw A' hR' e he hl
    rcases hD with hD | ⟨σ, h1, h2, v, hv', C', hC', hDC'⟩
    · exact ⟨D, Or.inl hD, heD⟩
    · exact ⟨C', Or.inr (Or.inr ⟨σ, h1, by omega, v, hv', hC'⟩), ancestorEq_trans heD hDC'⟩

end GoldilocksCorrectness.Proofs.Executions
