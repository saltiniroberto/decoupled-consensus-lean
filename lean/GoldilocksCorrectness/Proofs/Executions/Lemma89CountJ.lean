module
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Count
public import GoldilocksCorrectness.Proofs.Executions.Lemma89ChangeJ
public import GoldilocksCorrectness.Proofs.Executions.Lemma89StabilityJ
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders

@[expose] public section

/-!
- a held block's spreading (`held_spread`) and its consequences for `h_j` and `h_max`;
- a contested FG state stays contested while its `h_max` stays (`contest_persists`);
- `fork_choice_change_kinds`: every fork-choice change of the climb is one of four kinds,
  within one delay after the kind's first time.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ)
open GoldilocksCorrectness.Proofs.Routines (slot_mono slot_mono_int)

open GoldilocksCorrectness.Proofs.Routines (lem47_chain_state_heights)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (fg_contest_spec fg_contest_true_of floor_cases
  floor_le_h_max h_max_sub_one_le_floor root_cases)

open GoldilocksCorrectness.Proofs.Routines (block_admissible_of mem_T_receive_block)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq ancestorEq_compatible ancestorEq_antisymm)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## Honesty at the time of a configuration -/

/-- A validator honest at `t` is honest at the time of the configuration `stepBefore x t`, which
is at most `t`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `w`: the validator; `t`: the time. -/
theorem honest_config {S : Setup V} {Sched : Schedule V} (x : AtomicExec (protocol S) Sched)
    (hMono : Sched.MonotoneCorruption) {w : V} {t : ℕ} (hw : w ∉ Sched.adv (t : Int)) :
    w ∉ Sched.adv ((x[stepBefore x t].time : ℕ) : Int) :=
  fun h => hw (hMono _ _ (by exact_mod_cast time_stepBefore_le x t) h)

/-- A validator honest at `t` is honest at the time of the configuration `stepBefore x (t + 1)`,
which is `t`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `w`: the validator; `t`: the time. -/
theorem honest_config_succ {S : Setup V} {Sched : Schedule V} (x : AtomicExec (protocol S) Sched)
    (hDiv : TimeDiverges x.toTrace) {w : V} {t : ℕ} (hw : w ∉ Sched.adv (t : Int)) :
    w ∉ Sched.adv ((x[stepBefore x (t + 1)].time : ℕ) : Int) := by
  have he : x[stepBefore x (t + 1)].time = t :=
    Nat.add_right_cancel (stepBefore_spec x hDiv (Nat.succ_pos t)).2.1
  rw [he]
  exact hw

/-! ## The kit with honesty at the configuration's time -/

/-- `F_ancestorEq_of_high` with the two validators honest at the times of the configurations their
states are read from (`stepBefore x t`, `stepBefore x t'`), rather than at `t` and `t'`. The proof
is the landed one.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tEnd`: the time up to which the
  adversary bound holds; `t`, `t'`: the two times; `w`, `p`: the two validators; `B`: the block.

Roots name blocks until `tR`, at least `max t t'`: the proof compares (Lemma 89a) a block `w`
holds before `t` with `B`, which `p` holds before `t'`. -/
theorem F_ancestorEq_of_high_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    {tR : ℕ} (hRoots : RootsNameBlocksUntil S Sched x tR)
    (tEnd t t' : ℕ) (w p : V) (B : Block V)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int)) (ht : t ≤ tEnd) (ht' : t' ≤ tEnd)
    (hw : w ∉ Sched.adv ((x[stepBefore x t].time : ℕ) : Int))
    (hp : p ∉ Sched.adv ((x[stepBefore x t'].time : ℕ) : Int))
    (hB : B ∈ (stateBefore x t' p).S.T)
    (hlt : (stateBefore x t w).S.h_j < (chainStateOf S.C B).h)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : max t t' ≤ tR) :
    (stateBefore x t w).S.F.AncestorEq B := by
  obtain ⟨D, hD, hF⟩ := finalizedFromChain_of_exec S Sched x (stepBefore x t) w
  have hSt : stateBefore x t w = x[stepBefore x t][w].st := rfl
  rw [← hSt] at hD hF
  by_cases h0 : (chainStateOf S.C D).h_F = 0
  · rw [hF, GoldilocksCorrectness.Proofs.Routines.chainStateOf_F_genesis S.C D h0]
    exact genesis_ancestorEq B
  have hFD : (chainStateOf S.C D).F.AncestorEq D :=
    ((GoldilocksCorrectness.Statements.Routines.lem66_chain_state_certified S.C D).2.2
      (Nat.one_le_iff_ne_zero.mpr h0)).2.2.1
  have hjD : ((stateBefore x t w).S.σ D).h_j ≤ (stateBefore x t w).S.h_j :=
    h_j_of_mem_T_of_stateBefore S Sched x t w D hD (by rw [hF]; exact hFD)
  rw [σ_eq_of_stateBefore S Sched x t w D hD] at hjD
  have hFj := (lem47_chain_state_heights S.C D D).1.2.2
  have hlt' : (chainStateOf S.C D).h_F < (chainStateOf S.C B).h :=
    lt_of_le_of_lt hFj (lt_of_le_of_lt hjD hlt)
  have hti := time_stepBefore_le x t
  have htj := time_stepBefore_le x t'
  have hT : AdversaryFewerThanThirdUntil Sched (validator_count V)
      (max (x[stepBefore x t].time : Int) (x[stepBefore x t'].time : Int)) :=
    adversaryFewerThanThirdUntil_of_le (max_le (by exact_mod_cast (show x[stepBefore x t].time ≤
      tEnd by omega)) (by exact_mod_cast (show x[stepBefore x t'].time ≤ tEnd by omega))) hThird
  have h68 := lem68_honest_past_finalized S Sched x hU hRoots (stepBefore x t)
    (stepBefore x t') w p D B hT hw hp hD hB hlt' (le_trans (max_le_max hti htj) htR)
  rw [hF]
  exact h68

/-- `eq_of_cert_same_height` with the two holders honest at the times of the configurations their
states are read from. The proof is the landed one.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tEnd`, `t`, `t'`: the times;
  `p`, `w`: the two holders; `B₁`, `B₂`: the blocks carrying the certificates; `h`: the height;
  `T`, `T'`: the justified blocks.

Roots name blocks until `tR`, at least `max t t'`: the proof compares `T`, held by `p` before
`t`, with `T'`, held by `w` before `t'`. -/
theorem eq_of_cert_same_height_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) {tR : ℕ} (hRoots : RootsNameBlocksUntil S Sched x tR)
    (tEnd t t' : ℕ) (p w : V) (B₁ B₂ T T' : Block V) (h : Height)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int)) (ht : t ≤ tEnd) (ht' : t' ≤ tEnd)
    (hp : p ∉ Sched.adv ((x[stepBefore x t].time : ℕ) : Int))
    (hw : w ∉ Sched.adv ((x[stepBefore x t'].time : ℕ) : Int))
    (hB₁ : B₁ ∈ (stateBefore x t p).S.T) (hB₂ : B₂ ∈ (stateBefore x t' w).S.T)
    (hJ : GoldilocksCorrectness.Statements.Routines.JustificationCertOn B₁ h T)
    (hJ' : GoldilocksCorrectness.Statements.Routines.JustificationCertOn B₂ h T')
    (hT : T ∈ (stateBefore x t p).S.T) (hT' : T' ∈ (stateBefore x t' w).S.T)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : max t t' ≤ tR) :
    T = T' := by
  have hti := time_stepBefore_le x t
  have htj := time_stepBefore_le x t'
  have hA : AdversaryFewerThanThirdUntil Sched (validator_count V)
      (max (x[stepBefore x t].time : Int) (x[stepBefore x t'].time : Int)) :=
    adversaryFewerThanThirdUntil_of_le (max_le (by exact_mod_cast (show x[stepBefore x t].time ≤
      tEnd by omega)) (by exact_mod_cast (show x[stepBefore x t'].time ≤ tEnd by omega))) hThird
  have hroot := lem76_honest_one_justification S Sched x hU (stepBefore x t) (stepBefore x t') p w
    hA B₁ B₂ hB₁ hB₂ h T T' hJ hJ'
  exact hRoots T T' ⟨stepBefore x t, p, hp, le_trans hti (le_trans (le_max_left _ _) htR), hT⟩
    ⟨stepBefore x t', w, hw, le_trans htj (le_trans (le_max_right _ _) htR), hT'⟩ hroot

/-- `J_eq_of_h_j_eq` with the two validators honest at the times of the configurations their states
are read from. The proof is the landed one.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tEnd`, `t`, `t'`: the times;
  `p`, `q`: the two validators.

Roots name blocks until `tR`, at least `max t t'`: `eq_of_cert_same_height_at` at the times `t`
and `t'`. -/
theorem J_eq_of_h_j_eq_at (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    {tR : ℕ} (hRoots : RootsNameBlocksUntil S Sched x tR) (tEnd t t' : ℕ) (p q : V)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int)) (ht : t ≤ tEnd) (ht' : t' ≤ tEnd)
    (hp : p ∉ Sched.adv ((x[stepBefore x t].time : ℕ) : Int))
    (hq : q ∉ Sched.adv ((x[stepBefore x t'].time : ℕ) : Int))
    (heq : (stateBefore x t p).S.h_j = (stateBefore x t' q).S.h_j)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : max t t' ≤ tR) :
    (stateBefore x t p).S.J = (stateBefore x t' q).S.J := by
  by_cases h0 : (stateBefore x t p).S.h_j = 0
  · rw [J_genesis S Sched x t p h0, J_genesis S Sched x t' q (heq ▸ h0)]
  have h1 : 1 ≤ (stateBefore x t p).S.h_j := Nat.one_le_iff_ne_zero.mpr h0
  obtain ⟨W, hW, hc⟩ := J_cert S Sched x t p h1
  obtain ⟨W', hW', hc'⟩ := J_cert S Sched x t' q (heq ▸ h1)
  rw [← heq] at hc'
  exact eq_of_cert_same_height_at S Sched x hU hRoots tEnd t t' p q W W' _ _ _ hThird ht ht'
    hp hq hW hW' hc hc' (J_mem_T S Sched x t p) (J_mem_T S Sched x t' q) htR

/-- `mem_T_before_add_delay_of_held` with the holder `u` honest at the time of the configuration
`stepBefore x t₁` its tree is read from, rather than at `t₁`. The proof is the landed one; the
holder's honesty is read only there (the sender's honesty at its own send comes with the send).

The variables:
- `x`: the execution; `GST`: the time from which the network is synchronous; `t₁ ≤ t`: the two
  times; `u`: the holder; `w`: the receiver; `B`: the block.

Roots name blocks until `t + Δ S`: the proof compares the block `w` holds at the delivery, a step
at a time before `t + Δ S`, with `B`, which `u` holds before `t₁ ≤ t`. -/
theorem mem_T_before_add_delay_of_held_at {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched}
    (hdiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption) {GST : ℕ} {t : ℕ}
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (t + Δ S))
    (hParent : ParentHeldAtDelivery S Sched x)
    {t₁ : ℕ} {u w : V} {B : Block V}
    (ht₁t : t₁ ≤ t) (hGST : GST ≤ t)
    (hu : u ∉ Sched.adv ((x[stepBefore x t₁].time : ℕ) : Int))
    (hB : B ∈ (stateBefore x t₁ u).S.T)
    (hw : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ S →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    (hcompat : (stateBefore x (t + Δ S) w).S.F.compatible B = true) :
    B ∈ (stateBefore x (t + Δ S) w).S.T := by
  by_cases hg : B = Block.genesis
  · subst hg
    exact genesis_mem_T_of_exec S Sched x _ w
  rcases (compatible_iff _ _).1 hcompat with hFB | hBF
  swap
  · exact ancestors_mem_T_of_exec S Sched x _ w _ B
      (lem11_node_invariant S Sched x _ w).1.2.2.2.1 hBF
  obtain ⟨i, hi, hsend, hhon, hslot⟩ := tree_block_relayed x (k := stepBefore x t₁) hB hg
  have hhon' : u ∉ Sched.adv (x[i].time : Int) :=
    fun ha => hhon (hMono _ _ (by exact_mod_cast time_le_succ x i) ha)
  have hit : x[i + 1].time ≤ t :=
    le_trans (le_of_lt ((lt_stepBefore_iff x hdiv).1 hi)) ht₁t
  obtain ⟨d, hid, hl, hd⟩ := delivered_before_stepBefore_of_honest_send x hdiv hSync hCatch
    hMono (sm := ⟨u, NamedObject.block B⟩) ⟨hsend, hhon'⟩ trivial hit hGST hw
  obtain ⟨-, hwh, hstep⟩ := deliver_step_state x hl
  suffices h : B ∈ (x[d + 1][w].st).S.T from mem_T_mono x w hd h
  by_cases hheld : B ∈ (x[d][w].st).S.T
  · exact mem_T_mono x w (Nat.le_succ d) hheld
  rw [hstep]
  apply mem_T_receive_block
  right
  have hInvU := (lem11_node_invariant S Sched x (stepBefore x t₁) u).1
  obtain ⟨hparU, hwf, hprop, hps⟩ := hInvU.2.2.1.2 B hB hg
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
    have hdt : x[d].time ≤ t + Δ S :=
      le_of_lt (lt_of_le_of_lt (time_le_succ x d) ((lt_stepBefore_iff x hdiv).1 hd))
    have hBB : B' = B := hRoots B' B ⟨d, w, hwh, hdt, hB'⟩
      ⟨stepBefore x t₁, u, hu, by have := time_stepBefore_le x t₁; omega, hB⟩ hr
    exact hheld (hBB ▸ hB')
  · intro a ha
    have h1 := hInvU.2.2.2.2.2.2.1 B hB hg a ha
    rw [hInvU.2.2.2.2.2.1 B.parent hparU] at h1
    rw [hInvW.2.2.2.2.2.1 B.parent hpar]
    exact h1

/-! ## A held block's spreading -/

/-- **A held block reaches every honest awake validator within one delay, or is low.** From
`GST` on, with the execution assumptions and unforgeability: when `u`, honest at the time of the
configuration `stepBefore x t₁` (`t₁ ≤ t`), holds `D` before `t₁`, and `w` is awake and honest
from `t` to `t + Δ ≤ tEnd`, then before `t + Δ` either `w` holds `D` with its finalized block `D` or
an ancestor of `D`, or `D`'s chain-state height is at most `w`'s cache `h_j`.

Why: when `D` is higher than `w`'s `h_j`, `w`'s finalized block is an ancestor of `D`
(`F_ancestorEq_of_high_at`), so compatible with it, and the network delivers `D`
(`mem_T_before_add_delay_of_held_at`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tEnd`, `t₁`, `t`: the times;
  `u`: the holder; `w`: the receiver; `D`: the block.

Roots name blocks until `t + Δ S`: `F_ancestorEq_of_high_at` at `t + Δ` and `t₁ ≤ t`, and the
delivery by `t + Δ` (`mem_T_before_add_delay_of_held_at`). -/
theorem held_spread (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST tEnd t₁ t : ℕ) (u w : V) (D : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (t + Δ S))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int))
    (ht₁t : t₁ ≤ t) (hGST : GST ≤ t) (hEnd : t + Δ S ≤ tEnd)
    (hu : u ∉ Sched.adv ((x[stepBefore x t₁].time : ℕ) : Int))
    (hD : D ∈ (stateBefore x t₁ u).S.T)
    (hw : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ S →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int)) :
    (D ∈ (stateBefore x (t + Δ S) w).S.T ∧ (stateBefore x (t + Δ S) w).S.F.AncestorEq D) ∨
      (chainStateOf S.C D).h ≤ (stateBefore x (t + Δ S) w).S.h_j := by
  by_cases hlt : (stateBefore x (t + Δ S) w).S.h_j < (chainStateOf S.C D).h
  · have hwh := (hw (t + Δ S) (by omega) le_rfl).2
    have hFD := F_ancestorEq_of_high_at S Sched x hU hRoots tEnd (t + Δ S) t₁ w u D hThird hEnd
      (by omega) (honest_config x hMono hwh) hu hD hlt (max_le le_rfl (by omega))
    refine Or.inl ⟨?_, hFD⟩
    exact mem_T_before_add_delay_of_held_at hDiv hMono hSync hCatch hRoots hParent
      ht₁t hGST hu hD hw ((compatible_iff _ _).2 (Or.inl hFD))
  · exact Or.inr (Nat.le_of_not_lt hlt)

/-- **A held block's justification height reaches every honest awake validator's `h_j` within one
delay.** Under `held_spread`'s hypotheses, `D`'s justification height is at most `w`'s `h_j` before
`t + Δ`: when `w` holds `D` on its finalized block's chain, by the cache (Lemma 57); otherwise
`D`'s justification height is less than its height (Lemma 47), at most `w`'s `h_j`.

The variables: as in `held_spread`.

Roots name blocks until `t + Δ S`: `held_spread`. -/
theorem held_spread_h_j (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST tEnd t₁ t : ℕ) (u w : V) (D : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (t + Δ S))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int))
    (ht₁t : t₁ ≤ t) (hGST : GST ≤ t) (hEnd : t + Δ S ≤ tEnd)
    (hu : u ∉ Sched.adv ((x[stepBefore x t₁].time : ℕ) : Int))
    (hD : D ∈ (stateBefore x t₁ u).S.T)
    (hw : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ S →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int)) :
    (chainStateOf S.C D).h_j ≤ (stateBefore x (t + Δ S) w).S.h_j := by
  rcases held_spread S Sched x GST tEnd t₁ t u w D hDiv hMono hSync hCatch hRoots hParent
    hU hThird ht₁t hGST hEnd hu hD hw with ⟨hDw, hFD⟩ | hle
  · have h := h_j_of_mem_T_of_stateBefore S Sched x (t + Δ S) w D hDw hFD
    rw [σ_eq_of_stateBefore S Sched x (t + Δ S) w D hDw] at h
    exact h
  · have h47 := (lem47_chain_state_heights S.C D D).1.2.1
    unfold Height at *
    omega

/-- **A held block's height reaches every honest awake validator's `h_max` within one delay.**
Under `held_spread`'s hypotheses, `D`'s chain-state height is at most `w`'s `h_max` before
`t + Δ`: a held block is at most `h_max` (Lemma 46), and `h_j < h_max`.

The variables: as in `held_spread`.

Roots name blocks until `t + Δ S`: `held_spread`. -/
theorem held_spread_h_max (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST tEnd t₁ t : ℕ) (u w : V) (D : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (t + Δ S))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int))
    (ht₁t : t₁ ≤ t) (hGST : GST ≤ t) (hEnd : t + Δ S ≤ tEnd)
    (hu : u ∉ Sched.adv ((x[stepBefore x t₁].time : ℕ) : Int))
    (hD : D ∈ (stateBefore x t₁ u).S.T)
    (hw : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ S →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int)) :
    (chainStateOf S.C D).h ≤ (stateBefore x (t + Δ S) w).S.h_max := by
  rcases held_spread S Sched x GST tEnd t₁ t u w D hDiv hMono hSync hCatch hRoots hParent
    hU hThird ht₁t hGST hEnd hu hD hw with ⟨hDw, -⟩ | hle
  · exact height_le_h_max S Sched x (t + Δ S) w D hDw
  · have h := h_j_lt_h_max S Sched x (t + Δ S) w
    unfold Height at *
    omega

/-! ## A contested FG state -/

/-- **A contested state stays contested while its `h_max` stays.** Under unforgeability, roots
naming blocks, permanent corruption and fewer than a third of the validators in the adversary set
up to `tEnd`: when `w` is honest at `t` with `t₂ ≤ t ≤ tEnd`, its FG state before `t₂` is contested,
and its `h_max` before `t` is the one before `t₂`, then its FG state before `t` is contested.

Why: `h_j` does not decrease and stays less than `h_max`, so it stays; so does the justified block
(Lemma 76); the contesting block stays held, and the finalized block before `t` is an ancestor of it,
being higher than `h_j` (Lemma 89a).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tEnd`, `t₂ ≤ t`: the times; `w`: the
  validator.

Roots name blocks until `tR`, at least `t`: the proof compares blocks `w` holds before `t₂ ≤ t`
and before `t` (`h_j_mono`, Lemma 76, Lemma 89a). -/
theorem contest_persists (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) {tR : ℕ} (hRoots : RootsNameBlocksUntil S Sched x tR)
    (tEnd t₂ t : ℕ) (w : V)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int))
    (h2t : t₂ ≤ t) (ht : t ≤ tEnd) (hw : w ∉ Sched.adv (t : Int))
    (hc : fg_contest (stateBefore x t₂ w).S = true)
    (hm : (stateBefore x t w).S.h_max = (stateBefore x t₂ w).S.h_max)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : t ≤ tR) :
    fg_contest (stateBefore x t w).S = true := by
  obtain ⟨hm2, A, hA, hFA, hAh, hJA⟩ := fg_contest_spec _ hc
  have hw2 : w ∉ Sched.adv (t₂ : Int) := fun h => hw (hMono _ _ (by exact_mod_cast h2t) h)
  have hjm := h_j_mono S Sched x hDiv hMono hU hRoots tEnd t₂ t w hThird h2t ht hw htR
  have hjl := h_j_lt_h_max S Sched x t w
  have hjeq : (stateBefore x t w).S.h_j = (stateBefore x t₂ w).S.h_j := by
    unfold Height at *
    omega
  have hJ := J_eq_of_h_j_eq S Sched x hMono hU hRoots tEnd t t₂ w w hThird ht (le_trans h2t ht)
    hw hw2 hjeq (max_le htR (by omega))
  have hAt : A ∈ (stateBefore x t w).S.T := (stateBefore_grows x hDiv w h2t).1 hA
  rw [σ_eq_of_stateBefore S Sched x t₂ w A hA] at hAh
  have hFA' := F_ancestorEq_of_high S Sched x hMono hU hRoots tEnd t t₂ w w A hThird ht
    (le_trans h2t ht) hw hw2 hA (by rw [hAh, hm2, hjeq]; exact Nat.lt_succ_self _)
    (max_le htR (by omega))
  refine fg_contest_true_of _ A (by rw [hm, hm2, hjeq]) hAt hFA' ?_ ?_
  · rw [σ_eq_of_stateBefore S Sched x t w A hAt, hAh, hm]
  · rw [hJ]
    exact hJA

/-! ## The first time of a kind of change -/

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- **A level reached within one delay of its first holder is crossed only then.** For a
predicate `Lv w t` on validators and times (a level of `w`'s state before `t`): when a validator
`u` honest at a time `τ ≥ T₁` with `Lv u (τ + 1)` makes every validator `w` honest at a time
`t ≥ τ + 1 + d` before `a` satisfy `Lv w (τ + 1 + d)` (`hspread`), and the level, once reached
from `T₁ + d` on, stays reached up to a time before `a` at which `w` is honest (`hmono`), then
there is a time `τ` such that every crossing of the level (`¬ Lv w t`, `Lv w (t + 1)`) at a
validator honest at `t`, with `T₁ + d ≤ t < a`, is at a time from `τ` to `τ + d`.

Why: `τ` is the least time from `T₁` at which some validator honest then has the level right
after (`Nat.find`); a crossing later than `τ + d` would find the level reached already.

The variables:
- `Sched`: the schedule; `Lv`: the level; `T₁`, `d`, `a`: the times. -/
theorem kind_time (Sched : Schedule V) (Lv : V → ℕ → Prop) (T₁ d a : ℕ)
    (hspread : ∀ (τ : ℕ) (u w : V) (t : ℕ), T₁ ≤ τ → u ∉ Sched.adv (τ : Int) →
      Lv u (τ + 1) → τ + 1 + d ≤ t → t < a → w ∉ Sched.adv (t : Int) → Lv w (τ + 1 + d))
    (hmono : ∀ (w : V) (t₂ t : ℕ), T₁ + d ≤ t₂ → t₂ ≤ t → t < a → w ∉ Sched.adv (t : Int) →
      Lv w t₂ → Lv w t) :
    ∃ τ : ℕ, ∀ (w : V) (t : ℕ), T₁ + d ≤ t → t < a → w ∉ Sched.adv (t : Int) →
      ¬ Lv w t → Lv w (t + 1) → τ ≤ t ∧ t ≤ τ + d := by
  classical
  by_cases hex : ∃ τ : ℕ, T₁ ≤ τ ∧ ∃ u : V, u ∉ Sched.adv (τ : Int) ∧ Lv u (τ + 1)
  · refine ⟨Nat.find hex, ?_⟩
    intro w t ht1 hta hw hn hy
    have hle : Nat.find hex ≤ t := Nat.find_min' hex ⟨by omega, w, hw, hy⟩
    refine ⟨hle, ?_⟩
    by_contra hgt
    obtain ⟨hT, u, hu, hL⟩ := Nat.find_spec hex
    have hsp := hspread (Nat.find hex) u w t hT hu hL (by omega) hta hw
    exact hn (hmono w (Nat.find hex + 1 + d) t (by omega) (by omega) hta hw hsp)
  · refine ⟨0, ?_⟩
    intro w t ht1 _ hw _ hy
    exact absurd ⟨t, by omega, w, hw, hy⟩ hex

/-! ## The climb's context -/

/-- `ClimbCtx S Sched x GST tGAT tAwakeEnd T₁ r H₂`: the hypotheses of `fork_choice_change_kinds`
that its proof reads: the execution assumptions, unforgeability, every validator honest in the
phase awake then, fewer than a third in the adversary set up to its end, the threshold `H₂` at `T₁`
and every honest attestation before `aR S r` at most `H₂`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round; `H₂`: the threshold.

Roots name blocks until `aR S r`: every reader of the bundle compares blocks held before times at
most `aR S r`, the end of the climb. -/
structure ClimbCtx (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST tGAT tAwakeEnd T₁ r H₂ : ℕ) : Prop where
  hDiv : TimeDiverges x.toTrace
  hMono : Sched.MonotoneCorruption
  hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject
  hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject
  hRoots : RootsNameBlocksUntil S Sched x (aR S r)
  hParent : ParentHeldAtDelivery S Sched x
  hU : Unforgeability Vocab.goldilocks Sched x.toTrace
  hGST : GST ≤ tGAT
  hT₁ : tGAT ≤ T₁
  hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int)
  hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
    ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int)
  hH₂ : OldHeightAttained S Sched x T₁ H₂
  hOld : OldAttestationsAtMost S Sched x (aR S r) H₂
  hEnd : aR S r ≤ tAwakeEnd

namespace ClimbCtx

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd T₁ r H₂ : ℕ}

/-- B2 in the context: from `T₁ + Δ` to `aR S r`, an honest `h_max` is `H₂` or `H₂ + 1`. -/
theorem bounds (C : ClimbCtx S Sched x GST tGAT tAwakeEnd T₁ r H₂) {t : ℕ} {w : V}
    (h1 : T₁ + Δ S ≤ t) (h2 : t ≤ aR S r) (hw : w ∉ Sched.adv (t : Int)) :
    H₂ ≤ (stateBefore x t w).S.h_max ∧ (stateBefore x t w).S.h_max ≤ H₂ + 1 :=
  honest_h_max_bounds S Sched x GST tGAT tAwakeEnd T₁ r H₂ t w C.hDiv C.hMono C.hSync C.hCatch
    (C.hRoots.mono h2) C.hParent C.hU C.hGST C.hT₁ C.hThird C.hAwake C.hH₂ C.hOld C.hEnd
    h1 h2 hw

/-- Before `aR S r`, every `h_max` is at most `H₂ + 1` (A2). -/
theorem hmax_le (C : ClimbCtx S Sched x GST tGAT tAwakeEnd T₁ r H₂) {t : ℕ} (w : V)
    (h2 : t ≤ aR S r) : (stateBefore x t w).S.h_max ≤ H₂ + 1 := by
  obtain ⟨-, ⟨X, hX, hXh⟩, -⟩ := cachesWitnessed_of_stateBefore S Sched x t w
  rw [← hXh]
  exact held_height_le_before_action S Sched x tAwakeEnd r H₂ t w X C.hU C.hThird C.hOld h2
    C.hEnd hX

/-- A validator honest at `t ≤ tAwakeEnd` is awake and honest at every time of the phase up to
`t`. -/
theorem awakeHonest (C : ClimbCtx S Sched x GST tGAT tAwakeEnd T₁ r H₂) {w : V} {t : ℕ}
    (hw : w ∉ Sched.adv (t : Int)) (ht : t ≤ tAwakeEnd) :
    ∀ t' : ℕ, tGAT ≤ t' → t' ≤ t → w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int) := by
  intro t' h1 h2
  have hw' : w ∉ Sched.adv (t' : Int) := fun h => hw (C.hMono _ _ (by exact_mod_cast h2) h)
  exact ⟨C.hAwake t' h1 (le_trans h2 ht) w hw', hw'⟩

/-- `held_spread` in the context: a block that `u`, honest at `τ ≥ T₁`, holds before `τ + 1`
reaches `w`, honest at `t ≥ τ + 1 + Δ` before `aR S r`, by `τ + 1 + Δ`, or is at most its `h_j`. -/
theorem spread (C : ClimbCtx S Sched x GST tGAT tAwakeEnd T₁ r H₂) {τ t : ℕ} {u w : V}
    {D : Block V} (hT : T₁ ≤ τ) (hu : u ∉ Sched.adv (τ : Int))
    (hD : D ∈ (stateBefore x (τ + 1) u).S.T) (ht : τ + 1 + Δ S ≤ t) (hta : t < aR S r)
    (hw : w ∉ Sched.adv (t : Int)) :
    (D ∈ (stateBefore x (τ + 1 + Δ S) w).S.T ∧
        (stateBefore x (τ + 1 + Δ S) w).S.F.AncestorEq D) ∨
      (chainStateOf S.C D).h ≤ (stateBefore x (τ + 1 + Δ S) w).S.h_j :=
  held_spread S Sched x GST tAwakeEnd (τ + 1) (τ + 1) u w D C.hDiv C.hMono C.hSync C.hCatch
    (C.hRoots.mono (by omega)) C.hParent C.hU C.hThird le_rfl
    (by have := C.hGST; have := C.hT₁; omega)
    (by have := C.hEnd; omega) (honest_config_succ x C.hDiv hu) hD
    (fun t' h1 h2 => C.awakeHonest hw (by have := C.hEnd; omega) t'
      (by have := C.hT₁; omega) (by omega))

/-- `held_spread_h_j` in the context. -/
theorem spread_h_j (C : ClimbCtx S Sched x GST tGAT tAwakeEnd T₁ r H₂) {τ t : ℕ} {u w : V}
    {D : Block V} (hT : T₁ ≤ τ) (hu : u ∉ Sched.adv (τ : Int))
    (hD : D ∈ (stateBefore x (τ + 1) u).S.T) (ht : τ + 1 + Δ S ≤ t) (hta : t < aR S r)
    (hw : w ∉ Sched.adv (t : Int)) :
    (chainStateOf S.C D).h_j ≤ (stateBefore x (τ + 1 + Δ S) w).S.h_j :=
  held_spread_h_j S Sched x GST tAwakeEnd (τ + 1) (τ + 1) u w D C.hDiv C.hMono C.hSync C.hCatch
    (C.hRoots.mono (by omega)) C.hParent C.hU C.hThird le_rfl
    (by have := C.hGST; have := C.hT₁; omega)
    (by have := C.hEnd; omega) (honest_config_succ x C.hDiv hu) hD
    (fun t' h1 h2 => C.awakeHonest hw (by have := C.hEnd; omega) t'
      (by have := C.hT₁; omega) (by omega))

/-- `held_spread_h_max` in the context. -/
theorem spread_h_max (C : ClimbCtx S Sched x GST tGAT tAwakeEnd T₁ r H₂) {τ t : ℕ} {u w : V}
    {D : Block V} (hT : T₁ ≤ τ) (hu : u ∉ Sched.adv (τ : Int))
    (hD : D ∈ (stateBefore x (τ + 1) u).S.T) (ht : τ + 1 + Δ S ≤ t) (hta : t < aR S r)
    (hw : w ∉ Sched.adv (t : Int)) :
    (chainStateOf S.C D).h ≤ (stateBefore x (τ + 1 + Δ S) w).S.h_max :=
  held_spread_h_max S Sched x GST tAwakeEnd (τ + 1) (τ + 1) u w D C.hDiv C.hMono C.hSync C.hCatch
    (C.hRoots.mono (by omega)) C.hParent C.hU C.hThird le_rfl
    (by have := C.hGST; have := C.hT₁; omega)
    (by have := C.hEnd; omega) (honest_config_succ x C.hDiv hu) hD
    (fun t' h1 h2 => C.awakeHonest hw (by have := C.hEnd; omega) t'
      (by have := C.hT₁; omega) (by omega))

/-! ## The four levels: their spreading and their persistence -/

/-- The level `j ≤ h_j` spreads: when `u`, honest at `τ ≥ T₁`, has `h_j ≥ j` before `τ + 1`, every
`w` honest at `t ≥ τ + 1 + Δ` before `aR S r` has `h_j ≥ j` before `τ + 1 + Δ` (the block
witnessing `u`'s cache, `held_spread_h_j`). -/
theorem spread_level_h_j (C : ClimbCtx S Sched x GST tGAT tAwakeEnd T₁ r H₂) (j : ℕ) {τ t : ℕ}
    {u w : V} (hT : T₁ ≤ τ) (hu : u ∉ Sched.adv (τ : Int))
    (hL : j ≤ (stateBefore x (τ + 1) u).S.h_j) (ht : τ + 1 + Δ S ≤ t) (hta : t < aR S r)
    (hw : w ∉ Sched.adv (t : Int)) :
    j ≤ (stateBefore x (τ + 1 + Δ S) w).S.h_j := by
  obtain ⟨⟨D, hD, -, hj⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x (τ + 1) u
  have h := C.spread_h_j hT hu hD ht hta hw
  rw [hj] at hL
  exact le_trans hL h

/-- The level `H₂ ≤ head_height_floor` spreads: when `u`, honest at `τ ≥ T₁`, has
`head_height_floor ≥ H₂` before `τ + 1`, so does every `w` honest at `t ≥ τ + 1 + Δ` before
`aR S r`, before `τ + 1 + Δ`.

Why: either `u`'s `h_max` is at least `H₂ + 1`, and its witness raises `w`'s; or `u` is contested
at `h_max = H₂`, `h_j = H₂ − 1`, and its contesting block and its justified block's witness reach
`w`, whose state is then contested at `H₂` too, or has `h_max = H₂ + 1`. -/
theorem spread_level_floor (C : ClimbCtx S Sched x GST tGAT tAwakeEnd T₁ r H₂) {τ t : ℕ}
    {u w : V} (hT : T₁ ≤ τ) (hu : u ∉ Sched.adv (τ : Int))
    (hL : H₂ ≤ head_height_floor (stateBefore x (τ + 1) u).S) (ht : τ + 1 + Δ S ≤ t)
    (hta : t < aR S r) (hw : w ∉ Sched.adv (t : Int)) :
    H₂ ≤ head_height_floor (stateBefore x (τ + 1 + Δ S) w).S := by
  have hfw := h_max_sub_one_le_floor (stateBefore x (τ + 1 + Δ S) w).S
  by_cases hX : H₂ + 1 ≤ (stateBefore x (τ + 1) u).S.h_max
  · obtain ⟨-, ⟨X, hX', hXh⟩, -⟩ := cachesWitnessed_of_stateBefore S Sched x (τ + 1) u
    have h := C.spread_h_max hT hu hX' ht hta hw
    unfold Height at *
    omega
  rcases Nat.eq_zero_or_pos H₂ with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  have hwt : w ∉ Sched.adv ((τ + 1 + Δ S : ℕ) : Int) :=
    fun h => hw (C.hMono _ _ (by exact_mod_cast ht) h)
  rcases floor_cases (stateBefore x (τ + 1) u).S with ⟨hc, hm, hfl⟩ | ⟨-, hfl⟩
  swap
  · exfalso
    rw [hfl] at hL
    unfold Height at *
    omega
  obtain ⟨-, A, hA, -, hAh, hJA⟩ := fg_contest_spec _ hc
  rw [σ_eq_of_stateBefore S Sched x (τ + 1) u A hA] at hAh
  obtain ⟨⟨D, hD, hJD, hjD⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x (τ + 1) u
  have hjw := C.spread_h_j hT hu hD ht hta hw
  rw [← hjD] at hjw
  by_cases hY : H₂ + 1 ≤ (stateBefore x (τ + 1 + Δ S) w).S.h_max
  · unfold Height at *
    omega
  have hb := C.bounds (t := τ + 1 + Δ S) (w := w) (by omega) (by omega) hwt
  have hjl := h_j_lt_h_max S Sched x (τ + 1 + Δ S) w
  rw [hfl] at hL
  have hmu : (stateBefore x (τ + 1) u).S.h_max = H₂ := by
    unfold Height at *
    omega
  have hjeq : (stateBefore x (τ + 1 + Δ S) w).S.h_j = (stateBefore x (τ + 1) u).S.h_j := by
    unfold Height at *
    omega
  have hmw : (stateBefore x (τ + 1 + Δ S) w).S.h_max =
      (stateBefore x (τ + 1 + Δ S) w).S.h_j + 1 := by
    unfold Height at *
    omega
  rcases C.spread hT hu hA ht hta hw with ⟨hAw, hFA⟩ | hlo
  swap
  · exfalso
    unfold Height at *
    omega
  have hJ := J_eq_of_h_j_eq_at S Sched x C.hU C.hRoots tAwakeEnd (τ + 1 + Δ S) (τ + 1) w u
    C.hThird (by have := C.hEnd; omega) (by have := C.hEnd; omega) (honest_config x C.hMono hwt)
    (honest_config_succ x C.hDiv hu) hjeq (max_le (by omega) (by omega))
  have hcw : fg_contest (stateBefore x (τ + 1 + Δ S) w).S = true := by
    refine fg_contest_true_of _ A hmw hAw hFA ?_ ?_
    · rw [σ_eq_of_stateBefore S Sched x (τ + 1 + Δ S) w A hAw, hAh]
      unfold Height at *
      omega
    · rw [hJ]
      exact hJA
  rcases floor_cases (stateBefore x (τ + 1 + Δ S) w).S with ⟨-, -, hflw⟩ | ⟨hcf, -⟩
  · rw [hflw]
    unfold Height at *
    omega
  · rw [hcw] at hcf
    cases hcf

/-- The level `H₂ + 1 ≤ head_height_floor` spreads: when `u`, honest at `τ ≥ T₁`, has
`head_height_floor ≥ H₂ + 1` before `τ + 1`, so does every `w` honest at `t ≥ τ + 1 + Δ` before
`aR S r`, before `τ + 1 + Δ`.

Why: `u` is then contested at `h_max = H₂ + 1`, `h_j = H₂` (A2 bounds `h_max`); its contesting block
and its justified block's witness reach `w`, whose state is then contested at `H₂ + 1`. -/
theorem spread_level_floor_succ (C : ClimbCtx S Sched x GST tGAT tAwakeEnd T₁ r H₂) {τ t : ℕ}
    {u w : V} (hT : T₁ ≤ τ) (hu : u ∉ Sched.adv (τ : Int))
    (hL : H₂ + 1 ≤ head_height_floor (stateBefore x (τ + 1) u).S) (ht : τ + 1 + Δ S ≤ t)
    (hta : t < aR S r) (hw : w ∉ Sched.adv (t : Int)) :
    H₂ + 1 ≤ head_height_floor (stateBefore x (τ + 1 + Δ S) w).S := by
  have hwt : w ∉ Sched.adv ((τ + 1 + Δ S : ℕ) : Int) :=
    fun h => hw (C.hMono _ _ (by exact_mod_cast ht) h)
  have hmu := C.hmax_le u (t := τ + 1) (by omega)
  have hflu := floor_le_h_max (stateBefore x (τ + 1) u).S
  rcases floor_cases (stateBefore x (τ + 1) u).S with ⟨hc, hm, hfl⟩ | ⟨-, hfl⟩
  swap
  · exfalso
    rw [hfl] at hL
    unfold Height at *
    omega
  obtain ⟨-, A, hA, -, hAh, hJA⟩ := fg_contest_spec _ hc
  rw [σ_eq_of_stateBefore S Sched x (τ + 1) u A hA] at hAh
  obtain ⟨⟨D, hD, hJD, hjD⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x (τ + 1) u
  have hjw := C.spread_h_j hT hu hD ht hta hw
  rw [← hjD] at hjw
  have hmw := C.hmax_le w (t := τ + 1 + Δ S) (by omega)
  have hjl := h_j_lt_h_max S Sched x (τ + 1 + Δ S) w
  rw [hfl] at hL
  have hjeq : (stateBefore x (τ + 1 + Δ S) w).S.h_j = (stateBefore x (τ + 1) u).S.h_j := by
    unfold Height at *
    omega
  have hmw' : (stateBefore x (τ + 1 + Δ S) w).S.h_max =
      (stateBefore x (τ + 1 + Δ S) w).S.h_j + 1 := by
    unfold Height at *
    omega
  rcases C.spread hT hu hA ht hta hw with ⟨hAw, hFA⟩ | hlo
  swap
  · exfalso
    unfold Height at *
    omega
  have hJ := J_eq_of_h_j_eq_at S Sched x C.hU C.hRoots tAwakeEnd (τ + 1 + Δ S) (τ + 1) w u
    C.hThird (by have := C.hEnd; omega) (by have := C.hEnd; omega) (honest_config x C.hMono hwt)
    (honest_config_succ x C.hDiv hu) hjeq (max_le (by omega) (by omega))
  have hcw : fg_contest (stateBefore x (τ + 1 + Δ S) w).S = true := by
    refine fg_contest_true_of _ A hmw' hAw hFA ?_ ?_
    · rw [σ_eq_of_stateBefore S Sched x (τ + 1 + Δ S) w A hAw, hAh]
      unfold Height at *
      omega
    · rw [hJ]
      exact hJA
  rcases floor_cases (stateBefore x (τ + 1 + Δ S) w).S with ⟨-, -, hflw⟩ | ⟨hcf, -⟩
  · rw [hflw]
    unfold Height at *
    omega
  · rw [hcw] at hcf
    cases hcf

/-- The level `H₂ ≤ head_height_floor` persists: reached before `t₂ ≥ T₁ + Δ`, it holds before
every `t ≥ t₂` before `aR S r` at which `w` is honest (`contest_persists` when `h_max` stays `H₂`). -/
theorem mono_level_floor (C : ClimbCtx S Sched x GST tGAT tAwakeEnd T₁ r H₂) {w : V} {t₂ t : ℕ}
    (h1 : T₁ + Δ S ≤ t₂) (h2t : t₂ ≤ t) (hta : t < aR S r) (hw : w ∉ Sched.adv (t : Int))
    (hL : H₂ ≤ head_height_floor (stateBefore x t₂ w).S) :
    H₂ ≤ head_height_floor (stateBefore x t w).S := by
  have hft := h_max_sub_one_le_floor (stateBefore x t w).S
  by_cases hX : H₂ + 1 ≤ (stateBefore x t w).S.h_max
  · unfold Height at *
    omega
  rcases Nat.eq_zero_or_pos H₂ with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  have hw2 : w ∉ Sched.adv (t₂ : Int) := fun h => hw (C.hMono _ _ (by exact_mod_cast h2t) h)
  have hb2 := C.bounds (t := t₂) (w := w) h1 (by omega) hw2
  have hmm := h_max_mono S Sched x C.hDiv w h2t
  rcases floor_cases (stateBefore x t₂ w).S with ⟨hc, -, hfl⟩ | ⟨-, hfl⟩
  swap
  · exfalso
    rw [hfl] at hL
    unfold Height at *
    omega
  have hmeq : (stateBefore x t w).S.h_max = (stateBefore x t₂ w).S.h_max := by
    unfold Height at *
    omega
  have hct := contest_persists S Sched x C.hDiv C.hMono C.hU C.hRoots tAwakeEnd t₂ t w C.hThird
    h2t (by have := C.hEnd; omega) hw hc hmeq (by omega)
  rcases floor_cases (stateBefore x t w).S with ⟨-, -, hflt⟩ | ⟨hcf, -⟩
  · rw [hflt, hmeq, ← hfl]
    exact hL
  · rw [hct] at hcf
    cases hcf

/-- The level `H₂ + 1 ≤ head_height_floor` persists: reached before `t₂`, it holds before every
`t ≥ t₂` before `aR S r` at which `w` is honest (`contest_persists`, `h_max` staying `H₂ + 1`). -/
theorem mono_level_floor_succ (C : ClimbCtx S Sched x GST tGAT tAwakeEnd T₁ r H₂) {w : V}
    {t₂ t : ℕ} (h2t : t₂ ≤ t) (hta : t < aR S r) (hw : w ∉ Sched.adv (t : Int))
    (hL : H₂ + 1 ≤ head_height_floor (stateBefore x t₂ w).S) :
    H₂ + 1 ≤ head_height_floor (stateBefore x t w).S := by
  have hmm := h_max_mono S Sched x C.hDiv w h2t
  have hm2 := C.hmax_le w (t := t₂) (by omega)
  have hmt := C.hmax_le w (t := t) (by omega)
  have hfl2 := floor_le_h_max (stateBefore x t₂ w).S
  rcases floor_cases (stateBefore x t₂ w).S with ⟨hc, -, hfl⟩ | ⟨-, hfl⟩
  swap
  · exfalso
    rw [hfl] at hL
    unfold Height at *
    omega
  have hmeq : (stateBefore x t w).S.h_max = (stateBefore x t₂ w).S.h_max := by
    unfold Height at *
    omega
  have hct := contest_persists S Sched x C.hDiv C.hMono C.hU C.hRoots tAwakeEnd t₂ t w C.hThird
    h2t (by have := C.hEnd; omega) hw hc hmeq (by omega)
  rcases floor_cases (stateBefore x t w).S with ⟨-, -, hflt⟩ | ⟨hcf, -⟩
  · rw [hflt, hmeq, ← hfl]
    exact hL
  · rw [hct] at hcf
    cases hcf

/-! ## Every fork-choice change crosses one of the four levels -/

/-- **A fork-choice change of the climb crosses one of four levels.** At a time `t` from
`T₁ + Δ` to before `aR S r`, a `ForkChoiceChangeAt` at a validator honest at `t` crosses one of the
levels `H₂ − 1 ≤ h_j`, `H₂ ≤ head_height_floor`, `H₂ ≤ h_j`, `H₂ + 1 ≤ head_height_floor`: the
level fails before `t` and holds before `t + 1`.

Why: with `h_max` at `H₂` or `H₂ + 1` (B2, A2), a rise of `head_height_floor` (which is `h_max` or
`h_max − 1`) is to `H₂` from `H₂ − 1`, or to `H₂ + 1`. A root that becomes the justified block `J`
with `h_max = h_j + 1` and is no ancestor of the old root comes with a rise of `h_j` to `H₂ − 1` or
`H₂`: were `h_j` unchanged, `J` would be too (Lemma 76) and `h_max` as well, and the old root,
the finalized block of a contested state (the old `J` itself otherwise), would leave the new state
contested by the same block (Lemma 89a), against its root being `J`. -/
theorem classify (C : ClimbCtx S Sched x GST tGAT tAwakeEnd T₁ r H₂) {w : V} {t : ℕ}
    (h1 : T₁ + Δ S ≤ t) (hta : t < aR S r) (hw : w ∉ Sched.adv (t : Int))
    (hch : ForkChoiceChangeAt S Sched x w t) :
    (¬ H₂ - 1 ≤ (stateBefore x t w).S.h_j ∧ H₂ - 1 ≤ (stateBefore x (t + 1) w).S.h_j) ∨
    (¬ H₂ ≤ head_height_floor (stateBefore x t w).S ∧
      H₂ ≤ head_height_floor (stateBefore x (t + 1) w).S) ∨
    (¬ H₂ ≤ (stateBefore x t w).S.h_j ∧ H₂ ≤ (stateBefore x (t + 1) w).S.h_j) ∨
    (¬ H₂ + 1 ≤ head_height_floor (stateBefore x t w).S ∧
      H₂ + 1 ≤ head_height_floor (stateBefore x (t + 1) w).S) := by
  have hb0 := C.bounds (t := t) (w := w) h1 (by omega) hw
  have hmm := h_max_mono S Sched x C.hDiv w (show t ≤ t + 1 by omega)
  have hb1 := C.hmax_le w (t := t + 1) (by omega)
  have hE := C.hEnd
  rcases hch with ⟨hr1, hm1, hnot⟩ | hfl
  · have hlt : (stateBefore x t w).S.h_j < (stateBefore x (t + 1) w).S.h_j := by
      by_contra hge
      push Not at hge
      have hj0 := h_j_lt_h_max S Sched x t w
      have heq : (stateBefore x t w).S.h_j = (stateBefore x (t + 1) w).S.h_j := by
        unfold Height at *
        omega
      have hmeq : (stateBefore x t w).S.h_max = (stateBefore x (t + 1) w).S.h_max := by
        unfold Height at *
        omega
      have hJ := J_eq_of_h_j_eq_at S Sched x C.hU C.hRoots tAwakeEnd t (t + 1) w w C.hThird
        (by omega) (by omega) (honest_config x C.hMono hw) (honest_config_succ x C.hDiv hw) heq
        (max_le (by omega) (by omega))
      have hc1 : fg_contest (stateBefore x (t + 1) w).S = false := by
        rcases root_cases (stateBefore x (t + 1) w).S with ⟨-, -, h⟩ | ⟨hF, hor⟩
        · exact h
        · exfalso
          rcases hor with hc | hne
          · obtain ⟨-, B, -, hFB, -, hJB⟩ := fg_contest_spec _ hc
            exact hJB (by rw [← hr1, hF]; exact hFB)
          · exact hne hm1
      rcases root_cases (stateBefore x t w).S with ⟨hr0, -, -⟩ | ⟨-, hor0⟩
      · apply hnot
        rw [hr1, hr0, ← hJ]
        exact ancestorEq_refl _
      · rcases hor0 with hc0 | hne0
        · obtain ⟨-, A, hA, -, hAh, hJA⟩ := fg_contest_spec _ hc0
          have hAt := (stateBefore_grows x C.hDiv w (Nat.le_succ t)).1 hA
          rw [σ_eq_of_stateBefore S Sched x t w A hA] at hAh
          have hFA := F_ancestorEq_of_high_at S Sched x C.hU C.hRoots tAwakeEnd (t + 1) t w w A
            C.hThird (by omega) (by omega) (honest_config_succ x C.hDiv hw)
            (honest_config x C.hMono hw) hA (by rw [hAh, hmeq, hm1]; exact Nat.lt_succ_self _)
            (max_le (by omega) (by omega))
          have hct := fg_contest_true_of _ A hm1 hAt hFA
            (by rw [σ_eq_of_stateBefore S Sched x (t + 1) w A hAt, hAh, hmeq])
            (by rw [← hJ]; exact hJA)
          rw [hc1] at hct
          cases hct
        · apply hne0
          unfold Height at *
          omega
    by_cases hjv : (stateBefore x (t + 1) w).S.h_j + 1 = H₂
    · left
      unfold Height at *
      exact ⟨by omega, by omega⟩
    · right; right; left
      unfold Height at *
      exact ⟨by omega, by omega⟩
  · have hf0 := h_max_sub_one_le_floor (stateBefore x t w).S
    have hf1 := floor_le_h_max (stateBefore x (t + 1) w).S
    by_cases hf : head_height_floor (stateBefore x (t + 1) w).S = H₂ + 1
    · right; right; right
      unfold Height at *
      exact ⟨by omega, by omega⟩
    · right; left
      unfold Height at *
      exact ⟨by omega, by omega⟩

end ClimbCtx

/-! ## The four kinds of fork-choice change -/

/-- **The four kinds of fork-choice change.** The
proof; the audited statement is in `Statements/Executions/Lemma89Statements.lean`.

The route: every fork-choice change crosses one of four levels (`ClimbCtx.classify`); each level
reached by an honest validator reaches every honest validator within one delay (`spread_level_…`)
and stays reached (`mono_level_…`, `h_j_mono`), so its crossings lie within one delay after the
first time from `T₁` some honest validator has it (`kind_time`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round; `H₂`: the threshold.

Roots name blocks until `aR S r`: every change the conclusion classifies is at a time before
`aR S r`, and the levels are read before times at most `aR S r` (the bundle `ClimbCtx`). -/
theorem fork_choice_change_kinds (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd T₁ r H₂ : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (aR S r))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT) (hT₁ : tGAT ≤ T₁)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hH₂ : OldHeightAttained S Sched x T₁ H₂)
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hEnd : aR S r ≤ tAwakeEnd) :
    ∃ τ : Fin 4 → ℕ, ∀ (w : V) (t : ℕ), T₁ + Δ S ≤ t → t < aR S r →
      w ∉ Sched.adv (t : Int) → ForkChoiceChangeAt S Sched x w t →
      ∃ c : Fin 4, τ c ≤ t ∧ t ≤ τ c + Δ S := by
  have C : ClimbCtx S Sched x GST tGAT tAwakeEnd T₁ r H₂ :=
    ⟨hDiv, hMono, hSync, hCatch, hRoots, hParent, hU, hGST, hT₁, hThird, hAwake, hH₂,
      hOld, hEnd⟩
  have hjmono : ∀ j : ℕ, ∀ (w : V) (t₂ t : ℕ), T₁ + Δ S ≤ t₂ → t₂ ≤ t → t < aR S r →
      w ∉ Sched.adv (t : Int) → j ≤ (stateBefore x t₂ w).S.h_j →
      j ≤ (stateBefore x t w).S.h_j := fun j w t₂ t _ h2t hta hw hL =>
    le_trans hL (h_j_mono S Sched x hDiv hMono hU hRoots tAwakeEnd t₂ t w hThird h2t
      (by omega) hw (by omega))
  obtain ⟨τ0, h0⟩ := kind_time Sched (fun w t => H₂ - 1 ≤ (stateBefore x t w).S.h_j) T₁ (Δ S)
    (aR S r) (fun τ u w t hT hu hL ht hta hw => C.spread_level_h_j (H₂ - 1) hT hu hL ht hta hw)
    (hjmono (H₂ - 1))
  obtain ⟨τ1, h1⟩ := kind_time Sched (fun w t => H₂ ≤ head_height_floor (stateBefore x t w).S) T₁
    (Δ S) (aR S r) (fun τ u w t hT hu hL ht hta hw => C.spread_level_floor hT hu hL ht hta hw)
    (fun w t₂ t h1 h2t hta hw hL => C.mono_level_floor h1 h2t hta hw hL)
  obtain ⟨τ2, h2⟩ := kind_time Sched (fun w t => H₂ ≤ (stateBefore x t w).S.h_j) T₁ (Δ S)
    (aR S r) (fun τ u w t hT hu hL ht hta hw => C.spread_level_h_j H₂ hT hu hL ht hta hw)
    (hjmono H₂)
  obtain ⟨τ3, h3⟩ := kind_time Sched
    (fun w t => H₂ + 1 ≤ head_height_floor (stateBefore x t w).S) T₁ (Δ S) (aR S r)
    (fun τ u w t hT hu hL ht hta hw => C.spread_level_floor_succ hT hu hL ht hta hw)
    (fun w t₂ t _ h2t hta hw hL => C.mono_level_floor_succ h2t hta hw hL)
  refine ⟨fun c => if c.val = 0 then τ0 else if c.val = 1 then τ1 else if c.val = 2 then τ2
    else τ3, ?_⟩
  intro w t ht1 hta hw hch
  rcases C.classify ht1 hta hw hch with ⟨hn, hy⟩ | ⟨hn, hy⟩ | ⟨hn, hy⟩ | ⟨hn, hy⟩
  · exact ⟨0, h0 w t ht1 hta hw hn hy⟩
  · exact ⟨1, h1 w t ht1 hta hw hn hy⟩
  · exact ⟨2, h2 w t ht1 hta hw hn hy⟩
  · exact ⟨3, h3 w t ht1 hta hw hn hy⟩

end GoldilocksCorrectness.Proofs.Executions
