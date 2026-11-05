module
public import GoldilocksCorrectness.Proofs.Executions.Lemma89CountJ
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma89ClimbUpTo
public import GoldilocksCorrectness.Proofs.Executions.NetworkUpTo

@[expose] public section

/-!
# `Lemma89CountJ.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89CountJ.lean` that name a delivery
premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the deadlines
. The bound of each twin
is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in the twin's
own parameters.

* `mem_T_before_add_delay_of_held_at`, `held_spread`, `held_spread_h_j`, `held_spread_h_max`,
  `ClimbCtx`, `bounds`, `hmax_le`, `awakeHonest`, `spread`, `spread_h_j`, `spread_h_max`,
  `spread_level_h_j`, `spread_level_floor`, `spread_level_floor_succ`, `mono_level_floor`,
  `mono_level_floor_succ`, `classify`, `fork_choice_change_kinds`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
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

/-- `mem_T_before_add_delay_of_held` with the holder `u` honest at the time of the configuration
`stepBefore x t₁` its tree is read from, rather than at `t₁`. The proof is the landed one; the
holder's honesty is read only there (the sender's honesty at its own send comes with the send).

The variables:
- `x`: the execution; `GST`: the time from which the network is synchronous; `t₁ ≤ t`: the two
  times; `u`: the holder; `w`: the receiver; `B`: the block.

Roots name blocks until `t + Δ S`: the proof compares the block `w` holds at the delivery, a step
at a time before `t + Δ S`, with `B`, which `u` holds before `t₁ ≤ t`.

Restated with the delivery premises up to `t + Δ S`: the bound of its roots `hRoots`, the deadline of the one delivery its proof reads. -/
theorem mem_T_before_add_delay_of_held_at_upTo {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched}
    (hdiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption) {GST : ℕ} {t : ℕ}
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (t + Δ S))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (t + Δ S))
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
  obtain ⟨d, hid, hl, hd⟩ := delivered_before_stepBefore_of_honest_send_upTo x hdiv hSync hCatch
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
delivery by `t + Δ` (`mem_T_before_add_delay_of_held_at`).

Restated with the delivery premises up to `t + Δ S`: the bound of its roots `hRoots`, the deadline of the one delivery its proof reads. -/
theorem held_spread_upTo (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST tEnd t₁ t : ℕ) (u w : V) (D : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (t + Δ S))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (t + Δ S))
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
    exact mem_T_before_add_delay_of_held_at_upTo hDiv hMono hSync hCatch hRoots hParent
      ht₁t hGST hu hD hw ((compatible_iff _ _).2 (Or.inl hFD))
  · exact Or.inr (Nat.le_of_not_lt hlt)

/-- **A held block's justification height reaches every honest awake validator's `h_j` within one
delay.** Under `held_spread`'s hypotheses, `D`'s justification height is at most `w`'s `h_j` before
`t + Δ`: when `w` holds `D` on its finalized block's chain, by the cache (Lemma 57); otherwise
`D`'s justification height is less than its height (Lemma 47), at most `w`'s `h_j`.

The variables: as in `held_spread`.

Roots name blocks until `t + Δ S`: `held_spread`.

Restated with the delivery premises up to `t + Δ S`: the bound of its roots `hRoots`, the deadline of the one delivery its proof reads. -/
theorem held_spread_h_j_upTo (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST tEnd t₁ t : ℕ) (u w : V) (D : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (t + Δ S))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (t + Δ S))
    (hRoots : RootsNameBlocksUntil S Sched x (t + Δ S))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int))
    (ht₁t : t₁ ≤ t) (hGST : GST ≤ t) (hEnd : t + Δ S ≤ tEnd)
    (hu : u ∉ Sched.adv ((x[stepBefore x t₁].time : ℕ) : Int))
    (hD : D ∈ (stateBefore x t₁ u).S.T)
    (hw : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ S →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int)) :
    (chainStateOf S.C D).h_j ≤ (stateBefore x (t + Δ S) w).S.h_j := by
  rcases held_spread_upTo S Sched x GST tEnd t₁ t u w D hDiv hMono hSync hCatch hRoots hParent
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

Roots name blocks until `t + Δ S`: `held_spread`.

Restated with the delivery premises up to `t + Δ S`: the bound of its roots `hRoots`, the deadline of the one delivery its proof reads. -/
theorem held_spread_h_max_upTo (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST tEnd t₁ t : ℕ) (u w : V) (D : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (t + Δ S))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (t + Δ S))
    (hRoots : RootsNameBlocksUntil S Sched x (t + Δ S))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int))
    (ht₁t : t₁ ≤ t) (hGST : GST ≤ t) (hEnd : t + Δ S ≤ tEnd)
    (hu : u ∉ Sched.adv ((x[stepBefore x t₁].time : ℕ) : Int))
    (hD : D ∈ (stateBefore x t₁ u).S.T)
    (hw : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ S →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int)) :
    (chainStateOf S.C D).h ≤ (stateBefore x (t + Δ S) w).S.h_max := by
  rcases held_spread_upTo S Sched x GST tEnd t₁ t u w D hDiv hMono hSync hCatch hRoots hParent
    hU hThird ht₁t hGST hEnd hu hD hw with ⟨hDw, -⟩ | hle
  · exact height_le_h_max S Sched x (t + Δ S) w D hDw
  · have h := h_j_lt_h_max S Sched x (t + Δ S) w
    unfold Height at *
    omega

/-- `ClimbCtx S Sched x GST tGAT tAwakeEnd T₁ r H₂`: the hypotheses of `fork_choice_change_kinds`
that its proof reads: the execution assumptions, unforgeability, every validator honest in the
phase awake then, fewer than a third in the adversary set up to its end, the threshold `H₂` at `T₁`
and every honest attestation before `aR S r` at most `H₂`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round; `H₂`: the threshold.

Roots name blocks until `aR S r`: every reader of the bundle compares blocks held before times at
most `aR S r`, the end of the climb.

Restated with the delivery premises up to `aR S r`: the bound of its roots `hRoots`, the end of the climb; every reader of the bundle reads deliveries due by then. -/
structure ClimbCtxUpTo (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST tGAT tAwakeEnd T₁ r H₂ : ℕ) : Prop where
  hDiv : TimeDiverges x.toTrace
  hMono : Sched.MonotoneCorruption
  hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (aR S r)
  hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (aR S r)
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

namespace ClimbCtxUpTo

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd T₁ r H₂ : ℕ}

/-- B2 in the context: from `T₁ + Δ` to `aR S r`, an honest `h_max` is `H₂` or `H₂ + 1`.

Restated with the delivery premises up to `aR S r`: the bound of the bundle `ClimbCtxUpTo`. -/
theorem bounds (C : ClimbCtxUpTo S Sched x GST tGAT tAwakeEnd T₁ r H₂) {t : ℕ} {w : V}
    (h1 : T₁ + Δ S ≤ t) (h2 : t ≤ aR S r) (hw : w ∉ Sched.adv (t : Int)) :
    H₂ ≤ (stateBefore x t w).S.h_max ∧ (stateBefore x t w).S.h_max ≤ H₂ + 1 :=
  honest_h_max_bounds_upTo S Sched x GST tGAT tAwakeEnd T₁ r H₂ t w C.hDiv C.hMono (C.hSync.mono h2) (C.hCatch.mono h2)
    (C.hRoots.mono h2) C.hParent C.hU C.hGST C.hT₁ C.hThird C.hAwake C.hH₂ C.hOld C.hEnd
    h1 h2 hw

/-- Before `aR S r`, every `h_max` is at most `H₂ + 1` (A2).

Restated with the delivery premises up to `aR S r`: the bound of the bundle `ClimbCtxUpTo`. -/
theorem hmax_le (C : ClimbCtxUpTo S Sched x GST tGAT tAwakeEnd T₁ r H₂) {t : ℕ} (w : V)
    (h2 : t ≤ aR S r) : (stateBefore x t w).S.h_max ≤ H₂ + 1 := by
  obtain ⟨-, ⟨X, hX, hXh⟩, -⟩ := cachesWitnessed_of_stateBefore S Sched x t w
  rw [← hXh]
  exact held_height_le_before_action S Sched x tAwakeEnd r H₂ t w X C.hU C.hThird C.hOld h2
    C.hEnd hX

/-- A validator honest at `t ≤ tAwakeEnd` is awake and honest at every time of the phase up to
`t`.

Restated with the delivery premises up to `aR S r`: the bound of the bundle `ClimbCtxUpTo`. -/
theorem awakeHonest (C : ClimbCtxUpTo S Sched x GST tGAT tAwakeEnd T₁ r H₂) {w : V} {t : ℕ}
    (hw : w ∉ Sched.adv (t : Int)) (ht : t ≤ tAwakeEnd) :
    ∀ t' : ℕ, tGAT ≤ t' → t' ≤ t → w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int) := by
  intro t' h1 h2
  have hw' : w ∉ Sched.adv (t' : Int) := fun h => hw (C.hMono _ _ (by exact_mod_cast h2) h)
  exact ⟨C.hAwake t' h1 (le_trans h2 ht) w hw', hw'⟩

/-- `held_spread` in the context: a block that `u`, honest at `τ ≥ T₁`, holds before `τ + 1`
reaches `w`, honest at `t ≥ τ + 1 + Δ` before `aR S r`, by `τ + 1 + Δ`, or is at most its `h_j`.

Restated with the delivery premises up to `aR S r`: the bound of the bundle `ClimbCtxUpTo`. -/
theorem spread (C : ClimbCtxUpTo S Sched x GST tGAT tAwakeEnd T₁ r H₂) {τ t : ℕ} {u w : V}
    {D : Block V} (hT : T₁ ≤ τ) (hu : u ∉ Sched.adv (τ : Int))
    (hD : D ∈ (stateBefore x (τ + 1) u).S.T) (ht : τ + 1 + Δ S ≤ t) (hta : t < aR S r)
    (hw : w ∉ Sched.adv (t : Int)) :
    (D ∈ (stateBefore x (τ + 1 + Δ S) w).S.T ∧
        (stateBefore x (τ + 1 + Δ S) w).S.F.AncestorEq D) ∨
      (chainStateOf S.C D).h ≤ (stateBefore x (τ + 1 + Δ S) w).S.h_j :=
  held_spread_upTo S Sched x GST tAwakeEnd (τ + 1) (τ + 1) u w D C.hDiv C.hMono
  (C.hSync.mono (by omega)) (C.hCatch.mono (by omega))
    (C.hRoots.mono (by omega)) C.hParent C.hU C.hThird le_rfl
    (by have := C.hGST; have := C.hT₁; omega)
    (by have := C.hEnd; omega) (honest_config_succ x C.hDiv hu) hD
    (fun t' h1 h2 => C.awakeHonest hw (by have := C.hEnd; omega) t'
      (by have := C.hT₁; omega) (by omega))

/-- `held_spread_h_j` in the context.

Restated with the delivery premises up to `aR S r`: the bound of the bundle `ClimbCtxUpTo`. -/
theorem spread_h_j (C : ClimbCtxUpTo S Sched x GST tGAT tAwakeEnd T₁ r H₂) {τ t : ℕ} {u w : V}
    {D : Block V} (hT : T₁ ≤ τ) (hu : u ∉ Sched.adv (τ : Int))
    (hD : D ∈ (stateBefore x (τ + 1) u).S.T) (ht : τ + 1 + Δ S ≤ t) (hta : t < aR S r)
    (hw : w ∉ Sched.adv (t : Int)) :
    (chainStateOf S.C D).h_j ≤ (stateBefore x (τ + 1 + Δ S) w).S.h_j :=
  held_spread_h_j_upTo S Sched x GST tAwakeEnd (τ + 1) (τ + 1) u w D C.hDiv C.hMono
  (C.hSync.mono (by omega)) (C.hCatch.mono (by omega))
    (C.hRoots.mono (by omega)) C.hParent C.hU C.hThird le_rfl
    (by have := C.hGST; have := C.hT₁; omega)
    (by have := C.hEnd; omega) (honest_config_succ x C.hDiv hu) hD
    (fun t' h1 h2 => C.awakeHonest hw (by have := C.hEnd; omega) t'
      (by have := C.hT₁; omega) (by omega))

/-- `held_spread_h_max` in the context.

Restated with the delivery premises up to `aR S r`: the bound of the bundle `ClimbCtxUpTo`. -/
theorem spread_h_max (C : ClimbCtxUpTo S Sched x GST tGAT tAwakeEnd T₁ r H₂) {τ t : ℕ} {u w : V}
    {D : Block V} (hT : T₁ ≤ τ) (hu : u ∉ Sched.adv (τ : Int))
    (hD : D ∈ (stateBefore x (τ + 1) u).S.T) (ht : τ + 1 + Δ S ≤ t) (hta : t < aR S r)
    (hw : w ∉ Sched.adv (t : Int)) :
    (chainStateOf S.C D).h ≤ (stateBefore x (τ + 1 + Δ S) w).S.h_max :=
  held_spread_h_max_upTo S Sched x GST tAwakeEnd (τ + 1) (τ + 1) u w D C.hDiv C.hMono
  (C.hSync.mono (by omega)) (C.hCatch.mono (by omega))
    (C.hRoots.mono (by omega)) C.hParent C.hU C.hThird le_rfl
    (by have := C.hGST; have := C.hT₁; omega)
    (by have := C.hEnd; omega) (honest_config_succ x C.hDiv hu) hD
    (fun t' h1 h2 => C.awakeHonest hw (by have := C.hEnd; omega) t'
      (by have := C.hT₁; omega) (by omega))

/-- The level `j ≤ h_j` spreads: when `u`, honest at `τ ≥ T₁`, has `h_j ≥ j` before `τ + 1`, every
`w` honest at `t ≥ τ + 1 + Δ` before `aR S r` has `h_j ≥ j` before `τ + 1 + Δ` (the block
witnessing `u`'s cache, `held_spread_h_j`).

Restated with the delivery premises up to `aR S r`: the bound of the bundle `ClimbCtxUpTo`. -/
theorem spread_level_h_j (C : ClimbCtxUpTo S Sched x GST tGAT tAwakeEnd T₁ r H₂) (j : ℕ) {τ t : ℕ}
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
`w`, whose state is then contested at `H₂` too, or has `h_max = H₂ + 1`.

Restated with the delivery premises up to `aR S r`: the bound of the bundle `ClimbCtxUpTo`. -/
theorem spread_level_floor (C : ClimbCtxUpTo S Sched x GST tGAT tAwakeEnd T₁ r H₂) {τ t : ℕ}
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
and its justified block's witness reach `w`, whose state is then contested at `H₂ + 1`.

Restated with the delivery premises up to `aR S r`: the bound of the bundle `ClimbCtxUpTo`. -/
theorem spread_level_floor_succ (C : ClimbCtxUpTo S Sched x GST tGAT tAwakeEnd T₁ r H₂) {τ t : ℕ}
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
every `t ≥ t₂` before `aR S r` at which `w` is honest (`contest_persists` when `h_max` stays `H₂`).

Restated with the delivery premises up to `aR S r`: the bound of the bundle `ClimbCtxUpTo`. -/
theorem mono_level_floor (C : ClimbCtxUpTo S Sched x GST tGAT tAwakeEnd T₁ r H₂) {w : V} {t₂ t : ℕ}
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
`t ≥ t₂` before `aR S r` at which `w` is honest (`contest_persists`, `h_max` staying `H₂ + 1`).

Restated with the delivery premises up to `aR S r`: the bound of the bundle `ClimbCtxUpTo`. -/
theorem mono_level_floor_succ (C : ClimbCtxUpTo S Sched x GST tGAT tAwakeEnd T₁ r H₂) {w : V}
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

/-- **A fork-choice change of the climb crosses one of four levels.** At a time `t` from
`T₁ + Δ` to before `aR S r`, a `ForkChoiceChangeAt` at a validator honest at `t` crosses one of the
levels `H₂ − 1 ≤ h_j`, `H₂ ≤ head_height_floor`, `H₂ ≤ h_j`, `H₂ + 1 ≤ head_height_floor`: the
level fails before `t` and holds before `t + 1`.

Why: with `h_max` at `H₂` or `H₂ + 1` (B2, A2), a rise of `head_height_floor` (which is `h_max` or
`h_max − 1`) is to `H₂` from `H₂ − 1`, or to `H₂ + 1`. A root that becomes the justified block `J`
with `h_max = h_j + 1` and is no ancestor of the old root comes with a rise of `h_j` to `H₂ − 1` or
`H₂`: were `h_j` unchanged, `J` would be too (Lemma 76) and `h_max` as well, and the old root,
the finalized block of a contested state (the old `J` itself otherwise), would leave the new state
contested by the same block (Lemma 89a), against its root being `J`.

Restated with the delivery premises up to `aR S r`: the bound of the bundle `ClimbCtxUpTo`. -/
theorem classify (C : ClimbCtxUpTo S Sched x GST tGAT tAwakeEnd T₁ r H₂) {w : V} {t : ℕ}
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

end ClimbCtxUpTo

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
`aR S r`, and the levels are read before times at most `aR S r` (the bundle `ClimbCtx`).

Restated with the delivery premises up to `aR S r`: the bound of its roots `hRoots`; every delivery its proof reads is due by then. -/
theorem fork_choice_change_kinds_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd T₁ r H₂ : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (aR S r))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (aR S r))
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
  have C : ClimbCtxUpTo S Sched x GST tGAT tAwakeEnd T₁ r H₂ :=
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

