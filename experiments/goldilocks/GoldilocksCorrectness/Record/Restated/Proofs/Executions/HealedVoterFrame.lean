module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma91
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89CountJ
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89FastFamily
public import GoldilocksCorrectness.Proofs.Executions.Lemma91
public import GoldilocksCorrectness.Proofs.Executions.Lemma89CountJ
public import GoldilocksCorrectness.Proofs.Executions.Lemma89FastFamily
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# HealedVoterFrame, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/HealedVoterFrame.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: the voter frame after the hand-over,
namely a block on the honest chain before slot `s` held by every honest active voter of slot `s`
before the view freeze of slot `s − 1`, and `VoterFrameOnChainAt` for every honest active voter of
slot `s`. The page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff one_le_Δ
  slot_le_of_supportCutoff_lt supportCutoff_mono times_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Proofs.Executions (mem_awakeThroughout_iff)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-- **The updater of slot `μ` holds its saved confirmation from the support cutoff of `μ` to that
of `μ + 1`.** A proof-page helper.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, its run facts; `E`: the environment
  facts; `hSkew`: the clock bounds are less than `Δ`;
- `μ`: the slot; `t₀`: the time; `u`: the updater; `C`: the confirmation it saved.

Why: `u` is active after every step from its tick to the support cutoff of `μ` up to its tick to the
support cutoff of `μ + 1` (`updaterAt`; a tick to a clock value at most the duty window's start comes
before the first, `clock_mono`), so in every configuration in force at `t₀`, which lies strictly
between the two ticks' real times. It holds `C` at its tick to the support cutoff of `μ`
(`saved_confirmation_held_compatible_supportCutoff`), so before `t₀`. Its finalized block at its
update tick to the support cutoff of `μ + 1` is an ancestor of the confirmation the update saves
(Lemma 78's route: `update_state_of_tick`, `F.tk2.tick_supportCutoff_confirmation`,
`saved_confirmation_F_ancestorEq`), and the finalized block before `t₀` is an ancestor of that one.

Read aloud: an updater of `μ` holds the confirmation it saved for `μ`, with a compatible finalized
block, at every time strictly between its own tick to the support cutoff of `μ` and its own tick to
that of `μ + 1`. -/
theorem confirmation_updater_holder (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
 (μ t₀ : ℕ) (u : V) (C : Block V)
    (hu : u ∈ updaterAt M S A x μ)
    (hC : (x.tickOutput u (M.supportCutoff S.C (μ + 1))).savedConfirmation μ = some C)
    -- `u`'s tick to the support cutoff of `μ` is at a real time before `t₀`; its update tick after `t₀`
    --
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (h1 : x.time (x.tickStep u (M.supportCutoff S.C μ)) < t₀)
    (h2' : (t₀ : ℝ) < x.time (x.tickStep u (M.supportCutoff S.C (μ + 1)))) :
    u ∈ A.activeAtTime x t₀ ∧ u ∉ A.corrupted (x.stepBefore t₀) ∧
      C ∈ (x.stateBefore t₀ u).tree ∧ (x.stateBefore t₀ u).finalized.compatible C = true := by
  have hwin := (updaterAt_window M F) S A μ u E hu
  -- `u` held `C` with a compatible finalized block at its tick to the support cutoff of `μ`
  obtain ⟨hkμl, hCT, -⟩ :=
    (saved_confirmation_held_compatible_supportCutoff M F U) S A x R μ u C E hSkew hwin hC
  set kμ := x.tickStep u (M.supportCutoff S.C μ) with hkμ
  -- its tick `k'` to the support cutoff of `μ + 1`, and its activity from `kμ` up to `k'`
  obtain ⟨k', hk', hcase⟩ := Activity.mem_activeThroughoutToTick.1 hwin
  have hk's : x.tickStep u (M.supportCutoff S.C (μ + 1)) = k' := (tickStep_eq_of_lbl M) x E hk'
  rw [hk's] at h2'
  have hdw : duty_window_start S.C (μ + 1) < ((M.supportCutoff S.C μ : ℕ) : Int) := by
    have h1' := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_le_slotStart
      M.toSlotLayout F.sched) S μ
    have h2'' := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U)
      S μ
    have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S μ
    have h4 := (GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_le_dutyWindowStart
      M.toSlotLayout F.sched U) S (μ + 1)
    have hΔ := one_le_Δ S
    have h5 : M.dutyWindowStart S.C (μ + 1) < M.supportCutoff S.C μ := by omega
    have h6 : ((M.dutyWindowStart S.C (μ + 1) : ℕ) : Int) < ((M.supportCutoff S.C μ : ℕ) : Int) := by
      exact_mod_cast h5
    exact lt_of_le_of_lt h4 h6
  have hact : ∀ i : ℕ, kμ ≤ i → i ≤ k' → u ∈ A.active i := by
    intro i h1i h2i
    rcases hcase with hall | ⟨k, hkk', c, hca, hkc, hfrom⟩
    · exact hall i h2i
    · refine hfrom i ?_ h2i
      -- the tick to `c`, at most the duty window's start, is not after the tick to the cutoff of `μ`
      by_contra hlt
      push_neg at hlt
      have hcu : u ∉ A.corrupted k := Activity.not_mem_corrupted_of_mem_active (hfrom k le_rfl hkk')
      have := E.clock_mono kμ k u _ _ (by omega) hcu (Or.inl hkμl) (Or.inl hkc)
      have hcc : ((M.supportCutoff S.C μ : ℕ) : Int) ≤ (c : Int) := by exact_mod_cast this
      exact lt_irrefl _ (lt_of_le_of_lt (hcc.trans hca) hdw)
  have hkμk' : kμ < k' := (lt_of_time_lt M) x R (by linarith)
  have ht1 : 1 ≤ t₀ := by
    have : (0 : ℝ) < t₀ := lt_of_le_of_lt ((time_nonneg M) x R kμ) h1
    exact_mod_cast this
  obtain ⟨hb1, hb2⟩ := (stepBefore_time M) x R E ht1
  -- every configuration in force at `t₀` is after `kμ` and before `k'`
  have hin : ∀ i : ℕ, x.time i ≤ t₀ → (t₀ : ℝ) ≤ x.time (i + 1) → kμ ≤ i ∧ i ≤ k' := by
    intro i hi1 hi2
    refine ⟨?_, ?_⟩
    · have := (lt_of_time_lt M) x R (show x.time kμ < x.time (i + 1) by linarith)
      omega
    · exact ((lt_of_time_lt M) x R (show x.time i < x.time k' by linarith)).le
  have hsb := hin _ hb1.le hb2
  refine ⟨Activity.mem_activeAtTime.2 fun i hi1 hi2 => hact i (hin i hi1 hi2).1 (hin i hi1 hi2).2,
    Activity.not_mem_corrupted_of_mem_active (hact _ hsb.1 hsb.2), ?_, ?_⟩
  · show C ∈ (x.st (x.stepBefore t₀) u).tree
    have hCT' : C ∈ (x.st kμ u).tree := hCT
    exact (mem_T_mono M F) x R E u hsb.1 hCT'
  · -- the finalized block before the update is an ancestor of the saved confirmation (Lemma 78's route)
    show (x.st (x.stepBefore t₀) u).finalized.compatible C = true
    obtain ⟨τ, hτ, hτle⟩ := (tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hwin
      ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_lt_supportCutoff M.toSlotLayout
        F.sched U) S (μ + 1))
    obtain ⟨n'', sent, hrun, hAwake, hsave, -, -, -⟩ :=
      (update_state_of_tick M F U) S A x R μ u E hk' ⟨τ, hτ, hτle⟩
    obtain ⟨-, hInv, -, hcut, hsl⟩ := (cutoff_state_facts_of_tick M F U) x R E μ u τ hk' hτ hτle
    have hUpdate := F.tk2.tick_supportCutoff_confirmation S.C S.P S.X _ _ n'' sent hrun hInv hcut
      (by rw [hsl]; exact hAwake)
    rw [hsl] at hUpdate
    rw [hsave] at hC
    have h := GoldilocksCorrectness.Record.Statements.Routines.saved_confirmation_F_ancestorEq
      (Nat.le_add_left 1 μ) hUpdate
    rw [Nat.add_sub_cancel] at h
    have hFC : (x.tickInput u (M.supportCutoff S.C (μ + 1))).finalized.AncestorEq C := by
      rw [← (GoldilocksCorrectness.Record.Proofs.Routines.fg_to_ac_F M F)]; exact h C hC
    have hti : x.tickInput u (M.supportCutoff S.C (μ + 1)) = x.st k' u := by
      unfold Trace.tickInput; rw [hk's]
    rw [hti] at hFC
    exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans
      ((F_ancestorEq_of_le M F) x R E u hsb.2) hFC))

/-- A proof-page helper.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `x`, `R`: the setup, the execution, its run facts; `A`: the activity; `u`: the validator; `a`, `b`: the clock
  values that open and end the per-tick window; `t₀`: the window's start; `Δs`: its length.

Why: the steps up to the tick are covered by the per-tick set (in its second case, the tick to a value at most `a`
is before `t₀`), the steps after it by the stay row.

Read aloud: a validator active up to its tick to `b`, and for `Δs` after that tick, is active throughout
`[t₀, t₀ + Δs]` for every `t₀` between its last tick to a value at most `a` and its tick to `b`. -/
theorem activeThroughout_of_toTick_of_stay {S : Setup V} {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x) {A : Activity V} {u : V} {a : ℤ} {b : ℕ} {t₀ Δs : ℝ}
    (hu : u ∈ A.activeThroughoutToTick x a b)
    -- every tick of `u` to a value at most `a` is at a real time before `t₀`
    (hkt : ∀ (k : ℕ) (c : ℕ), (c : ℤ) ≤ a → x.lbl k = Event.tick u c → x.time k < t₀)
    -- `t₀` is at most the real time of every tick of `u` to `b`
    (ht₀ : ∀ k' : ℕ, x.lbl k' = Event.tick u b → t₀ ≤ x.time k')
    -- the stay row: `u` is active for `Δs` after the real time of its tick to `b`
    (hstay : ∀ k' : ℕ, x.lbl k' = Event.tick u b →
      u ∈ A.activeThroughout x (x.time k') (x.time k' + Δs)) :
    u ∈ A.activeThroughout x t₀ (t₀ + Δs) := by
  obtain ⟨k', hk', hcase⟩ := Activity.mem_activeThroughoutToTick.1 hu
  have hst := Activity.mem_activeThroughout.1 (hstay k' hk')
  have ht := ht₀ k' hk'
  rw [Activity.mem_activeThroughout]
  intro i hi1 hi2
  rcases Nat.lt_or_ge k' i with hlt | hle
  · -- after the tick: the stay row
    exact hst i (by linarith) (le_trans (R.time_mono hlt.le) (R.time_le_succ i))
  · -- up to the tick: the per-tick set
    rcases hcase with h | ⟨k, -, c, hc, hlbl, h⟩
    · exact h i hle
    · refine h i ?_ hle
      by_contra hik
      push Not at hik
      have h1 : x.time (i + 1) ≤ x.time k := R.time_mono hik
      have h2 := hkt k c hc hlbl
      linarith

/-- **The core of `chain_block_held_before_freeze`, with the delivery premises up to the view freeze of slot `s − 1`.**
The proof of both forms (`chain_block_held_before_freeze` passes `E.upTo _` and `Sy.upTo _`,
`chain_block_held_before_freeze_upTo` its own premises). A proof-page helper.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, its run facts; `GST`: the time from which the
  network is synchronous; `s₀`: the first slot of the chain; `s`: the slot; `w`: the voter; `B`: the block.

Why: write `vf` for the view freeze of slot `s − 1` and `t₀ := vf − max (Δ S) Δs`. `B` is an ancestor of, or
equal to, the confirmation `C` an updater `u` saved for a slot `μ < s`; `u` held `C` at its tick to the support
cutoff of `μ` (`saved_confirmation_held_compatible_supportCutoff`), so `C`'s slot starts before that cutoff
(`slot_le_clockValue_of_mem_tree`, `clockValue_lt_of_tick_of_active`). `w` ticks to the support cutoff of slot
`s − 1` and to `vf`, and is active from `t₀` up to its tick to `vf` (`honestActiveAt_window`). When `w`'s
finalized block is an ancestor of `B`, `C` reaches `w` by its tick to `vf`
(`block_at_tick_of_held_step_deadline`, with the window `[t₀, t₀ + Δs]`), from a holder:
- `u`'s tick to the support cutoff of `μ` more than the recovery delay before `vf`, `μ + 1 < s`: the validator
  `hHold` names, at `t₀`;
- the same with `μ = s − 1`: `u` itself at `t₀` (`confirmation_updater_holder`), active through the window by
  its own reader;
- `u`'s tick to the support cutoff of `μ` at or after `t₀`: `u` at that tick, active through the window by its
  own reader when `μ = s − 1`, and by its reader and the row `hStay` (`activeThroughout_of_toTick_of_stay`)
  when `μ + 1 < s`.
Otherwise `B` is an ancestor of `w`'s finalized block, which `w` holds.

Read aloud: an honest active voter holds the honest chain so far when its voter tree is frozen, with the
delivery premises up to the view freeze of slot `s − 1`. -/
theorem chain_block_held_before_freeze_core (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ s : ℕ) (w : V) (B : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.viewFreeze S.C (s - 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.viewFreeze S.C (s - 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.viewFreeze S.C (s - 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C (s - 1))
    (hHold : ∀ μ : ℕ, s₀ ≤ μ → μ + 1 < s →
      ∀ u ∈ updaterAt M S A x μ,
      (x.time (x.tickStep u (M.supportCutoff S.C μ)) : ℝ) + max (Δ S) Δs < M.viewFreeze S.C (s - 1) →
      ∀ C : Block V,
      (x.tickOutput u (M.supportCutoff S.C (μ + 1))).savedConfirmation μ = some C →
      ∃ v : V, v ∈ A.activeThroughout x ((M.viewFreeze S.C (s - 1) - max (Δ S) Δs : ℕ) : ℝ)
          (((M.viewFreeze S.C (s - 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) ∧
        v ∉ A.corrupted (x.stepBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs)) ∧
        C ∈ (x.stateBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs) v).tree ∧
        (x.stateBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs) v).finalized.compatible C = true)
    (hStay : ∀ σ : ℕ, s₀ ≤ σ → σ + 1 < s → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hw : w ∈ honestActiveAt M S A x s)
    (hB : OnHonestChainBefore M S A x s₀ s B)
    (hF : (x.tickInput w (M.viewFreeze S.C (s - 1))).finalized.compatible B = true) :
    B ∈ (x.tickInput w (M.viewFreeze S.C (s - 1))).tree := by
  obtain ⟨μ, hμs, hμ₀, u, hu, C, hC, hBC⟩ := hB
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  have hN0 : (0 : ℝ) ≤ ΔNet := Nat.cast_nonneg _
  -- the times of the slots `s − 1`, `s`, `s + 1`, `μ`, `μ + 1`
  obtain ⟨-, hcs1, hfs1, hss1, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s - 1)
  rw [show s - 1 + 1 = s by omega] at hss1
  obtain ⟨-, hcs, -, hss, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s
  obtain ⟨-, hcs', -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s + 1)
  obtain ⟨-, hcμ, -, hsμ, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S μ
  obtain ⟨-, hcμ1, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 1)
  have hslμ : M.slotStart S.C μ ≤ M.slotStart S.C (s - 1) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega)
  -- the sync bound over the natural numbers
  have hΔsN : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have h : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h
  -- the window start `t₀`
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℕ, t₀ = M.viewFreeze S.C (s - 1) - max (Δ S) Δs := ⟨_, rfl⟩
  rw [← ht₀] at hHold
  have ht₀R : (t₀ : ℝ) + ((max (Δ S) Δs : ℕ) : ℝ) = ((M.viewFreeze S.C (s - 1) : ℕ) : ℝ) := by
    exact_mod_cast (show t₀ + max (Δ S) Δs = M.viewFreeze S.C (s - 1) by omega)
  have hmxR : ((Δ S : ℕ) : ℝ) ≤ ((max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hmx1
  have hvfR : ((M.viewFreeze S.C (s - 1) : ℕ) : ℝ) = ((M.supportCutoff S.C (s - 1) : ℕ) : ℝ) + Δ S := by
    exact_mod_cast (show M.viewFreeze S.C (s - 1) = M.supportCutoff S.C (s - 1) + Δ S by omega)
  have hcsR : ((M.supportCutoff S.C s : ℕ) : ℝ) = ((M.supportCutoff S.C (s - 1) : ℕ) : ℝ) + 4 * Δ S := by
    exact_mod_cast (show M.supportCutoff S.C s = M.supportCutoff S.C (s - 1) + 4 * Δ S by omega)
  have hcs'R : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = ((M.supportCutoff S.C (s - 1) : ℕ) : ℝ) + 8 * Δ S := by
    exact_mod_cast (show M.supportCutoff S.C (s + 1) = M.supportCutoff S.C (s - 1) + 8 * Δ S by omega)
  have hcμR : ((M.supportCutoff S.C μ : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (s - 1) : ℕ) : ℝ) := by
    exact_mod_cast (show M.supportCutoff S.C μ ≤ M.supportCutoff S.C (s - 1) by omega)
  have hcμ1R : ((M.supportCutoff S.C (μ + 1) : ℕ) : ℝ) = ((M.supportCutoff S.C μ : ℕ) : ℝ) + 4 * Δ S := by
    exact_mod_cast (show M.supportCutoff S.C (μ + 1) = M.supportCutoff S.C μ + 4 * Δ S by omega)
  have hcμ2R : ((M.supportCutoff S.C μ : ℕ) : ℝ) = ((M.slotStart S.C μ : ℕ) : ℝ) + 2 * Δ S := by
    exact_mod_cast hcμ
  -- the duty windows' starts, integers (`duty_window_start_eq`, `slotStart_cast`)
  have hD : ∀ σ : ℕ, @Eq Int (duty_window_start S.C σ + ((4 * Δ S * S.C.k : ℕ) : ℤ))
      (((M.slotStart S.C σ : ℕ) : ℤ) + (Δ S : ℤ)) := by
    intro σ
    rw [GoldilocksCorrectness.Proofs.Routines.duty_window_start_eq,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_cast M.toSlotLayout F.sched U) S σ,
      ← GoldilocksCorrectness.Proofs.Routines.Δ_cast S]
    push_cast
    ring
  -- the duty window of every slot `σ ≤ s` starts at least one delay before `t₀`
  have hdws : ∀ σ : ℕ, σ ≤ s → (duty_window_start S.C σ : ℝ) + Δ S ≤ t₀ := by
    intro σ hσ
    have h1 := hD σ
    have h2 : M.slotStart S.C σ ≤ M.slotStart S.C s :=
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hσ
    have h3 : t₀ + max (Δ S) Δs = M.slotStart S.C (s - 1) + 3 * Δ S := by omega
    have hN : M.slotStart S.C σ + Δ S + Δ S ≤ t₀ + 4 * Δ S * S.C.k := by
      have hK1 := hΔsN
      generalize 4 * Δ S * S.C.k = K at hK1 ⊢
      omega
    have hI : duty_window_start S.C σ + (Δ S : ℤ) ≤ ((t₀ : ℕ) : ℤ) := by
      have hNZ : ((M.slotStart S.C σ + Δ S + Δ S : ℕ) : ℤ) ≤ ((t₀ + 4 * Δ S * S.C.k : ℕ) : ℤ) := by
        exact_mod_cast hN
      push_cast at hNZ h1
      linarith
    have hR : ((duty_window_start S.C σ + (Δ S : ℤ) : ℤ) : ℝ) ≤ (((t₀ : ℕ) : ℤ) : ℝ) := by exact_mod_cast hI
    push_cast at hR
    exact hR
  -- the duty window of slot `μ + 1` starts three delays before slot `μ`
  have hdw3 : (duty_window_start S.C (μ + 1) : ℝ) + 3 * Δ S ≤ M.slotStart S.C μ := by
    have h1 := hD (μ + 1)
    have hk4 := Nat.mul_le_mul_left (4 * Δ S) S.C.k_ge_two
    have hN : M.slotStart S.C (μ + 1) + Δ S + 3 * Δ S ≤ M.slotStart S.C μ + 4 * Δ S * S.C.k := by
      generalize 4 * Δ S * S.C.k = K at hk4 ⊢
      omega
    have hI : duty_window_start S.C (μ + 1) + 3 * (Δ S : ℤ) ≤ ((M.slotStart S.C μ : ℕ) : ℤ) := by
      have hNZ : ((M.slotStart S.C (μ + 1) + Δ S + 3 * Δ S : ℕ) : ℤ) ≤
          ((M.slotStart S.C μ + 4 * Δ S * S.C.k : ℕ) : ℤ) := by
        exact_mod_cast hN
      push_cast at hNZ h1
      linarith
    have hR : ((duty_window_start S.C (μ + 1) + 3 * (Δ S : ℤ) : ℤ) : ℝ) ≤
        (((M.slotStart S.C μ : ℕ) : ℤ) : ℝ) := by exact_mod_cast hI
    push_cast at hR
    exact hR
  -- `w`: its ticks to the support cutoff of slot `s − 1` and to the view freeze, and its window from `t₀`
  have hwT := (honestActiveAt_window M F) S A s w E hw
  obtain ⟨kW, hkW, hwinW⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hwT
    (t₀ := ((M.supportCutoff S.C (s - 1) : ℕ) : ℝ) - ΔClockAhead)
    (by have := hdws s le_rfl; linarith)
  have hkWt := (E.tick_active kW w _ hkW).2.1
  have htickW : ∀ c : ℕ, M.supportCutoff S.C (s - 1) ≤ c → c ≤ M.viewFreeze S.C (s - 1) →
      ∃ i : ℕ, x.lbl i = Event.tick w c := by
    intro c hc1 hc2
    have hc1R : ((M.supportCutoff S.C (s - 1) : ℕ) : ℝ) ≤ c := by exact_mod_cast hc1
    have hc2R : (c : ℝ) ≤ ((M.viewFreeze S.C (s - 1) : ℕ) : ℝ) := by exact_mod_cast hc2
    obtain ⟨i, hi, -⟩ := E.tick_of_active c (by omega) w (fun i h1 h2 =>
      hwinW i (by linarith) ((lt_of_time_lt M) x R (by linarith)).le)
    exact ⟨i, hi⟩
  obtain ⟨kw, hkw⟩ := htickW (M.viewFreeze S.C (s - 1)) (by omega) le_rfl
  obtain ⟨k₂, hk₂⟩ := htickW (M.supportCutoff S.C (s - 1)) le_rfl (by omega)
  have hkwe : x.tickStep w (M.viewFreeze S.C (s - 1)) = kw := (tickStep_eq_of_lbl M) x E hkw
  have hwk : w ∉ A.corrupted kw := E.not_mem_corrupted_of_tick hkw
  have hkwt := (E.tick_active kw w _ hkw).2.2
  obtain ⟨kW', hkW', hwinT⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hwT
    (t₀ := (t₀ : ℝ)) (by have := hdws s le_rfl; linarith)
  have hkW't := (E.tick_active kW' w _ hkW').2.1
  have hkwW : kw < kW' := (lt_of_time_lt M) x R (by linarith)
  unfold Trace.tickInput at hF ⊢
  rw [hkwe] at hF hRoots ⊢
  -- `B` an ancestor of `w`'s finalized block: held already
  rcases (compatible_iff _ _).1 hF with hFB | hBF
  swap
  · exact (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E kw w _ B
      (F.nd.nodeInv_finalized_mem_tree
        ((GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariant M F) S A x R E kw w hwk).1) hBF
  have hFw : (x.st kw w).finalized.compatible C = true :=
    (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFB hBC))
  suffices hCw : C ∈ (x.st kw w).tree from
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E kw w C B hCw hBC
  by_cases hg : C = Block.genesis
  · subst hg
    exact (GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F) S A x R E kw w
  -- the updater `u`: it held `C` at its tick to the support cutoff of `μ`
  have huW := (updaterAt_window M F) S A μ u E hu
  obtain ⟨hkμl, hCT, hFC⟩ :=
    (saved_confirmation_held_compatible_supportCutoff M F U) S A x R μ u C E hSkew huW hC
  have hCT' : C ∈ (x.st (x.tickStep u (M.supportCutoff S.C μ)) u).tree := hCT
  have hFC' : (x.st (x.tickStep u (M.supportCutoff S.C μ)) u).finalized.compatible C = true := hFC
  have huk : u ∉ A.corrupted (x.tickStep u (M.supportCutoff S.C μ)) := E.not_mem_corrupted_of_tick hkμl
  have hkμt := (E.tick_active _ u _ hkμl).2.2
  obtain ⟨kU', hkU', hwinU⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E huW
    (t₀ := ((M.supportCutoff S.C μ : ℕ) : ℝ) - ΔClockAhead) (by linarith)
  have hkU't := (E.tick_active kU' u _ hkU').2.1
  have hkμU : x.tickStep u (M.supportCutoff S.C μ) < kU' := (lt_of_time_lt M) x R (by linarith)
  have hkU'e : x.tickStep u (M.supportCutoff S.C (μ + 1)) = kU' := (tickStep_eq_of_lbl M) x E hkU'
  -- `C`'s slot starts before the support cutoff of `μ`, so at most the support cutoff of slot `s − 1`
  have hcv := (clockValue_lt_of_tick_of_active M F) E hkμl
    (by omega) (fun j hj hjk => hwinU j hj (by omega))
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have hDc₂ : M.slotStart S.C C.slot ≤ M.supportCutoff S.C (s - 1) := by
    have hHs := (slot_le_clockValue_of_mem_tree M F) R E huk hCT'
    rw [← hsl] at hHs
    have := ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_iff M.toSlotLayout F.sched) S C.slot
      _).2 hHs
    omega
  -- the delivery to `w` from a holder active through `[t₀, t₀ + Δs]`
  have key : ∀ (h : V) (kU : ℕ) (tu : ℝ), x.time kU ≤ tu →
      tu + ΔNet + ΔClockAhead ≤ ((M.viewFreeze S.C (s - 1) : ℕ) : ℝ) →
      tu + ΔClockAhead < ((M.viewFreeze S.C (s - 1) : ℕ) : ℝ) →
      h ∈ A.activeThroughout x (t₀ : ℝ) ((t₀ : ℝ) + Δs) → h ∉ A.corrupted kU → C ∈ (x.st kU h).tree →
      (x.st (x.stepBefore t₀) h).finalized.compatible C = true → C ∈ (x.st kw w).tree := by
    intro h kU tu htu hc1 hc2 hh₀ hhk hhC hhF
    exact (block_at_tick_of_held_step_deadline M F U) S A x R GST (M.viewFreeze S.C (s - 1)) tu kU t₀
      (M.viewFreeze S.C (s - 1)) (M.supportCutoff S.C (s - 1)) kw k₂ h w C E hRedeliver Sy
      hRoots hParent (by omega) (by omega) hc1 hc2 (by linarith) (by omega) hh₀ htu hhk hhC hhF hg hkw
      (fun i hi hik => hwinT i hi (by omega)) hk₂ (by omega) hDc₂ hFw
  -- the updater of slot `s − 1` is active through `[t₀, t₀ + Δs]` by its own reader
  have hlast : μ + 1 = s → u ∈ A.activeThroughout x (t₀ : ℝ) ((t₀ : ℝ) + Δs) := by
    intro hμe
    have he : (((t₀ + Δs : ℕ) : ℕ) : ℝ) + ΔClockAhead < ((M.supportCutoff S.C (μ + 1) : ℕ) : ℝ) := by
      have h1 : t₀ + Δs + 3 * Δ S ≤ M.supportCutoff S.C (μ + 1) := by rw [hμe]; omega
      have h2 : ((t₀ + Δs + 3 * Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (μ + 1) : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h2 ⊢
      linarith
    have h := (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E huW (a' := t₀) (e := t₀ + Δs)
      (by have := hdws (μ + 1) (by omega); linarith) he
    rwa [Nat.cast_add] at h
  by_cases hfar : (x.time (x.tickStep u (M.supportCutoff S.C μ)) : ℝ) + max (Δ S) Δs <
      M.viewFreeze S.C (s - 1)
  · have hfar' : x.time (x.tickStep u (M.supportCutoff S.C μ)) < (t₀ : ℝ) := by
      push_cast at ht₀R hfar
      linarith
    have ht₀v : (t₀ : ℝ) + Δ S ≤ ((M.viewFreeze S.C (s - 1) : ℕ) : ℝ) := by linarith
    rcases Nat.lt_or_ge (μ + 1) s with hμ1 | hμ1
    · -- the validator `hHold` names, at `t₀`
      obtain ⟨v, hv₀, hvh, hCv, hFv⟩ := hHold μ hμ₀ hμ1 u hu hfar C hC
      exact key v (x.stepBefore t₀) t₀ ((time_stepBefore_le M) x R E t₀) (by linarith) (by linarith)
        hv₀ hvh hCv hFv
    · -- `μ = s − 1`: `u` itself at `t₀`
      have hμe : μ + 1 = s := by omega
      have h2' : (t₀ : ℝ) < x.time (x.tickStep u (M.supportCutoff S.C (μ + 1))) := by
        rw [hkU'e]
        have : M.supportCutoff S.C (μ + 1) = M.supportCutoff S.C s := by rw [hμe]
        rw [this] at hkU't
        linarith
      obtain ⟨-, h2, h3, h4⟩ := (confirmation_updater_holder M F U) S A x R E μ t₀ u C hu hC hSkew hfar' h2'
      exact key u (x.stepBefore t₀) t₀ ((time_stepBefore_le M) x R E t₀) (by linarith) (by linarith)
        (hlast hμe) h2 h3 h4
  · -- `u`'s tick to the support cutoff of `μ` is at or after `t₀`: `u` at that tick
    have hnear : (t₀ : ℝ) ≤ x.time (x.tickStep u (M.supportCutoff S.C μ)) := by
      push Not at hfar
      push_cast at ht₀R hfar
      linarith
    have hFa : (x.st (x.stepBefore t₀) u).finalized.compatible C = true :=
      GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible
        ((F_ancestorEq_of_le M F) x R E u ((stepBefore_le_of_le_time_st M F) R E hnear)) hFC'
    have hact : u ∈ A.activeThroughout x (t₀ : ℝ) ((t₀ : ℝ) + Δs) := by
      rcases Nat.lt_or_ge (μ + 1) s with hμ1 | hμ1
      · -- the reader up to its tick to the support cutoff of `μ + 1`, then the row `hStay`
        refine (activeThroughout_of_toTick_of_stay M F) R huW ?_ ?_ ?_
        · intro k c hc hl
          have hkc := (E.tick_active k u c hl).2.2
          have hcR : ((c : ℤ) : ℝ) ≤ (duty_window_start S.C (μ + 1) : ℝ) := by exact_mod_cast hc
          have := hdws (μ + 1) (by omega)
          push_cast at hcR
          linarith
        · intro k' hk'
          have := (E.tick_active k' u _ hk').2.1
          linarith
        · intro k' hk'
          rw [← (tickStep_eq_of_lbl M) x E hk']
          exact hStay μ hμ₀ hμ1 u hu
      · exact hlast (by omega)
    exact key u (x.tickStep u (M.supportCutoff S.C μ)) (x.time (x.tickStep u (M.supportCutoff S.C μ))) le_rfl
      (by linarith) (by linarith) hact huk hCT' hFa

/-- **A block on the honest chain before `s` is held by an honest active voter of `s` before the
view freeze of slot `s − 1`.** The proof; the audited statement is in
`Statements/Executions/HealedVoterFrameStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the first slot of the chain; `s`: the slot; `w`: the voter; `B`:
  the block.

Roots name blocks until `M.viewFreeze S.C (s - 1)`: the confirmation the updater holds reaches `w`
by the view freeze of slot `s − 1`, one delay after the support cutoff of slot `s − 1`
(`mem_T_before_add_delay_of_held_at`).

 The updater serves its own confirmation when its tick to
that support cutoff is within that delay of the view freeze, staying active for `Δs` after its tick to the support
cutoff of the next slot; otherwise the validator `hHold` names serves it.

Read aloud: an honest active voter holds the honest chain so far when its voter tree is frozen. -/
theorem chain_block_held_before_freeze (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ s : ℕ) (w : V) (B : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.viewFreeze S.C (s - 1)))))
    (hParent : ParentHeldAtDelivery M x)
    -- the recovery delay after `GST` has elapsed by the view freeze of slot `s − 1`
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C (s - 1))
    -- for every confirmation an updater saved for a slot `μ` before `s − 1` whose updater ticked to
    -- the support cutoff of `μ` more than the recovery delay before the view freeze of slot `s − 1`
    --, some validator active at
    -- the window start, honest at its last step before it, holds it with a compatible finalized
    -- block; that validator is active at every step at a real time from the window start to one
    -- sync delay after it (, applies)
    (hHold : ∀ μ : ℕ, s₀ ≤ μ → μ + 1 < s →
      ∀ u ∈ updaterAt M S A x μ,
      (x.time (x.tickStep u (M.supportCutoff S.C μ)) : ℝ) + max (Δ S) Δs < M.viewFreeze S.C (s - 1) →
      ∀ C : Block V,
      (x.tickOutput u (M.supportCutoff S.C (μ + 1))).savedConfirmation μ = some C →
      ∃ v : V, v ∈ A.activeThroughout x ((M.viewFreeze S.C (s - 1) - max (Δ S) Δs : ℕ) : ℝ)
          (((M.viewFreeze S.C (s - 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) ∧
        v ∉ A.corrupted (x.stepBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs)) ∧
        C ∈ (x.stateBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs) v).tree ∧
        (x.stateBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs) v).finalized.compatible C = true)
    -- every updater of a slot from the healed slot `s₀` to `s − 2` is active for the sync delay after the real time
    -- of its own tick to the support cutoff of the next slot
    (hStay : ∀ σ : ℕ, s₀ ≤ σ → σ + 1 < s → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hw : w ∈ honestActiveAt M S A x s)
    (hB : OnHonestChainBefore M S A x s₀ s B)
    (hF : (x.tickInput w (M.viewFreeze S.C (s - 1))).finalized.compatible B = true) :
    B ∈ (x.tickInput w (M.viewFreeze S.C (s - 1))).tree := by
  exact (chain_block_held_before_freeze_core M F U) S A x R GST s₀ s w B (E.upTo _) hNet hSkew hRedeliver (Sy.upTo _) hΔs hRoots
    hParent hGST hHold hStay hw hB hF

/-- **The voter frame after the hand-over, with the delivery premises up to the view freeze of slot `s − 1`.** The proof of
the three forms: `voterFrame_after_handover_until` passes `E.upTo _` and `Sy.upTo _`, `voterFrame_after_handover_until_upTo`
its own premises lowered to the view freeze of slot `s − 1`. A proof-page helper.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, its run facts; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `i₂`: the step from which the caches are on the
  chain; `H`: the threshold; `s`: the slot of the vote; `w`: the voter.

Why: let `k` be a tick of `w` to the vote time of slot `s` (the one tick, `tickStep_eq_of_lbl`). The root of `w`'s fork
choice at `k` is on the chain before `s` (Lemma 91 (f), `lem91f_voter_root_on_chain_before_until`, read at `k`: every
tick to a support cutoff of a slot `s_a + 1` before `k` is at a real time less than the support cutoff of slot `s`), so
compatible with every block `B` of that chain. When the root is `B` or an ancestor of `B`, the state at `k` is not
contested and its `head_height_floor` is the greatest chain-state height minus one (Lemma 91 (d),
`lem91d_not_contested_until`); some block of the chain before `s` has a chain-state height at least that (the justified
block when the greatest chain-state height is at most `H + 1`, otherwise the entry the progress certificate at the
greatest chain-state height minus one of the block that raised the chain names, Lemma 67, `cert_entry_at_slot`). The later
of `B` and that block is held at `w`'s tick to the view freeze of slot `s − 1` (`chain_block_held_before_freeze_core`:
`w`'s finalized block there is an ancestor of its finalized block at `k`, an ancestor of the root), so it is in the voter
tree of slot `s` and a viable head at `k` (`proposal_viable_head_at_tick_st`).

Read aloud: after the hand-over, at every tick of an honest active voter to the vote time of its slot, the root of its
fork choice is compatible with the honest chain before that slot, and, when the root is a block of that chain or an
ancestor of one, some block of its voter tree that is that block or a descendant of it is a viable head. -/
theorem voterFrame_after_handover_core (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ i₂ H s : ℕ) (w : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.viewFreeze S.C (s - 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.viewFreeze S.C (s - 1)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.voteTime S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time (x.tickStep w (M.voteTime S.C s))) (M.supportCutoff S.C (s₀ + 1))))
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C (s - 1))
    (hHold : ∀ μ : ℕ, s₀ ≤ μ → μ + 1 < s →
      ∀ u ∈ updaterAt M S A x μ,
      (x.time (x.tickStep u (M.supportCutoff S.C μ)) : ℝ) + max (Δ S) Δs < M.viewFreeze S.C (s - 1) →
      ∀ C : Block V,
      (x.tickOutput u (M.supportCutoff S.C (μ + 1))).savedConfirmation μ = some C →
      ∃ v : V, v ∈ A.activeThroughout x ((M.viewFreeze S.C (s - 1) - max (Δ S) Δs : ℕ) : ℝ)
          (((M.viewFreeze S.C (s - 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) ∧
        v ∉ A.corrupted (x.stepBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs)) ∧
        C ∈ (x.stateBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs) v).tree ∧
        (x.stateBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs) v).finalized.compatible C = true)
    (hStay : ∀ σ : ℕ, s₀ ≤ σ → σ + 1 < s → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the caches at every step at a real time after `x[i₂].time`
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₂ < x.time j → x.time j ≤ x.time (x.tickStep w (M.voteTime S.C s)) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (hs : x.time i₂ < M.viewFreeze S.C (s - 1))
    (hChain : ConfirmationsChainBefore M S A x s₀ s)
    (hw : w ∈ honestActiveAt M S A x s) :
    VoterFrameOnChainAt M S A x s₀ s w := by
  intro B hB k hk
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hs1 : 1 ≤ s := by obtain ⟨μ, hμ, -⟩ := hB; omega
  -- the times of the slots `s − 1`, `s`, `s + 1`
  obtain ⟨hvs, hcs, -, hss, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s
  obtain ⟨-, -, hfs1, hss1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s - 1)
  rw [show s - 1 + 1 = s by omega] at hss1
  obtain ⟨-, hcs', -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s + 1)
  have hvtR : ((M.voteTime S.C s : ℕ) : ℝ) = ((M.viewFreeze S.C (s - 1) : ℕ) : ℝ) + 2 * Δ S := by
    exact_mod_cast (show M.voteTime S.C s = M.viewFreeze S.C (s - 1) + 2 * Δ S by omega)
  have hcsR : ((M.supportCutoff S.C s : ℕ) : ℝ) = ((M.voteTime S.C s : ℕ) : ℝ) + Δ S := by
    exact_mod_cast (show M.supportCutoff S.C s = M.voteTime S.C s + Δ S by omega)
  have hcs'R : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = ((M.voteTime S.C s : ℕ) : ℝ) + 5 * Δ S := by
    exact_mod_cast (show M.supportCutoff S.C (s + 1) = M.voteTime S.C s + 5 * Δ S by omega)
  -- `k` is `w`'s tick to the vote time of slot `s`, at a real time in `[vt − ΔClockAhead, vt + ΔClockBehind]`
  have hke : x.tickStep w (M.voteTime S.C s) = k := (tickStep_eq_of_lbl M) x E hk
  rw [hke] at hRoots hAdvQ hCaches
  have hwk : w ∉ A.corrupted k := E.not_mem_corrupted_of_tick hk
  obtain ⟨-, hkt1, hkt2⟩ := E.tick_active k w _ hk
  -- `k` is strictly after the hand-over time: `vt(s) − ΔClockAhead > vf(s − 1) > x.time i₂`
  have hiw : x.time i₂ < x.time k := by linarith
  -- the caches at the steps at the real time of `k`, the one state Lemma 91 (d) and (f) read
  have hCk : ∀ (j : ℕ) (u : V), x.time k ≤ x.time j → x.time j ≤ x.time k → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u) :=
    fun j u h₁ h₂ hu => hCaches j u (lt_of_lt_of_le hiw h₁) h₂ hu
  -- every tick to a support cutoff before `k` is for a slot before `s`
  have hs' : ∀ s_a : ℕ, (∃ (k' : ℕ) (u : V), k' < k ∧ x.lbl k' = Event.tick u (M.supportCutoff S.C (s_a + 1))) →
      s_a < s := by
    rintro s_a ⟨k', u, hk'k, hl'⟩
    have h1 := (E.tick_active k' u _ hl').2.1
    have h2 : x.time k' ≤ x.time k := (time_mono M) x R hk'k.le
    have h3 : ((M.supportCutoff S.C (s_a + 1) : ℕ) : ℝ) < ((M.supportCutoff S.C s : ℕ) : ℝ) := by linarith
    have h4 : M.supportCutoff S.C (s_a + 1) < M.supportCutoff S.C (s - 1 + 1) := by
      rw [show s - 1 + 1 = s by omega]; exact_mod_cast h3
    have := ((GoldilocksCorrectness.Record.Proofs.Routines.slot_le_of_supportCutoff_lt M.toSlotLayout F.sched) S s_a
      (s - 1)).2.1 h4
    omega
  -- the root is on the chain before `s` (Lemma 91 (f))
  have hR := (lem91f_voter_root_on_chain_before_until M F U Fx) S A x R s₀ k s H w E hRoots hAdvQ hOld (hCk k w le_rfl le_rfl hwk)
    hwk hs'
  refine ⟨(onHonestChainBefore_compatible M F) S A x s₀ s _ B hChain hR hB, fun hRB => ?_⟩
  have hRB' : (M.get_fc_root (x.st k w)).AncestorEq B := by
    rw [← (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]; exact hRB
  -- the state is not contested, and `head_height_floor` is `h_max − 1` (Lemma 91 (d))
  have hfl := ((lem91d_not_contested_until M F U Fx) S A x R s₀ k s H w E hAdvQ hChain hOld (hCk k w le_rfl le_rfl hwk) hwk hs').2
  -- `w`'s tick `kw` to the view freeze of slot `s − 1`, before `k`, from a smaller clock value
  have hD : @Eq Int (duty_window_start S.C s + ((4 * Δ S * S.C.k : ℕ) : ℤ))
      (((M.slotStart S.C s : ℕ) : ℤ) + (Δ S : ℤ)) := by
    rw [GoldilocksCorrectness.Proofs.Routines.duty_window_start_eq,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_cast M.toSlotLayout F.sched U) S s,
      ← GoldilocksCorrectness.Proofs.Routines.Δ_cast S]
    push_cast
    ring
  have hdw : (duty_window_start S.C s : ℝ) + 3 * Δ S ≤ ((M.viewFreeze S.C (s - 1) : ℕ) : ℝ) := by
    have hk4 := Nat.mul_le_mul_left (4 * Δ S) S.C.k_ge_two
    have hN : M.slotStart S.C s + Δ S + 3 * Δ S ≤ M.viewFreeze S.C (s - 1) + 4 * Δ S * S.C.k := by
      generalize 4 * Δ S * S.C.k = K at hk4 ⊢
      omega
    have hI : duty_window_start S.C s + 3 * (Δ S : ℤ) ≤ ((M.viewFreeze S.C (s - 1) : ℕ) : ℤ) := by
      have hNZ : ((M.slotStart S.C s + Δ S + 3 * Δ S : ℕ) : ℤ) ≤
          ((M.viewFreeze S.C (s - 1) + 4 * Δ S * S.C.k : ℕ) : ℤ) := by
        exact_mod_cast hN
      push_cast at hNZ hD
      linarith
    have hR' : ((duty_window_start S.C s + 3 * (Δ S : ℤ) : ℤ) : ℝ) ≤
        (((M.viewFreeze S.C (s - 1) : ℕ) : ℤ) : ℝ) := by exact_mod_cast hI
    push_cast at hR'
    exact hR'
  have hwT := (honestActiveAt_window M F) S A s w E hw
  obtain ⟨kW, hkW, hwinW⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hwT
    (t₀ := ((M.viewFreeze S.C (s - 1) : ℕ) : ℝ) - ΔClockAhead) (by linarith)
  have hkWt := (E.tick_active kW w _ hkW).2.1
  obtain ⟨kw, hkw, -, hkw2⟩ := E.tick_of_active (M.viewFreeze S.C (s - 1)) (by omega) w
    (fun i h1 h2 => hwinW i h1 ((lt_of_time_lt M) x R (by linarith)).le)
  have hkwW : kw < kW := (lt_of_time_lt M) x R (by linarith)
  have hlt : x.clockValue kw w < M.viewFreeze S.C (s - 1) :=
    (clockValue_lt_of_tick_of_active M F) E hkw (by omega) (fun j h1 h2 => hwinW j h1 (by omega))
  have hkwk : kw ≤ k := ((tick_lt_of_clock_lt M) x E hkw hk (by omega)).le
  have hkwe : x.tickStep w (M.viewFreeze S.C (s - 1)) = kw := (tickStep_eq_of_lbl M) x E hkw
  -- `w`'s finalized block at `kw` is an ancestor of `B`
  have hFk : (x.st kw w).finalized.AncestorEq B :=
    ancestorEq_trans ((F_ancestorEq_of_le M F) x R E w hkwk)
      (ancestorEq_trans ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E
        k w) hRB')
  have hRootsW : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.viewFreeze S.C (s - 1)))) := by
    rw [hkwe]
    exact (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) ((time_mono M) x R hkwk) hRoots
  have hheld : ∀ D : Block V, OnHonestChainBefore M S A x s₀ s D → B.AncestorEq D →
      D ∈ (x.tickInput w (M.viewFreeze S.C (s - 1))).tree := fun D hD hBD =>
    (chain_block_held_before_freeze_core M F U) S A x R GST s₀ s w D E hNet hSkew hRedeliver Sy hΔs hRootsW hParent
      hGST hHold hStay hw hD (by
        unfold Trace.tickInput
        rw [hkwe]
        exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFk hBD)))
  -- a block of the chain before `s` at a chain-state height at least `h_max − 1`
  obtain ⟨Eb, hE, hEh⟩ : ∃ Eb : Block V, OnHonestChainBefore M S A x s₀ s Eb ∧
      hMax M S.C (x.st k w) - 1 ≤ (M.chainStateOf S.C Eb).h := by
    by_cases hM : hMax M S.C (x.st k w) ≤ H + 1
    · -- the justified block, on the chain at the height `h_j > H`
      obtain ⟨hH, -, -, hJh, -⟩ := hCaches k w hiw le_rfl hwk
      obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E k w
      have h1 : 1 ≤ (M.chainStateOf S.C D).h_j := by
        rw [← hhjD]; exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H) hH)
      obtain ⟨hJC, -, -⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).1 h1
      rw [← hJD, ← hhjD] at hJC
      obtain ⟨s_a, uₐ, Eb, hka, hla, -, -, hEb, hAt, -, -, hEr⟩ := (cert_entry_at_slot M F U Fx) S A x R s₀ H k w D _ _ E
        hAdvQ hOld hD ((progressCertOn_of_justificationCertOn M F) hJC) hH
      have hJmem : (x.st k w).justified ∈ (x.st k w).tree :=
        (F.nd.nodeInv_justifiedInTree (lem11_node_invariant M F S A x R E k w hwk).1)
      have hEJ : Eb = (x.st k w).justified :=
        hRoots Eb _ ((onHonestChainAt_inHonestTreeBy M F U) S A x R E _ uₐ (M.supportCutoff S.C (s_a + 1)) _ Eb hla
          ((time_mono M) x R hka.le) hEb)
          ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := k) (v := w) hwk le_rfl
            hJmem) hEr.symm
      refine ⟨Eb, ⟨s_a, hs' s_a ⟨_, uₐ, hka, hla⟩, hAt⟩, ?_⟩
      rw [hEJ, hJh]
      omega_nat
    · -- the entry at `h_max − 1` named by the certificate of the block that raised the chain
      obtain ⟨-, ⟨Z, hZ, hZh⟩, -⟩ := (cachesWitnessed_of_exec M F) S A x R E k w
      obtain ⟨Y, hYZ, -, -, -, -, hPC⟩ := (GoldilocksCorrectness.Record.Statements.Routines.lem67_first_advance M F) S.C Z
        (hMax M S.C (x.st k w) - 1) (by omega_nat) (by rw [hZh]; omega_nat)
      have hYT : Y ∈ (x.st k w).tree :=
        (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E k w Z Y hZ hYZ
      obtain ⟨s_a, uₐ, Eb, hka, hla, -, -, -, hAt, -, hEh, -⟩ := (cert_entry_at_slot M F U Fx) S A x R s₀ H k w Y _ _ E
        hAdvQ hOld hYT hPC (by omega_nat)
      exact ⟨Eb, ⟨s_a, hs' s_a ⟨_, uₐ, hka, hla⟩, hAt⟩, by rw [hEh]⟩
  -- the candidate: the later of `B` and `Eb`
  obtain ⟨W, hWc, hBW, hWh⟩ : ∃ W : Block V, OnHonestChainBefore M S A x s₀ s W ∧ B.AncestorEq W ∧
      hMax M S.C (x.st k w) - 1 ≤ (M.chainStateOf S.C W).h := by
    rcases (compatible_iff _ _).1 ((onHonestChainBefore_compatible M F) S A x s₀ s B Eb hChain hB hE) with h | h
    · exact ⟨Eb, hE, h, hEh⟩
    · exact ⟨B, hB, ancestorEq_refl B,
        le_trans hEh ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C h)⟩
  obtain ⟨hWt, hWv⟩ := (proposal_viable_head_at_tick_st M F U) S A x R (M.viewFreeze S.C (s - 1)) s w W _ _ E kw k
    hkw hlt hkwk hwk (hheld W hWc hBW) le_rfl ⟨rfl, rfl⟩ (ancestorEq_trans hRB' hBW) (by rw [hfl]; exact hWh)
  exact ⟨W, (GoldilocksCorrectness.Record.Statements.Routines.mem_voter_block_tree_iff_at S.C _ s W).1 hWt, hWv, hBW⟩

/-- **The voter frame after the hand-over.** The proof; the audited statement is in
`Statements/Executions/HealedVoterFrameStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `i₂`: the step from which the caches are on the
  chain; `H`: the threshold; `s`: the slot of the vote; `w`: the voter.

Roots name blocks until `M.voteTime S.C s`: the proof reads `w`'s state before the vote time of slot
`s` (Lemma 91f, and the entry the certificate names against `w`'s justified block), and the blocks
of the chain `w` holds by the view freeze of slot `s − 1`.

Caches and `hAdvQ` up to the real time of `w`'s tick to the vote time of slot `s`: the proof reads `w`'s state at that tick
(Lemma 91 (d) and (f) there).

Read aloud: after the hand-over, an honest active voter's fork-choice root is compatible with the
honest chain before its slot, and, when the root is a block of that chain or an ancestor of one,
some block of its voter tree that is that block or a descendant of it is a viable head.

 -/
theorem voterFrame_after_handover_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ i₂ H s : ℕ) (w : V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.voteTime S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum of validators have been in the adversary set up to the later of the real time of `w`'s tick to
    -- `M.voteTime S.C s` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time (x.tickStep w (M.voteTime S.C s))) (M.supportCutoff S.C (s₀ + 1))))
    -- the recovery delay after `GST` has elapsed by the view freeze of slot `s − 1`
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C (s - 1))
    -- for every confirmation an updater saved for a slot `μ` before `s − 1` whose updater ticked to
    -- the support cutoff of `μ` more than the recovery delay before the view freeze of slot `s − 1`
    --, some validator active at
    -- the window start, honest at its last step before it, holds it with a compatible finalized
    -- block; that validator is active at every step at a real time from the window start to one
    -- sync delay after it (, applies)
    (hHold : ∀ μ : ℕ, s₀ ≤ μ → μ + 1 < s →
      ∀ u ∈ updaterAt M S A x μ,
      (x.time (x.tickStep u (M.supportCutoff S.C μ)) : ℝ) + max (Δ S) Δs < M.viewFreeze S.C (s - 1) →
      ∀ C : Block V,
      (x.tickOutput u (M.supportCutoff S.C (μ + 1))).savedConfirmation μ = some C →
      ∃ v : V, v ∈ A.activeThroughout x ((M.viewFreeze S.C (s - 1) - max (Δ S) Δs : ℕ) : ℝ)
          (((M.viewFreeze S.C (s - 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) ∧
        v ∉ A.corrupted (x.stepBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs)) ∧
        C ∈ (x.stateBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs) v).tree ∧
        (x.stateBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs) v).finalized.compatible C = true)
    -- every updater of a slot from the healed slot `s₀` to `s − 2` is active for the sync delay after the real time
    -- of its own tick to the support cutoff of the next slot
    (hStay : ∀ σ : ℕ, s₀ ≤ σ → σ + 1 < s → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the caches at every step at a real time after `x[i₂].time`
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₂ < x.time j → x.time j ≤ x.time (x.tickStep w (M.voteTime S.C s)) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    -- the view freeze of slot `s − 1`, where the voter tree is read, is after `x[i₂].time`
    (hs : x.time i₂ < M.viewFreeze S.C (s - 1))
    (hChain : ConfirmationsChainBefore M S A x s₀ s)
    (hw : w ∈ honestActiveAt M S A x s) :
    VoterFrameOnChainAt M S A x s₀ s w := by
  exact (voterFrame_after_handover_core M F U Fx) S A x R GST s₀ i₂ H s w (E.upTo _) hNet hSkew hRedeliver (Sy.upTo _) hΔs
    hRoots hParent hAdvQ hGST hHold hStay hOld hCaches hs hChain hw

/-- **The voter frame after the hand-over.** The proof; the audited statement is in
`Statements/Executions/HealedVoterFrameStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `i₂`: the step from which the caches are on the
  chain; `H`: the threshold; `s`: the slot of the vote; `w`: the voter.

Roots name blocks until `M.voteTime S.C s`: the proof reads `w`'s state before the vote time of slot
`s` (Lemma 91f, and the entry the certificate names against `w`'s justified block), and the blocks
of the chain `w` holds by the view freeze of slot `s − 1`.

It is `voterFrame_after_handover_until` with the caches restricted to the steps it reads.

Read aloud: after the hand-over, an honest active voter's fork-choice root is compatible with the
honest chain before its slot, and, when the root is a block of that chain or an ancestor of one,
some block of its voter tree that is that block or a descendant of it is a viable head.

 -/
theorem voterFrame_after_handover (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ i₂ H s : ℕ) (w : V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.voteTime S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum of validators have been in the adversary set up to the later of the real time of `w`'s tick to
    -- `M.voteTime S.C s` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time (x.tickStep w (M.voteTime S.C s))) (M.supportCutoff S.C (s₀ + 1))))
    -- the recovery delay after `GST` has elapsed by the view freeze of slot `s − 1`
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C (s - 1))
    -- for every confirmation an updater saved for a slot `μ` before `s − 1` whose updater ticked to
    -- the support cutoff of `μ` more than the recovery delay before the view freeze of slot `s − 1`
    --, some validator active at
    -- the window start, honest at its last step before it, holds it with a compatible finalized
    -- block; that validator is active at every step at a real time from the window start to one
    -- sync delay after it (, applies)
    (hHold : ∀ μ : ℕ, s₀ ≤ μ → μ + 1 < s →
      ∀ u ∈ updaterAt M S A x μ,
      (x.time (x.tickStep u (M.supportCutoff S.C μ)) : ℝ) + max (Δ S) Δs < M.viewFreeze S.C (s - 1) →
      ∀ C : Block V,
      (x.tickOutput u (M.supportCutoff S.C (μ + 1))).savedConfirmation μ = some C →
      ∃ v : V, v ∈ A.activeThroughout x ((M.viewFreeze S.C (s - 1) - max (Δ S) Δs : ℕ) : ℝ)
          (((M.viewFreeze S.C (s - 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) ∧
        v ∉ A.corrupted (x.stepBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs)) ∧
        C ∈ (x.stateBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs) v).tree ∧
        (x.stateBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs) v).finalized.compatible C = true)
    -- every updater of a slot from the healed slot `s₀` to `s − 2` is active for the sync delay after the real time
    -- of its own tick to the support cutoff of the next slot
    (hStay : ∀ σ : ℕ, s₀ ≤ σ → σ + 1 < s → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the caches at every step at a real time after `x[i₂].time`
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₂ < x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    -- the view freeze of slot `s − 1`, where the voter tree is read, is after `x[i₂].time`
    (hs : x.time i₂ < M.viewFreeze S.C (s - 1))
    (hChain : ConfirmationsChainBefore M S A x s₀ s)
    (hw : w ∈ honestActiveAt M S A x s) :
    VoterFrameOnChainAt M S A x s₀ s w := by
  exact (voterFrame_after_handover_until M F U Fx) S A x R GST s₀ i₂ H s w E hNet hSkew hRedeliver Sy hΔs hRoots hParent
    hAdvQ hGST hHold hStay hOld (fun j u h₁ _ h₃ => hCaches j u h₁ h₃) hs hChain hw

end GoldilocksCorrectness.Record.Proofs.Executions

