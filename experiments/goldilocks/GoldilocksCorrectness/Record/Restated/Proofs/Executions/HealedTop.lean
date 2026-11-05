module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89HandoverVF
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89Count
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HealedVoterFrame
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HealedChainBefore
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma90Inclusion
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma85
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Unforgeability
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HonestProposalExtension
public import GoldilocksCorrectness.Proofs.Executions.Lemma89HandoverVF
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Count
public import GoldilocksCorrectness.Proofs.Executions.HealedVoterFrame
public import GoldilocksCorrectness.Proofs.Executions.HealedChainBefore
public import GoldilocksCorrectness.Proofs.Executions.Lemma90Inclusion
public import GoldilocksCorrectness.Proofs.Executions.Lemma85
public import GoldilocksCorrectness.Proofs.Executions.Unforgeability
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# HealedTop, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/HealedTop.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: the frames at every slot after the healed
slot, the facts after the hand-over (the root collision, or the healed slot with the facts every
later lemma reads), Lemma 86 (finality safety after healing) and Lemma 90 (the confirmed tip after
healing), each also for the readings up to a time `t`. The page's routine-level theorems are the
facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  dutyWindowStart anchorCW)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_of_anchor one_le_Δ slotStart_eq
  slotStart_mono supportCutoff_eq supportCutoff_mono viewFreeze_eq voteTime_eq voteTime_mono
  voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (anchorCW_eq)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Proofs.Executions (mem_awakeThroughout_of_forall r_lt_of_lt_of_mono)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (OpeningsOutsideWaitsAndWindows Vocab.goldilocks
  acObject fgObject healFrontSlots)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **`GST` is one sync delay before the healed slot's support cutoff.** When `GST ≤ tGAT` and the
slot after `s₀` starts at or after the anchor `anchorCW S tGAT = tGAT + 4Δ(k + 2)`, and the sync delay is at most the
protocol's slow window less three delays and the two clock bounds (whose sum is nonnegative), then
`GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀`. A proof-page helper.

Read aloud: the whole sync window before the healed slot's support cutoff is in the synchronous period. -/
theorem gst_sync_of_anchor (U : UniformSchedule M.toSlotLayout) (S : Setup V) {GST tGAT Δs s₀ : ℕ}
    (hGST : GST ≤ tGAT) {ΔClockAhead ΔClockBehind : ℝ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hAnc : anchorCW S tGAT ≤ M.slotStart S.C (s₀ + 1)) (hAB : 0 ≤ ΔClockAhead + ΔClockBehind) :
    GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀ := by
  obtain ⟨-, hcs, -, hss, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s₀
  -- the sync delay's bound on natural numbers, the two clock bounds' sum being nonnegative
  have hkN : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  rw [anchorCW_eq, Nat.mul_add] at hAnc
  rcases le_total (Δ S) Δs with h | h
  · rw [max_eq_right h] at hkN ⊢; omega
  · rw [max_eq_left h] at hkN ⊢; omega

omit F in
/-- **The catch-up delay's bound gives the sync delay's bound at `max (Δ S) Δw`.** When the
catch-up delay `Δw` is at most the protocol's slow window less three delays,
`Δw + 3 * Δ S ≤ 4 * Δ S * S.C.k`, so is `max (Δ S) Δw`.

Why: when `Δ S ≤ Δw` the maximum is `Δw`; otherwise it is `Δ S`, and `Δ S + 3 * Δ S = 4 * Δ S`,
at most `4 * Δ S * S.C.k` since `S.C.k ≥ 2`.

The variables:
- `S`: the setup; `Δw`: the catch-up delay;
- `hΔw`: the catch-up delay is at most the slow window `4 * Δ S * S.C.k` less three delays.

Read aloud: a catch-up delay that fits in the slow window less three delays gives a sync delay
`max (Δ S) Δw` that fits too. -/
theorem hΔs_of_hΔw (S : Setup V) {Δw : ℕ} (hΔw : Δw + 3 * Δ S ≤ 4 * Δ S * S.C.k) :
    max (Δ S) Δw + 3 * Δ S ≤ 4 * Δ S * S.C.k := by
  have hk : 1 ≤ S.C.k := le_trans (by decide) S.C.k_ge_two
  have h4 : 4 * Δ S * 1 ≤ 4 * Δ S * S.C.k := Nat.mul_le_mul_left (4 * Δ S) hk
  rcases le_total (Δ S) Δw with h | h
  · rw [max_eq_right h]; exact hΔw
  · rw [max_eq_left h]; omega

/-- The old `GST` line of the healed slot from the deadline spelling: `GST ≤ M.voteTime S.C s₀`. -/
theorem gst_le_voteTime_of_sync (U : UniformSchedule M.toSlotLayout) (S : Setup V) {GST Δs s₀ : ℕ}
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) : GST ≤ M.voteTime S.C s₀ := by
  have h1 := le_max_left (Δ S) Δs
  have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s₀
  omega

/-- A proof-page helper.

Read aloud: the recovery delay after `GST` has elapsed by the view freeze of every slot from `s₀` on. -/
theorem gst_sync_le_viewFreeze (U : UniformSchedule M.toSlotLayout) (S : Setup V) {GST Δs s₀ s : ℕ}
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (hs : s₀ ≤ s) :
    GST + max (Δ S) Δs ≤ M.viewFreeze S.C s := by
  have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S hs
  obtain ⟨-, hc, hf, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s
  omega

/-! ## The holder of an old confirmation at the window start -/

/-- **A member of slot `σ` holds the confirmations of the earlier slots, from the vote time of `σ`
to the support cutoff of `σ + 1`.** A proof-page helper.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, its run facts; `E`: the environment facts;
- `s₀`: the first slot of the chain; `σ`: the member's slot; `μ`: the slot of the confirmation;
  `t₀`: the time; `u`: the updater of `μ`; `v`: the member; `C`: the confirmation.

Why: `v` is active through its duty window of `σ`, which covers `t₀`, and outside the adversary set
at the support cutoff of `σ + 1`, so at its last step before `t₀`. `C` is a block of the honest chain
before `σ`, so the voter condition `VoterFrameOnChainAt` at `σ` puts it in `v`'s tree before the vote
time of `σ` (through a viable head of the voter tree when the fork-choice root is `C` or an ancestor of
`C`, and through the root itself, which is in the tree, otherwise); the tree only grows. The updater
condition `UpdaterFinalizedOnChainAt` at `σ` makes `v`'s finalized block before its update compatible
with `C`, and the finalized block before `t₀` is an ancestor of that one.

Read aloud: an honest active voter of `σ` whose voter and updater conditions hold at `σ` holds every
confirmation saved for an earlier slot from `s₀` on, with a compatible finalized block, at every time after
its own vote tick of `σ` and more than `ΔClockAhead` before the support cutoff of `σ + 1`. -/
theorem confirmation_member_holder (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (s₀ σ μ t₀ : ℕ) (u v : V) (C : Block V)
    (hv : v ∈ honestActiveAt M S A x σ) (hs₀μ : s₀ ≤ μ) (hμσ : μ < σ)
    (hu : u ∈ updaterAt M S A x μ)
    (hC : (x.tickOutput u (M.supportCutoff S.C (μ + 1))).savedConfirmation μ = some C)
    (hVF : VoterFrameOnChainAt M S A x s₀ σ v) (hUF : UpdaterFinalizedOnChainAt M S A x s₀ σ v)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    -- `v`'s vote tick is at a real time before `t₀`; `t₀` is more than `ΔClockAhead` before the support cutoff of
    -- `σ + 1`, so before `v`'s update tick (; the second bound read per clock,)
    (h1 : x.time (x.tickStep v (M.voteTime S.C σ)) < t₀)
    (h2 : (t₀ : ℝ) + ΔClockAhead < M.supportCutoff S.C (σ + 1)) :
    v ∈ A.activeAtTime x t₀ ∧ v ∉ A.corrupted (x.stepBefore t₀) ∧
      C ∈ (x.stateBefore t₀ v).tree ∧ (x.stateBefore t₀ v).finalized.compatible C = true := by
  have hΔ := one_le_Δ S
  have hk := S.C.k_ge_two
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hssn : ∀ n : ℕ, M.slotStart S.C n = 4 * Δ S * n := fun n =>
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S n
  have hvtn : ∀ n : ℕ, M.voteTime S.C n = M.slotStart S.C n + Δ S := fun n =>
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S n
  have hscn : ∀ n : ℕ, M.supportCutoff S.C n = M.voteTime S.C n + Δ S := fun n =>
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S n
  have hvtR : ((M.voteTime S.C σ : ℕ) : ℝ) = 4 * Δ S * (σ : ℝ) + Δ S := by rw [hvtn, hssn]; push_cast; ring
  have hc1R : ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) = 4 * Δ S * (σ : ℝ) + 6 * Δ S := by
    rw [hscn, hvtn, hssn]; push_cast; ring
  have hdw := duty_window_start_real S σ
  have hkR : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by
    have : 4 * Δ S * 2 ≤ 4 * Δ S * S.C.k := Nat.mul_le_mul_left _ hk
    exact_mod_cast (by omega : 8 * Δ S ≤ 4 * Δ S * S.C.k)
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  -- `v`'s window of `σ`: its tick `kV` to the vote time of `σ`, its tick `kC` to the support cutoff of `σ + 1`
  have hwW := (honestActiveAt_window M F) S A σ v E hv
  have hwV : v ∈ A.activeThroughoutToTick x (duty_window_start S.C σ) (M.voteTime S.C σ) :=
    (mem_activeThroughoutToTick_of_inside M F) R E hwW (by rw [hvtn]; omega)
      (by rw [hdw, hvtR]; linarith) (by rw [hvtR, hc1R]; linarith)
  obtain ⟨kV, hkV, -⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hwV
    (t₀ := ((M.voteTime S.C σ : ℕ) : ℝ) - ΔClockAhead) (by rw [hdw, hvtR]; linarith)
  rw [(tickStep_eq_of_lbl M) x E hkV] at h1
  have hkVt := (E.tick_active kV v _ hkV).2
  obtain ⟨kC, hkC, -⟩ := Activity.mem_activeThroughoutToTick.1 hwW
  have hkCt := (E.tick_active kC v _ hkC).2
  have ht1 : 1 ≤ t₀ := by
    have : (0 : ℝ) < t₀ := lt_of_le_of_lt ((time_nonneg M) x R kV) h1
    exact_mod_cast this
  obtain ⟨hk1, hk2⟩ := (stepBefore_time M) x R E ht1
  -- `v` is active in the configuration in force at `t₀`
  have hact : v ∈ A.activeThroughout x (t₀ : ℝ) (t₀ : ℕ) :=
    (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E hwW
      (by rw [hdw]; rw [hvtR] at hkVt; linarith) h2
  have hvk : v ∈ A.active (x.stepBefore t₀) := Activity.mem_activeThroughout.1 hact _ hk1.le hk2
  have hkVb : kV < x.stepBefore t₀ := by
    refine ((lt_stepBefore_iff M) x R E).2 ?_
    rw [R.time_keep kV (by rw [hkV]; exact nofun)]; exact h1
  have hbC : x.stepBefore t₀ < kC := (lt_of_time_lt M) x R (by linarith)
  have hCon : OnHonestChainBefore M S A x s₀ σ C := ⟨μ, hμσ, hs₀μ, u, hu, C, hC, ancestorEq_refl C⟩
  refine ⟨Activity.mem_activeAtTime_of_mem_activeThroughout hact le_rfl le_rfl,
    Activity.not_mem_corrupted_of_mem_active hvk, ?_, ?_⟩
  · -- `C` is in `v`'s tree at its vote tick (the voter condition), so before `t₀`
    show C ∈ (x.st (x.stepBefore t₀) v).tree
    refine (mem_T_mono M F) x R E v hkVb.le ?_
    obtain ⟨hcomp, hview⟩ := hVF C hCon kV hkV
    have hInv : M.nodeInv S.C S.P S.X (x.st kV v) :=
      (lem11_node_invariant M F S A x R E kV v (E.not_mem_corrupted_of_tick hkV)).1
    rcases (compatible_iff _ _).1 hcomp with hrC | hCr
    · obtain ⟨W, hW, -, hCW⟩ := hview hrC
      have hWT : W ∈ (x.st kV v).tree :=
        (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hW.1).1
      exact (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ v W C hWT hCW
    · -- the fork-choice root is in the tree (the justified or the finalized block)
      have hroot : (M.fg_to_ac (x.st kV v)).fc_root ∈ (x.st kV v).tree := by
        rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F) (x.st kV v), F.ndAdded.get_fc_root_eq hInv]
        split
        · exact F.nd.nodeInv_justifiedInTree hInv
        · exact F.nd.nodeInv_finalized_mem_tree hInv
      exact (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ v _ C hroot hCr
  · -- the finalized block before `t₀` is an ancestor of the one at the update tick (the updater condition)
    show (x.st (x.stepBefore t₀) v).finalized.compatible C = true
    have hUC := hUF C hCon
    unfold Trace.tickInput at hUC
    rw [(tickStep_eq_of_lbl M) x E hkC] at hUC
    exact GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible
      ((F_ancestorEq_of_le M F) x R E v hbC.le) hUC

/-- **A holder of every old confirmation at the window start of slot `s`.** The line `hHold` of
`chain_block_held_before_freeze`, from the voter and updater conditions at the slots
from `s₀ + 1` to `s − 1` and the committees' sleepiness. A proof-page helper.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, its run facts; `E`: the environment
  facts;
- `s₀`: the first slot of the chain; `s`: the voter's slot; `anchor`: the time from which the
  committees' sleepiness holds; `Δs`: the sync delay.

Why: write `t₀ := M.viewFreeze S.C (s - 1) - max (Δ S) Δs`, the window start. For a slot `μ` whose updater
`u` ticked to `M.supportCutoff S.C μ` at a real time before `t₀`: when `t₀` is before the support cutoff of `μ + 1` and before `u`'s tick to
it, the updater itself holds its confirmation (`confirmation_updater_holder`); otherwise the slot `σ` with
`M.voteTime S.C σ ≤ t₀ ≤ M.supportCutoff S.C (σ + 1)` lies strictly between `μ` and `s`, its committee
has an honest active member (`committee_majority_of_sleepiness`), and that member holds it
(`confirmation_member_holder`).

Read aloud: when the voter and updater conditions hold at every slot after `s₀` and before `s`, every
confirmation an updater saved for a slot `μ` from `s₀` on, before `s − 1`, whose updater ticked to
the support cutoff of `μ` more than the recovery delay before the view freeze of slot `s − 1`, is held at the window start by a
validator active then, honest at its last step before it, with a compatible finalized block. -/
theorem confirmation_holder_at_window_start (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the sum of the two clock bounds is less than `Δ S`
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
 (s₀ s anchor : ℕ) (Δs : ℕ)
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C s)) (hAnchor : anchor ≤ M.slotStart S.C (s₀ + 1))
    (hFrames : ∀ σ : ℕ, s₀ < σ → σ < s →
      (∀ w ∈ honestActiveAt M S A x σ, VoterFrameOnChainAt M S A x s₀ σ w) ∧
      (∀ v ∈ updaterAt M S A x σ, UpdaterFinalizedOnChainAt M S A x s₀ σ v))
    -- every updater of a slot from the healed slot `s₀` on, before `s`, is active for the sync delay after the
    -- real time of its own tick to the support cutoff of the next slot
    (hStay : ∀ σ : ℕ, s₀ ≤ σ → σ < s → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs)) :
    ∀ μ : ℕ, s₀ ≤ μ → μ + 1 < s →
      ∀ u ∈ updaterAt M S A x μ,
      (x.time (x.tickStep u (M.supportCutoff S.C μ)) : ℝ) + max (Δ S) Δs < M.viewFreeze S.C (s - 1) →
      ∀ C : Block V,
      (x.tickOutput u (M.supportCutoff S.C (μ + 1))).savedConfirmation μ = some C →
      ∃ v : V, v ∈ A.activeThroughout x ((M.viewFreeze S.C (s - 1) - max (Δ S) Δs : ℕ) : ℝ)
          (((M.viewFreeze S.C (s - 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) ∧
        v ∉ A.corrupted (x.stepBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs)) ∧
        C ∈ (x.stateBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs) v).tree ∧
        (x.stateBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs) v).finalized.compatible C = true := by
  intro μ hμ₀ hμs u hu hrange C hC
  -- a tick to a value at most the duty window's start of slot `n + 1` is at a real time at most
  -- `ΔClockBehind` after the start of slot `n` (`S.C.k ≥ 2`)
  have hdws : ∀ (w : V) (n k c : ℕ), (c : ℤ) ≤ duty_window_start S.C (n + 1) → x.lbl k = Event.tick w c →
      x.time k ≤ (M.slotStart S.C n : ℝ) + ΔClockBehind := by
    intro w n k c hc hl
    have h1 : duty_window_start S.C (n + 1) ≤ ((M.dutyWindowStart S.C (n + 1) : ℕ) : ℤ) :=
      (GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_le_dutyWindowStart M.toSlotLayout
        F.sched U) S (n + 1)
    have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_le_slotStart M.toSlotLayout
      F.sched) S n
    have h5 : c ≤ M.dutyWindowStart S.C (n + 1) := by exact_mod_cast le_trans hc h1
    have h3 : c ≤ M.slotStart S.C n := le_trans h5 h2
    have h4 : (c : ℝ) ≤ M.slotStart S.C n := by exact_mod_cast h3
    have := (E.tick_active k w c hl).2.2
    linarith
  have hΔ := one_le_Δ S
  have hmx1 := le_max_left (Δ S) Δs
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  -- the recovery delay is at most the view freeze: the antecedent, the tick's real time being nonnegative
  have hmxvf : max (Δ S) Δs ≤ M.viewFreeze S.C (s - 1) := by
    have h0 : (0 : ℝ) ≤ x.time (x.tickStep u (M.supportCutoff S.C μ)) := by
      rw [← R.time_zero]; exact R.time_mono (Nat.zero_le _)
    have : ((max (Δ S) Δs : ℕ) : ℝ) < M.viewFreeze S.C (s - 1) := by linarith
    exact_mod_cast this.le
  obtain ⟨-, hcμ, -, hsμ, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S μ
  obtain ⟨hvμ1, hcμ1, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (μ + 1)
  obtain ⟨-, -, hfs1, hss1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s - 1)
  rw [show s - 1 + 1 = s by omega] at hss1
  -- the step of a tick to `c` is at a real time at most `c + ΔClockBehind` (the trace's start when there is none)
  have htick_le : ∀ (w : V) (c : ℕ), x.time (x.tickStep w c) ≤ (c : ℝ) + ΔClockBehind := by
    intro w c
    by_cases h : ∃ i : ℕ, x.lbl i = Event.tick w c
    · obtain ⟨i, hi⟩ := h
      rw [(tickStep_eq_of_lbl M) x E hi]
      exact (E.tick_active i w c hi).2.2
    · unfold Trace.tickStep
      rw [dif_neg h, R.time_zero]
      have := Nat.cast_nonneg (α := ℝ) c
      linarith
  -- a validator active up to its tick to `c` ticks to `c` at a real time at least `c − ΔClockAhead`
  have htick_ge : ∀ (w : V) (a : ℤ) (c : ℕ), w ∈ A.activeThroughoutToTick x a c →
      (c : ℝ) - ΔClockAhead ≤ x.time (x.tickStep w c) := by
    intro w a c hw
    obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hw
    rw [(tickStep_eq_of_lbl M) x E hk']
    exact (E.tick_active k' w c hk').2.1
  generalize ht₀ : M.viewFreeze S.C (s - 1) - max (Δ S) Δs = t₀
  by_cases hU : t₀ < M.supportCutoff S.C (μ + 1) ∧
      (t₀ : ℝ) < x.time (x.tickStep u (M.supportCutoff S.C (μ + 1)))
  · -- the updater itself, between its two ticks: its tick to the support cutoff of `μ` is before `t₀`
    -- by the antecedent
    have hU1 : x.time (x.tickStep u (M.supportCutoff S.C μ)) < t₀ := by
      rw [← ht₀, Nat.cast_sub hmxvf]
      push_cast at hrange ⊢
      linarith
    obtain ⟨-, h2, h3, h4⟩ := (confirmation_updater_holder M F U) S A x R E μ t₀ u C hu hC hSkew hU1 hU.2
    -- `u` ticked to the support cutoff of `μ` (`saved_confirmation_held_compatible_supportCutoff`), so `t₀` is after
    -- every tick of `u` to a value at most the duty window's start of slot `μ + 1`
    obtain ⟨hkμl, -, -⟩ := (saved_confirmation_held_compatible_supportCutoff M F U) S A x R μ u C E hSkew
      ((updaterAt_window M F) S A μ u E hu) hC
    have hkμt := (E.tick_active _ u _ hkμl).2.1
    have hcμR : ((M.supportCutoff S.C μ : ℕ) : ℝ) = (M.slotStart S.C μ : ℝ) + 2 * Δ S := by exact_mod_cast hcμ
    refine ⟨u, (activeThroughout_of_toTick_of_stay M F) R ((updaterAt_window M F) S A μ u E hu) ?_ ?_ ?_, h2, h3, h4⟩
    · intro k c hc hl
      have := hdws u μ k c hc hl
      linarith
    · intro k' hk'
      rw [← (tickStep_eq_of_lbl M) x E hk']
      exact hU.2.le
    · intro k' hk'
      rw [← (tickStep_eq_of_lbl M) x E hk']
      exact hStay μ hμ₀ (by omega) u hu
  · -- a member of the latest slot whose members have all ticked to its vote time before `t₀`
    have hlo : ((M.supportCutoff S.C (μ + 1) : ℕ) : ℝ) - ΔClockAhead ≤ t₀ := by
      rcases not_and_or.1 hU with h | h
      · push Not at h
        have : ((M.supportCutoff S.C (μ + 1) : ℕ) : ℝ) ≤ t₀ := by exact_mod_cast h
        linarith
      · push Not at h
        have := htick_ge u _ _ ((updaterAt_window M F) S A μ u E hu)
        linarith
    have hcμ1R : ((M.supportCutoff S.C (μ + 1) : ℕ) : ℝ) = (M.slotStart S.C (μ + 1) : ℝ) + 2 * Δ S := by
      exact_mod_cast hcμ1
    have hgt : M.slotStart S.C (μ + 1) + Δ S < t₀ := by
      have h : ((M.slotStart S.C (μ + 1) + Δ S : ℕ) : ℝ) < t₀ := by push_cast; linarith
      exact_mod_cast h
    obtain ⟨hσ1, hσ2⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_div_le M.toSlotLayout F.sched U) S
      (t₀ - Δ S)
    generalize (t₀ - Δ S) / (4 * Δ S) = σ at hσ1 hσ2
    obtain ⟨hvσ, hcσ, -, hsσ, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
    obtain ⟨-, hcσ1, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
    have hσs : σ < s := by
      rcases Nat.lt_or_ge σ s with h | h
      · exact h
      · have := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S h
        omega
    obtain ⟨σ', hμσ', hσ'σ, h1R, h2N, h2R⟩ : ∃ σ' : ℕ, μ < σ' ∧ σ' ≤ σ ∧
        ((M.voteTime S.C σ' : ℕ) : ℝ) + ΔClockBehind < t₀ ∧ t₀ < M.supportCutoff S.C (σ' + 1) ∧
        (t₀ : ℝ) + ΔClockAhead < M.supportCutoff S.C (σ' + 1) := by
      by_cases hc : ((M.voteTime S.C σ : ℕ) : ℝ) + ΔClockBehind < t₀
      · refine ⟨σ, ?_, le_rfl, hc, by omega, ?_⟩
        · rcases Nat.lt_or_ge μ σ with h | h
          · exact h
          · have := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
              (show σ + 1 ≤ μ + 1 by omega)
            omega
        · have h : t₀ < M.slotStart S.C (σ + 1) + Δ S := by omega
          have hR : (t₀ : ℝ) < (M.slotStart S.C (σ + 1) : ℝ) + Δ S := by exact_mod_cast h
          have e : ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) = (M.slotStart S.C (σ + 1) : ℝ) + 2 * Δ S := by
            exact_mod_cast hcσ1
          rw [e]
          linarith
      · push Not at hc
        have hvσR : ((M.voteTime S.C σ : ℕ) : ℝ) = (M.slotStart S.C σ : ℝ) + Δ S := by exact_mod_cast hvσ
        have hσμ : μ + 1 < σ := by
          have hg : ((M.slotStart S.C (μ + 1) + Δ S : ℕ) : ℝ) < t₀ := by exact_mod_cast hgt
          push_cast at hg
          have h' : M.slotStart S.C (μ + 1) < M.slotStart S.C σ := by
            have : ((M.slotStart S.C (μ + 1) : ℕ) : ℝ) < M.slotStart S.C σ := by linarith
            exact_mod_cast this
          rcases Nat.lt_or_ge (μ + 1) σ with h | h
          · exact h
          · have := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S h
            omega
        obtain ⟨hvσm, -, -, hsσm, -⟩ :=
          (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ - 1)
        rw [show σ - 1 + 1 = σ by omega] at hsσm
        have hcσR : ((M.supportCutoff S.C σ : ℕ) : ℝ) = (M.slotStart S.C σ : ℝ) + 2 * Δ S := by exact_mod_cast hcσ
        refine ⟨σ - 1, by omega, by omega, ?_, ?_, ?_⟩
        · have e : ((M.voteTime S.C (σ - 1) : ℕ) : ℝ) + 4 * Δ S = M.voteTime S.C σ := by
            exact_mod_cast (show M.voteTime S.C (σ - 1) + 4 * Δ S = M.voteTime S.C σ by omega)
          have h : ((M.voteTime S.C σ : ℕ) : ℝ) ≤ t₀ := by
            exact_mod_cast (show M.voteTime S.C σ ≤ t₀ by omega)
          linarith
        · rw [show σ - 1 + 1 = σ by omega]
          have : (t₀ : ℝ) < M.supportCutoff S.C σ := by rw [hcσR]; linarith
          exact_mod_cast this
        · rw [show σ - 1 + 1 = σ by omega, hcσR]
          linarith
    have hσ's : σ' < s := by omega
    have hAnσ : anchor ≤ M.slotStart S.C (σ' + 1) :=
      le_trans hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
    have hK := (committee_majority_of_sleepiness M F) S A x anchor σ' hSleepK hAnσ
      ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))
    obtain ⟨v, hv⟩ := Finset.card_pos.1 (show 0 < (S.P.committee σ' ∩ honestActiveAt M S A x σ').card by omega)
    have hvH := (Finset.mem_inter.1 hv).2
    obtain ⟨hVF, hUF⟩ := hFrames σ' (by omega) hσ's
    have hvU := (honestActiveAt_subset_updaterAt M F) S A x R E σ' hvH
    obtain ⟨-, h2, h3, h4⟩ := (confirmation_member_holder M F U) S A x R E s₀ σ' μ t₀ u v C hvH hμ₀ hμσ' hu hC
      (hVF v hvH) (hUF v hvU) hSkew (lt_of_le_of_lt (htick_le v _) h1R) h2R
    obtain ⟨hvσ', -, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ'
    have hvσ'R : ((M.voteTime S.C σ' : ℕ) : ℝ) = (M.slotStart S.C σ' : ℝ) + Δ S := by exact_mod_cast hvσ'
    refine ⟨v, (activeThroughout_of_toTick_of_stay M F) R ((updaterAt_window M F) S A σ' v E hvU) ?_ ?_ ?_, h2, h3, h4⟩
    · intro k c hc hl
      have := hdws v σ' k c hc hl
      linarith
    · intro k' hk'
      have := (E.tick_active k' v _ hk').2.1
      linarith
    · intro k' hk'
      rw [← (tickStep_eq_of_lbl M) x E hk']
      exact hStay σ' (by omega) hσ's v hvU

/-- **The holder at the window start, under the frames' premises read up to `t`.** `confirmation_holder_at_window_start`
at a slot `s` whose support cutoff is at most `t`, with the committee sleepiness and the row `hStay` read up to `t`, as
`frames_after_healed_slot_until` has them: its conclusion is the premise `hHold` of the voter frame
`voterFrame_after_handover_until` at `s`. A proof-page helper, the supply of `hHold` in
`frames_after_healed_slot_until`'s body.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, its run facts; `E`: the environment facts;
- `s₀`: the first slot of the chain; `s`: the voter's slot; `anchor`: the time from which the committees' sleepiness
  holds; `t`: the time up to which the premises are read; `Δs`: the sync delay.

Why: the sleepiness up to `t` gives it up to the support cutoff of `s` (`CommitteeSleepinessUntil.mono`); a slot
`σ < s` has its update, the support cutoff of `σ + 1`, at most the support cutoff of `s`, so at most `t`.

Read aloud: when the voter and updater conditions hold at every slot after `s₀` and before `s`, and the support cutoff
of `s` is at most `t`, every confirmation an updater saved for a slot `μ` from `s₀` on, before `s − 1`, whose updater
ticked to the support cutoff of `μ` more than the recovery delay before the view freeze of slot `s − 1`, is held at the
window start by a validator active through the sync delay after it, honest at its last step before it, with a
compatible finalized block. -/
theorem confirmation_holder_at_window_start_until (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the sum of the two clock bounds is less than `Δ S`
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (s₀ s anchor t : ℕ) (Δs : ℕ)
    (hSleepK : CommitteeSleepinessUntil M S A x anchor t) (hAnchor : anchor ≤ M.slotStart S.C (s₀ + 1))
    -- the support cutoff of `s` is at most `t`
    (hst : M.supportCutoff S.C s ≤ t)
    (hFrames : ∀ σ : ℕ, s₀ < σ → σ < s →
      (∀ w ∈ honestActiveAt M S A x σ, VoterFrameOnChainAt M S A x s₀ σ w) ∧
      (∀ v ∈ updaterAt M S A x σ, UpdaterFinalizedOnChainAt M S A x s₀ σ v))
    -- every updater of a slot from the healed slot `s₀` on, whose update is at most `t`, is active for the
    -- sync delay after the real time of its own tick to the support cutoff of the next slot
    --
    (hStay : ∀ σ : ℕ, s₀ ≤ σ → M.supportCutoff S.C (σ + 1) ≤ t → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs)) :
    ∀ μ : ℕ, s₀ ≤ μ → μ + 1 < s →
      ∀ u ∈ updaterAt M S A x μ,
      (x.time (x.tickStep u (M.supportCutoff S.C μ)) : ℝ) + max (Δ S) Δs < M.viewFreeze S.C (s - 1) →
      ∀ C : Block V,
      (x.tickOutput u (M.supportCutoff S.C (μ + 1))).savedConfirmation μ = some C →
      ∃ v : V, v ∈ A.activeThroughout x ((M.viewFreeze S.C (s - 1) - max (Δ S) Δs : ℕ) : ℝ)
          (((M.viewFreeze S.C (s - 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) ∧
        v ∉ A.corrupted (x.stepBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs)) ∧
        C ∈ (x.stateBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs) v).tree ∧
        (x.stateBefore (M.viewFreeze S.C (s - 1) - max (Δ S) Δs) v).finalized.compatible C = true :=
  (confirmation_holder_at_window_start M F U) S A x R E hSkew s₀ s anchor Δs (CommitteeSleepinessUntil.mono M hSleepK hst) hAnchor hFrames
    (fun σ h1 h2 u hu => hStay σ h1
      (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (show σ + 1 ≤ s by omega)) hst) u hu)

/-- **Kit fact, an honest active validator of a slot ticks to its vote time.** Every validator of
`honestActiveAt M S A x (s' + 1)` has a tick to the vote time of slot `s' + 1`: it is active from the duty
window's start of the slot to its tick to the support cutoff of the next slot, and the vote time is inside
that window by more than the two clock bounds (`mem_activeThroughoutToTick_of_inside`). `lem81_inv_before`'s
base-case reading, for any slot.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, its run facts; `s'`: the slot before; `w`: the
  validator.

Read aloud: an honest active validator of a slot takes the tick to that slot's vote time. -/
theorem tick_voteTime_of_honestActiveAt_succ (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (s' : ℕ) (w : V)
    (hw : w ∈ honestActiveAt M S A x (s' + 1)) :
    ∃ k : ℕ, x.lbl k = Event.tick w (M.voteTime S.C (s' + 1)) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  obtain ⟨hv1, -, -, hs1, -, -, -⟩ := (slot_times M F U) S (s' + 1)
  obtain ⟨-, hc2, -, -, -, -, -⟩ := (slot_times M F U) S (s' + 1 + 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s'
  obtain ⟨-, -, -, hs0, -, hk8, -⟩ := (slot_times M F U) S s'
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  have hv1R : ((M.voteTime S.C (s' + 1) : ℕ) : ℝ) = 4 * Δ S * s' + 5 * Δ S := by
    rw [hv1, hs0, hss]; push_cast; ring
  have hc2R : ((M.supportCutoff S.C (s' + 1 + 1) : ℕ) : ℝ) = 4 * Δ S * s' + 10 * Δ S := by
    rw [hc2, hs1, hs0, hss]; push_cast; ring
  have hdw1 := duty_window_start_real S (s' + 1)
  push_cast at hdw1
  have h1 : 1 ≤ M.voteTime S.C (s' + 1) := by omega
  have hr := (mem_activeThroughoutToTick_of_inside M F) R E ((honestActiveAt_window M F) S A (s' + 1) w E hw) h1
    (by rw [hdw1, hv1R]; linarith) (by rw [hv1R, hc2R]; linarith)
  obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 hr
  exact ⟨k, hk⟩

/-- **Kit fact, the votes clause at the slot after `s'`, from the frames up to it.** Under
`lem81_inv_before`'s premises with the voter frames at the slots from `s₀ + 1` to `s' + 1` and the updater
frames at the slots from `s₀ + 1` to `s'`: every Goldfish vote an honest active validator of slot `s' + 1`
sends at its tick to the vote time extends every block on the honest chain before `s' + 1`. The first clause
of `ChainInvFor` at slot `s' + 1`, which `frames_after_healed_slot_until` needs before it holds the updater
frames at `s' + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, its run facts; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee sleepiness holds;
  `s'`: the slot before the votes' slot; `B₀`: the block every updater of slot `s₀` saved.

Why: `votes_clause_step` at `s'`, over the family of blocks that are `B₀` or an ancestor of it when `s' = s₀`
(the base invariants of `lem81_inv_before`), and over the honest chain before `s'` otherwise
(`lem81_inv_before` at `n := s' + 1`, the confirmations of slot `s'` extending it by
`chainInvFor_updater_confirmation` at the updater frames of `s'`); its voter frame input is the voter frame at
`s' + 1` read at each voter's tick to the vote time.

Read aloud: the honest votes of slot `s' + 1` extend the honest chain before `s' + 1`, once the frames up to
`s' + 1` hold for the voters and up to `s'` for the updaters. -/
theorem votes_clause_after_healed_slot (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor s' : ℕ) (B₀ : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s' + 1)))
    -- roots name blocks up to the real time of every validator's tick to a clock value at most the support cutoff of
    -- slot `s' + 1`
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s' + 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s' + 1 + 1)))
    (hAnchor : anchor ≤ M.slotStart S.C (s₀ + 1))
    (hB₀slot : s₀ ≤ B₀.slot)
    (hBase : HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀)
    (hBaseSaved : ∀ v ∈ updaterAt M S A x s₀,
      (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀)
    (hs' : s₀ ≤ s')
    (hVoterFrame : ∀ s : ℕ, s₀ < s → s ≤ s' + 1 → ∀ w ∈ honestActiveAt M S A x s,
      VoterFrameOnChainAt M S A x s₀ s w)
    (hUpdaterFrame : ∀ s : ℕ, s₀ < s → s ≤ s' → ∀ v ∈ updaterAt M S A x s,
      UpdaterFinalizedOnChainAt M S A x s₀ s v) :
    ∀ C : Block V, OnHonestChainBefore M S A x s₀ (s' + 1) C →
      ∀ u ∈ honestActiveAt M S A x (s' + 1), ∀ vote : GoldfishVote V,
        (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s' + 1)) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
        ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).tree,
          vote = GoldfishVote.mk u (s' + 1) H_u.root ∧ C.AncestorEq H_u := by
  have hcm : ∀ a b : ℕ, a ≤ b → M.supportCutoff S.C a ≤ M.supportCutoff S.C b := fun a b h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h
  have hOwner : VotesCastByOwner M A x := (votesCastByOwner_of_unforgeability M F) S A x R E
  have hAnch : ∀ s : ℕ, s₀ ≤ s → anchor ≤ M.slotStart S.C (s + 1) := fun s hs =>
    le_trans hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
  have hCom : ∀ s : ℕ, s₀ ≤ s → s ≤ s' + 1 →
      |S.P.committee s| < 2 * |S.P.committee s ∩ honestActiveAt M S A x s| := fun s hs hsn =>
    (committee_majority_of_sleepiness M F) S A x anchor s hSleepK (hAnch s hs) (hcm _ _ (by omega))
  have hGSTs : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s' := le_trans hGST (hcm _ _ hs')
  -- the family at slot `s'`: its invariants, and the confirmations of slot `s'` extending it
  obtain ⟨𝓒, h𝓒in, h𝓒out, hInv, hLocks, hConfExt⟩ : ∃ 𝓒 : Block V → Prop,
      (∀ C : Block V, 𝓒 C → OnHonestChainBefore M S A x s₀ (s' + 1) C) ∧
      (∀ C : Block V, OnHonestChainBefore M S A x s₀ s' C → 𝓒 C) ∧
      ChainInvFor M S A x (honestActiveAt M S A x s') 𝓒 s' ∧
      (∀ u ∈ honestActiveAt M S A x s', LiveLocksOnFamilyAt M S A x 𝓒 s' u) ∧
      (∀ C : Block V, 𝓒 C → ∀ v ∈ updaterAt M S A x s', ∀ C' : Block V,
        (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' → C.AncestorEq C') := by
    rcases Nat.eq_or_lt_of_le hs' with heq | hlt
    · -- at the healed slot: the blocks that are `B₀` or an ancestor of it (`lem81_inv_before`'s base invariants)
      rw [← heq]
      obtain ⟨u₀, hu₀⟩ : (S.P.committee s₀ ∩ honestActiveAt M S A x s₀).Nonempty :=
        Finset.card_pos.1 (by have := hCom s₀ le_rfl (by omega); omega)
      have hv₀ : u₀ ∈ updaterAt M S A x s₀ :=
        (honestActiveAt_subset_updaterAt M F) S A x R E s₀ (Finset.mem_inter.1 hu₀).2
      refine ⟨fun D => D.AncestorEq B₀,
        fun C hC => ⟨s₀, Nat.lt_succ_self s₀, le_rfl, u₀, hv₀, B₀, hBaseSaved u₀ hv₀, hC⟩,
        fun C ⟨σ, hσ, hσ₀, _⟩ => absurd hσ₀ (by omega),
        fun C hC => (honestChainExtends_of_ancestorEq M F) S A x _ B₀ C s₀ hC hBase,
        fun u hu n₃ sent₃ hrun hA => (liveLocksOnFamilyAt_base M F U) S A x R s₀ B₀ u n₃ E
          hB₀slot ((locksRevoked_of_voteTime_outcome M F U) S A x R E (s₀ + 1) u n₃ sent₃ hrun hA)
          (hBase.2.1 u hu n₃ sent₃ hrun hA), ?_⟩
      intro C hC v hv C' hC'
      rw [hBaseSaved v hv] at hC'
      cases hC'
      exact hC
    · -- after it: the honest chain before `s'`
      obtain ⟨hInv, hLocks⟩ := (lem81_inv_before M F U) S A x R GST s₀ anchor (s' + 1) B₀ E hNet hSkew hRedeliver Sy
        hΔs ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
          (by exact_mod_cast hcm _ _ (by omega)) hRoots)
        (fun k u c hk hc => hRootsTick k u c hk (le_trans hc (hcm _ _ (by omega))))
        hParent hOwner hGST (CommitteeSleepinessUntil.mono M hSleepK (hcm _ _ (by omega))) hAnchor hB₀slot hBase
        hBaseSaved (fun s h1 h2 => hVoterFrame s h1 (by omega)) (fun s h1 h2 => hUpdaterFrame s h1 (by omega))
        s' hlt (Nat.lt_succ_self s')
      refine ⟨OnHonestChainBefore M S A x s₀ s', fun C ⟨σ, hσ, hAt⟩ => ⟨σ, by omega, hAt⟩, fun C hC => hC, hInv,
        hLocks, ?_⟩
      intro C hC v hv C' hC'
      exact (chainInvFor_updater_confirmation M F U) S A x R GST s' (honestActiveAt M S A x s') _ v E hNet hSkew
        hRedeliver Sy hΔs (fun k u c hk hc => hRootsTick k u c hk (le_trans hc (hcm _ _ (Nat.le_succ s')))) hParent
        hOwner hGSTs (subset_refl _) (hCom s' hs' (by omega)) hInv hv (hUpdaterFrame s' hlt le_rfl v hv) C hC C' hC'
  -- the votes clause of the chain step at `s'`, with the voter frames at `s' + 1` read at the voters' ticks
  have h := (votes_clause_step M F U) S A x R GST s' (honestActiveAt M S A x s') (honestActiveAt M S A x (s' + 1))
    (updaterAt M S A x s') 𝓒 E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent hOwner hGSTs
    (subset_refl _) (subset_refl _) (subset_refl _)
    ((honestActiveAt_succ_subset_updaterAt M F U) S A s' R E hSkew)
    (hCom s' hs' (by omega)) (hCom (s' + 1) (by omega) le_rfl) hInv
    (fun u hu => (mem_honestActiveAt_or_lockFree M F U) S A s' u R E hSkew hu) hLocks hConfExt
    (fun C hC w hw => by
      have hC' : OnHonestChainBefore M S A x s₀ (s' + 1) C := by
        rcases hC with hC | ⟨v, hv, C', hsv, hCC'⟩
        · exact h𝓒in C hC
        · exact ⟨s', Nat.lt_succ_self s', hs', v, hv, C', hsv, hCC'⟩
      obtain ⟨k, hk⟩ := (tick_voteTime_of_honestActiveAt_succ M F U) S A x R E hSkew s' w hw
      have hti : x.tickInput w (M.voteTime S.C (s' + 1)) = x.st k w := by
        unfold Trace.tickInput
        rw [(tickStep_eq_of_lbl M) x E hk]
      rw [hti]
      exact hVoterFrame (s' + 1) (by omega) le_rfl w hw C hC' k hk)
  intro C hC u hu vote hsend
  refine h C ?_ u hu vote hsend
  obtain ⟨σ, hσ, hσ₀, v, hv, C', hC', hCC'⟩ := hC
  rcases Nat.lt_or_ge σ s' with hlt | hge
  · exact Or.inl (h𝓒out C ⟨σ, hlt, hσ₀, v, hv, C', hC', hCC'⟩)
  · obtain rfl : σ = s' := by omega
    exact Or.inr ⟨v, hv, C', hC', hCC'⟩

/-! ## The frames at every slot after the healed slot -/

/-- **Kit fact, the frames at one slot after the healed slot.** Under the premises of
`frames_after_healed_slot_until`: at every slot `s > s₀` whose support cutoff plus `ΔClockBehind` is at
most `t`, with committee sleepiness read up to the support cutoff of slot `s + 1`, every honest active
validator of `s` has its voter frame, and every updater of `s` whose tick to the support cutoff of slot
`s + 1` is at a real time at most `t` has its updater frame. The induction of
`frames_after_healed_slot_until`'s proof, stated on its own so that `healed_handover_facts_until`'s
proof reads it at a slot whose next support cutoff is after `t`.

Why: by strong induction on the slot, as `frames_after_healed_slot_until`'s proof.

The variables: as in `frames_after_healed_slot_until`.

Read aloud: the phase's frames at a slot `s`, when `s`'s own support cutoff is one clock bound before
`t` and committee sleepiness holds up to the next one. -/
theorem frames_at_slot_after_healed_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ s_m i₂ H anchor t : ℕ) (B₀ : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x t)
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) t)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hSleepK : CommitteeSleepinessUntil M S A x anchor t)
    -- every updater of a slot from the healed slot `s₀` on, whose update is at most `t`, is active for the
    -- sync delay after the real time of its own tick to the support cutoff of the next slot
    --
    (hStay : ∀ σ : ℕ, s₀ ≤ σ → M.supportCutoff S.C (σ + 1) ≤ t → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hAnchor : anchor ≤ M.slotStart S.C (s₀ + 1))
    (hB₀slot : s₀ ≤ B₀.slot)
    (hBase : HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀)
    (hBaseSaved : ∀ v ∈ updaterAt M S A x s₀,
      (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hi₂ : x.time i₂ < M.viewFreeze S.C s_m)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₂ ≤ x.time j → x.time j ≤ t →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st (j + 1) u))
    (hPhase : ∀ s : ℕ, s₀ < s → s < s_m →
      (∀ w ∈ roundMembers M S A x (s + 1), VoterFrameOnChainAt M S A x s₀ s w) ∧
      (∀ v ∈ updaterAt M S A x s, UpdaterFinalizedOnChainAt M S A x s₀ s v))
    (hLast : ∀ w : V, w ∉ A.corruptedAtTime x (M.voteTime S.C s_m) →
      VoterFrameOnChainAt M S A x s₀ s_m w)
    :
    ∀ s : ℕ, s₀ < s → ((M.supportCutoff S.C s : ℕ) : ℝ) + ΔClockBehind ≤ t →
      CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s + 1)) →
      (∀ w ∈ honestActiveAt M S A x s, VoterFrameOnChainAt M S A x s₀ s w) ∧
      (∀ v ∈ updaterAt M S A x s, x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) ≤ t →
        UpdaterFinalizedOnChainAt M S A x s₀ s v) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hcm : ∀ a b : ℕ, a ≤ b → M.supportCutoff S.C a ≤ M.supportCutoff S.C b := fun a b h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h
  -- the slot times, as reals
  have hT : ∀ s : ℕ, ((M.voteTime S.C s : ℕ) : ℝ) = M.slotStart S.C s + Δ S ∧
      ((M.supportCutoff S.C s : ℕ) : ℝ) = M.slotStart S.C s + 2 * Δ S ∧
      ((M.viewFreeze S.C s : ℕ) : ℝ) = M.slotStart S.C s + 3 * Δ S ∧
      ((M.slotStart S.C (s + 1) : ℕ) : ℝ) = M.slotStart S.C s + 4 * Δ S := fun s => by
    obtain ⟨h1, h2, h3, h4, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s
    exact ⟨by rw [h1]; push_cast; ring, by rw [h2]; push_cast; ring, by rw [h3]; push_cast; ring,
      by rw [h4]; push_cast; ring⟩
  have hssm : ∀ a b : ℕ, a ≤ b → ((M.slotStart S.C a : ℕ) : ℝ) ≤ M.slotStart S.C b := fun a b h => by
    exact_mod_cast (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S h
  -- the callees' caches row, on the state at each step strictly after the hand-over time
  have hCachesS := (cachesOnChain_st_of_succ M F) S A x R s₀ H i₂ (t : ℝ) E hCaches
  have hOwner : VotesCastByOwner M A x := (votesCastByOwner_of_unforgeability M F) S A x R E
  -- roots at every tick to a clock value at most `c`, when `c + ΔClockBehind` is at most `t`
  have hRootsTickOf : ∀ c : ℕ, (c : ℝ) + ΔClockBehind ≤ t → ∀ (k : ℕ) (u : V) (c' : ℕ),
      x.lbl k = Event.tick u c' → c' ≤ c → RootsNameBlocksUntil M A x (x.time k) := by
    intro c hc k u c' hk hc'
    have h1 := (E.tick_active k u c' hk).2.2
    have h2 : (c' : ℝ) ≤ c := by exact_mod_cast hc'
    exact (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (by linarith) hRoots
  -- an updater's tick to the support cutoff of the next slot is at most that cutoff plus `ΔClockBehind`
  have hUpdTick : ∀ σ : ℕ, ∀ v ∈ updaterAt M S A x σ,
      x.time (x.tickStep v (M.supportCutoff S.C (σ + 1))) ≤ ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) + ΔClockBehind := by
    intro σ v hv
    have hv' := hv
    unfold updaterAt at hv'
    obtain ⟨k', hk', -⟩ := (Activity.mem_activeThroughoutToTick).1 hv'
    rw [(tickStep_eq_of_lbl M) x E hk']
    exact (E.tick_active k' v _ hk').2.2
  -- the induction, at the slots `s` whose support cutoff plus `ΔClockBehind` is at most `t` and whose committee
  -- sleepiness is read up to the support cutoff of slot `s + 1` (from `hSleepK` when that cutoff is at most `t`, from
  -- `hSleepKTick` at an updater's own tick otherwise,)
  have key : ∀ s : ℕ, s₀ < s → ((M.supportCutoff S.C s : ℕ) : ℝ) + ΔClockBehind ≤ t →
      CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s + 1)) →
      (∀ w ∈ honestActiveAt M S A x s, VoterFrameOnChainAt M S A x s₀ s w) ∧
      (∀ v ∈ updaterAt M S A x s, x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) ≤ t →
        UpdaterFinalizedOnChainAt M S A x s₀ s v) := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro hs hcsR hKs
      obtain ⟨hvs, hcs, -, hss⟩ := hT s
      obtain ⟨-, hcs1, -, -⟩ := hT (s + 1)
      have hcst : M.supportCutoff S.C s ≤ t := by
        have : ((M.supportCutoff S.C s : ℕ) : ℝ) ≤ (t : ℝ) := by linarith
        exact_mod_cast this
      -- every frame at the slots after `s₀` and before `s`: every updater there ticked by `t`
      have hFrames : ∀ σ : ℕ, s₀ < σ → σ < s →
          (∀ w ∈ honestActiveAt M S A x σ, VoterFrameOnChainAt M S A x s₀ σ w) ∧
          (∀ v ∈ updaterAt M S A x σ, UpdaterFinalizedOnChainAt M S A x s₀ σ v) := by
        intro σ h1 h2
        have hσs : M.supportCutoff S.C (σ + 1) ≤ M.supportCutoff S.C s := hcm _ _ h2
        have hσR : ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) ≤ M.supportCutoff S.C s := by exact_mod_cast hσs
        have hσσ : ((M.supportCutoff S.C σ : ℕ) : ℝ) ≤ M.supportCutoff S.C s := by
          exact_mod_cast hcm _ _ (le_of_lt h2)
        obtain ⟨hV, hU⟩ := ih σ h2 h1 (by linarith)
          (CommitteeSleepinessUntil.mono M hKs (hcm _ _ (by omega : σ + 1 ≤ s + 1)))
        refine ⟨hV, fun v hv => hU v hv ?_⟩
        have := hUpdTick σ v hv
        linarith
      rcases Nat.lt_or_ge s s_m with hlt | hge
      · -- before the last honest round opening slot: Lemma 89's frames
        obtain ⟨hV, hU⟩ := hPhase s hs hlt
        refine ⟨fun w hw => hV w ?_, fun v hv _ => hU v hv⟩
        unfold roundMembers
        refine Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun h => ?_⟩
        unfold honestActiveAt at hw
        exact (Finset.mem_sdiff.1 hw).2 (Finset.mem_union_left _ h)
      · -- from it on: the chain before `s`, from the frames before `s`
        have hChain : ConfirmationsChainBefore M S A x s₀ s :=
          (lem81_chain_before M F U) S A x R GST s₀ anchor s B₀ E hNet hSkew hRedeliver Sy hΔs
            (hRootsTickOf _ hcsR) hParent hOwner hGST (CommitteeSleepinessUntil.mono M hSleepK hcst) hAnchor hB₀slot
            hBase hBaseSaved (fun σ h1 h2 => (hFrames σ h1 h2).1) (fun σ h1 h2 => (hFrames σ h1 h2).2)
        have hcut0 : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) ≤ t := by
          exact_mod_cast le_trans (hcm _ _ (by omega : s₀ + 1 ≤ s)) hcst
        -- the voter frames at `s`
        have hVF : ∀ w ∈ honestActiveAt M S A x s, VoterFrameOnChainAt M S A x s₀ s w := by
          intro w hw
          rcases Nat.eq_or_lt_of_le hge with heq | hgt
          · -- at the last honest round opening slot: Lemma 89's added clause
            rw [← heq] at hw ⊢
            refine hLast w ((not_mem_corruptedAtTime_of_honestActiveAt M F) R E hw ?_)
            obtain ⟨h1, h2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s_m
            have := hcm _ _ (show s_m ≤ s_m + 1 by omega)
            omega
          · -- after it: the voter frame after the hand-over
            obtain ⟨k, hk⟩ := (tick_voteTime_of_honestActiveAt_succ M F U) S A x R E hSkew (s - 1) w
              (by rwa [show s - 1 + 1 = s by omega])
            rw [show s - 1 + 1 = s by omega] at hk
            have hke : x.tickStep w (M.voteTime S.C s) = k := (tickStep_eq_of_lbl M) x E hk
            have hkt : x.time (x.tickStep w (M.voteTime S.C s)) ≤ t := by
              rw [hke]
              have h1 := (E.tick_active k w _ hk).2.2
              linarith
            have hs1 : s₀ ≤ s - 1 := by omega
            have hsvf : x.time i₂ < M.viewFreeze S.C (s - 1) := by
              obtain ⟨-, -, ha, -⟩ := hT s_m
              obtain ⟨-, -, hb, -⟩ := hT (s - 1)
              have := hssm _ _ (show s_m ≤ s - 1 by omega)
              linarith
            exact (voterFrame_after_handover_until M F U Fx) S A x R GST s₀ i₂ H s w E hNet hSkew hRedeliver Sy hΔs
              ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hkt hRoots) hParent
              (hAdvQ.mono (max_le hkt hcut0)) ((gst_sync_le_viewFreeze M F U) S hGST hs1)
              ((confirmation_holder_at_window_start_until M F U) S A x R E hSkew s₀ s anchor t Δs hSleepK hAnchor hcst
                hFrames hStay)
              (fun σ h1 h2 u hu => hStay σ h1 (le_trans (hcm _ _ (by omega : σ + 1 ≤ s)) hcst) u hu) hOld
              (fun j u h₁ h₂ hu => hCachesS j u h₁ (le_trans h₂ hkt) hu) hsvf hChain hw
        refine ⟨hVF, fun v hv hvt => ?_⟩
        -- the updater frames at `s`: the slot-`s` confirmations of the earlier updaters extend the chain before `s`,
        -- from the votes clause at `s`
        have hCom : |S.P.committee s| < 2 * |S.P.committee s ∩ honestActiveAt M S A x s| :=
          (committee_majority_of_sleepiness M F) S A x anchor s hKs
            (le_trans hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
              (by omega))) le_rfl
        have hVotes : ∀ C : Block V, OnHonestChainBefore M S A x s₀ s C →
            ∀ u ∈ honestActiveAt M S A x s, ∀ vote : GoldfishVote V,
              (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
                (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
              ∃ H_u ∈ (x.tickInput u (M.voteTime S.C s)).tree, vote = GoldfishVote.mk u s H_u.root ∧
                C.AncestorEq H_u := by
          obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
          exact (votes_clause_after_healed_slot M F U) S A x R GST s₀ anchor s' B₀ E hNet hSkew hRedeliver Sy hΔs
            ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (by linarith) hRoots)
            (hRootsTickOf _ hcsR) hParent hGST hKs hAnchor hB₀slot hBase
            hBaseSaved (by omega)
            (fun σ h1 h2 => by
              rcases Nat.lt_or_ge σ (s' + 1) with h | h
              · exact (hFrames σ h1 h).1
              · obtain rfl : σ = s' + 1 := by omega
                exact hVF)
            (fun σ h1 h2 => (hFrames σ h1 (by omega)).2)
        have hsTick : ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (s + 1)) →
            x.time i₂ < x.time k := by
          intro k u hk
          have h1 := (E.tick_active k u _ hk).2.1
          obtain ⟨-, -, ha, -⟩ := hT s_m
          have := hssm _ _ hge
          linarith
        exact (updater_frames_at_slot M F U Fx) S A x R s₀ i₂ H s (t : ℝ) E hSkew hRoots
          (hAdvQ.mono (max_le le_rfl hcut0)) hOld hCachesS hsTick hChain
          (fun u hu hUF C hC C' hC' => (votes_clause_updater_confirmation M F U) S A x R GST s
            (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) u E hNet hSkew hRedeliver Sy hΔs
            (hRootsTickOf _ hcsR) hParent hOwner (le_trans hGST (hcm _ _ (by omega))) (subset_refl _) hCom hVotes hu
            hUF C hC C' hC') v hv hvt
  exact key

/-- **The frames at every slot after the healed slot.** The proof; the audited statement is in
`Statements/Executions/HealedTopStatements.lean`. Why: by strong induction on the slot `s > s₀`.
For `s < s_m`, Lemma 89's voter frame at `roundMembers M S Sched (s + 1)`, which contains the honest
active validators of `s`, and its updater frame at `updaterAt M S A x s`. For `s ≥ s_m`, the frames at the slots before `s` give
`ConfirmationsChainBefore M S Sched x s₀ s` (`lem81_chain_before`); then the voter frame at `s_m` is
Lemma 89's clause, the voter frame at `s > s_m` is `voterFrame_after_handover`, and the updater
frame at `s ≥ s_m` is `updaterFrame_after_handover`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `s_m`: the last honest round opening slot; `i₂`:
  the step from which the caches are on the chain; `H`: the threshold; `anchor`: the time from
  which committee sleepiness holds; `t`: the bound on the slots' update times; `B₀`: the block
  every updater of slot `s₀` saved.

Roots name blocks until `t`: the conclusions are for the slots `s` whose update, at the support
cutoff of slot `s + 1`, is at most `t`; at such a slot the proof reads `lem81_chain_before` up to
the support cutoff of slot `s`, `voterFrame_after_handover` up to the vote time of slot `s` and
`updaterFrame_after_handover` up to the support cutoff of slot `s + 1`.

Caches up to `t`: at a slot `s` the proof reads the caches up to the support cutoff of slot `s + 1`,
at most `t` (`voterFrame_after_handover_until`, `updaterFrame_after_handover_until`).

Read aloud: the phase's frames, carried past the hand-over by strong induction on the slot, at every
slot whose update is at most `t`. -/
theorem frames_after_healed_slot_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ s_m i₂ H anchor t : ℕ) (B₀ : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x t)
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) t)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hSleepK : CommitteeSleepinessUntil M S A x anchor t)
    -- every tick at a real time at most `t`, to a clock value `c`: committee sleepiness from `anchor` read up to `c`
    --
    (hSleepKTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → (x.time k : ℝ) ≤ t →
      CommitteeSleepinessUntil M S A x anchor c)
    -- every updater of a slot from the healed slot `s₀` on, whose update is at most `t`, is active for the
    -- sync delay after the real time of its own tick to the support cutoff of the next slot
    --
    (hStay : ∀ σ : ℕ, s₀ ≤ σ → M.supportCutoff S.C (σ + 1) ≤ t → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hAnchor : anchor ≤ M.slotStart S.C (s₀ + 1))
    (hB₀slot : s₀ ≤ B₀.slot)
    (hBase : HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀)
    (hBaseSaved : ∀ v ∈ updaterAt M S A x s₀,
      (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hi₂ : x.time i₂ < M.viewFreeze S.C s_m)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₂ ≤ x.time j → x.time j ≤ t →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st (j + 1) u))
    (hPhase : ∀ s : ℕ, s₀ < s → s < s_m →
      (∀ w ∈ roundMembers M S A x (s + 1), VoterFrameOnChainAt M S A x s₀ s w) ∧
      (∀ v ∈ updaterAt M S A x s, UpdaterFinalizedOnChainAt M S A x s₀ s v))
    (hLast : ∀ w : V, w ∉ A.corruptedAtTime x (M.voteTime S.C s_m) →
      VoterFrameOnChainAt M S A x s₀ s_m w) :
    (∀ s : ℕ, s₀ < s → M.supportCutoff S.C (s + 1) ≤ t →
      ∀ w ∈ honestActiveAt M S A x s, VoterFrameOnChainAt M S A x s₀ s w) ∧
    (∀ s : ℕ, s₀ < s → ∀ v ∈ updaterAt M S A x s,
      x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) ≤ t → UpdaterFinalizedOnChainAt M S A x s₀ s v) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hT : ∀ s : ℕ, ((M.voteTime S.C s : ℕ) : ℝ) = M.slotStart S.C s + Δ S ∧
      ((M.supportCutoff S.C s : ℕ) : ℝ) = M.slotStart S.C s + 2 * Δ S ∧
      ((M.viewFreeze S.C s : ℕ) : ℝ) = M.slotStart S.C s + 3 * Δ S ∧
      ((M.slotStart S.C (s + 1) : ℕ) : ℝ) = M.slotStart S.C s + 4 * Δ S := fun s => by
    obtain ⟨h1, h2, h3, h4, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s
    exact ⟨by rw [h1]; push_cast; ring, by rw [h2]; push_cast; ring, by rw [h3]; push_cast; ring,
      by rw [h4]; push_cast; ring⟩
  have key := (frames_at_slot_after_healed_until M F U Fx) S A x R GST s₀ s_m i₂ H anchor t B₀ E hNet hSkew hRedeliver Sy hΔs
    hRoots hParent hAdvQ hGST hSleepK hStay hAnchor hB₀slot hBase hBaseSaved hOld hi₂ hCaches hPhase hLast
  -- a slot whose next support cutoff is at most `t`: its own cutoff plus `ΔClockBehind` is at most `t`
  have hcsR_of : ∀ s : ℕ, M.supportCutoff S.C (s + 1) ≤ t →
      ((M.supportCutoff S.C s : ℕ) : ℝ) + ΔClockBehind ≤ t := by
    intro s hst
    obtain ⟨-, hcs, -, hss⟩ := hT s
    obtain ⟨-, hcs1, -, -⟩ := hT (s + 1)
    have hstR : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ t := by exact_mod_cast hst
    linarith
  refine ⟨fun s hs hst => (key s hs (hcsR_of s hst) (CommitteeSleepinessUntil.mono M hSleepK hst)).1,
    fun s hs v hv hvt => ?_⟩
  rcases Nat.lt_or_ge s s_m with hlt | hge
  · exact (hPhase s hs hlt).2 v hv
  -- from the last honest round opening slot on: committee sleepiness up to the support cutoff of slot `s + 1`,
  -- read at `v`'s own tick to it, at a real time at most `t`
  have hv' := hv
  unfold updaterAt at hv'
  obtain ⟨k, hk, -⟩ := (Activity.mem_activeThroughoutToTick).1 hv'
  have hke : x.tickStep v (M.supportCutoff S.C (s + 1)) = k := (tickStep_eq_of_lbl M) x E hk
  have hkt : x.time k ≤ t := by rw [← hke]; exact hvt
  have hcsR : ((M.supportCutoff S.C s : ℕ) : ℝ) + ΔClockBehind ≤ t := by
    obtain ⟨-, hcs, -, hss⟩ := hT s
    obtain ⟨-, hcs1, -, -⟩ := hT (s + 1)
    have h1 := (E.tick_active k v _ hk).2.1
    linarith
  exact (key s hs hcsR (hSleepKTick k v _ hk hkt)).2 v hv hvt

/-! ## The facts after the hand-over -/

/-- **The facts after the hand-over, for the readings up to a time `t`.** The proof; the audited
statement is in `Statements/Executions/HealedTopStatements.lean`. Why: for `t ≥ tAwakeEnd`, either a
root collision has hit two blocks honest validators hold by `t`, or roots name blocks up to `t`
(`rootsNameBlocksUntil_or_collision`); then `healed_handover_facts`'s proof with every reading up to
`t`: Lemma 89 reads up to the support cutoff of the last opening's first slot, at most `tAwakeEnd`;
the caches from `i₂` up to `t` (`caches_after_handover`); the frames at the slots whose update is at
most `t` (`frames_after_healed_slot_until`); and the chain before the slot after each such slot
(`lem81_chain_before`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `m`, `r`: the index of the last honest round opening slot and the rounds of the honest round opening slots.

Read aloud: for every time `t` after the phase, unless a collision has hit an honest proposal or two
blocks held by `t`, the honest chain after healing exists up to `t` and every honest validator's
caches stay on it up to `t`. -/
theorem healed_handover_facts_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (r : ℕ → ℕ)
    (hGST : GST ≤ tGAT)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot, every validator outside the adversary set at the support cutoff of the slot
    -- after its first slot is active through the attestations' sync delay after the later of that first slot's duty
    -- window's start and `GST`
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (r i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (t : ℕ) (ht : tAwakeEnd ≤ t)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) t)
    -- every tick at a real time at most `t`, to a clock value `c`: committee sleepiness from `anchorCW S tGAT` read up
    -- to `c`
    (hCommitteesTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → (x.time k : ℝ) ≤ t →
      CommitteeSleepinessUntil M S A x (anchorCW S tGAT) c)
    -- every updater of a slot from the first honest round opening slot `r 0 * S.C.R` on, whose update is at
    -- most `t`, is active for the sync delay after the real time of its own tick to the support cutoff of the
    -- next slot
    (hStay : ∀ σ : ℕ, r 0 * S.C.R ≤ σ → M.supportCutoff S.C (σ + 1) ≤ t → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hSeq : HonestOpeningSeq M S A x r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hOpenings : OpeningsOutsideWaitsAndWindows S r m)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) t) :
      RootCollisionAtOpening M S A x r m ∨ RootCollisionHeldBy M S A x t ∨
      ∃ (s₀ i₂ : ℕ) (B₀ : Block V),
        (M.supportCutoff S.C (s₀ + 1) < x.time i₂ ∧
          ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (s₀ + 1)) → x.time k < x.time i₂) ∧
        x.time i₂ ≤ tAwakeEnd ∧
        (∀ s : ℕ, tAwakeEnd ≤ M.slotStart S.C s → x.time i₂ < M.slotStart S.C s ∧
          ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.slotStart S.C s) → x.time i₂ < x.time k) ∧
        r 0 * S.C.R ≤ s₀ ∧
        GST ≤ M.voteTime S.C s₀ ∧ anchorCW S tGAT ≤ M.slotStart S.C (s₀ + 1) ∧ s₀ ≤ B₀.slot ∧
        HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀ ∧
        (∀ v ∈ updaterAt M S A x s₀,
          (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀) ∧
        (∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1)) →
          v ∈ updaterAt M S A x s₀) ∧
        OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) (M.chainStateOf S.C B₀).h ∧
        (∀ (j : ℕ) (u : V), x.time i₂ ≤ x.time j → x.time j ≤ t →
          u ∉ A.corrupted j →
          CachesOnChain M S A x s₀ (M.chainStateOf S.C B₀).h (x.st j u)) ∧
        (∀ (j : ℕ) (u : V), x.time i₂ ≤ x.time j → x.time j ≤ t →
          u ∉ A.corrupted j →
          CachesOnChain M S A x s₀ (M.chainStateOf S.C B₀).h (x.st (j + 1) u)) ∧
        (∀ s : ℕ, s₀ < s → M.supportCutoff S.C (s + 1) ≤ t →
          ∀ w ∈ honestActiveAt M S A x s, VoterFrameOnChainAt M S A x s₀ s w) ∧
        (∀ s : ℕ, s₀ < s → ∀ v ∈ updaterAt M S A x s,
          x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) ≤ t → UpdaterFinalizedOnChainAt M S A x s₀ s v) ∧
        (∀ (σ k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1)) →
          x.time k ≤ t → ConfirmationsChainBefore M S A x s₀ σ ∧
          ∀ v ∈ updaterAt M S A x σ, x.time (x.tickStep v (M.supportCutoff S.C (σ + 1))) ≤ t →
          ∀ C' : Block V, (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C' →
          (∀ C : Block V, OnHonestChainBefore M S A x s₀ σ C → C.AncestorEq C') ∧
          (s₀ ≤ σ → ∀ v' ∈ updaterAt M S A x σ, x.time (x.tickStep v' (M.supportCutoff S.C (σ + 1))) ≤ t →
          ∀ C'' : Block V, (x.tickOutput v' (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C'' →
          C'.compatible C'' = true)) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk := S.C.k_ge_two
  have hR := S.C.R_ge_two
  have hcm : ∀ a b : ℕ, a ≤ b → M.supportCutoff S.C a ≤ M.supportCutoff S.C b := fun a b h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h
  -- the slot times, as reals
  have hT : ∀ s : ℕ, ((M.voteTime S.C s : ℕ) : ℝ) = M.slotStart S.C s + Δ S ∧
      ((M.supportCutoff S.C s : ℕ) : ℝ) = M.slotStart S.C s + 2 * Δ S ∧
      ((M.viewFreeze S.C s : ℕ) : ℝ) = M.slotStart S.C s + 3 * Δ S ∧
      ((M.slotStart S.C (s + 1) : ℕ) : ℝ) = M.slotStart S.C s + 4 * Δ S := fun s => by
    obtain ⟨h1, h2, h3, h4, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s
    exact ⟨by rw [h1]; push_cast; ring, by rw [h2]; push_cast; ring, by rw [h3]; push_cast; ring,
      by rw [h4]; push_cast; ring⟩
  have hssm : ∀ a b : ℕ, a ≤ b → ((M.slotStart S.C a : ℕ) : ℝ) ≤ M.slotStart S.C b := fun a b h => by
    exact_mod_cast (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S h
  have htR : (tAwakeEnd : ℝ) ≤ t := by exact_mod_cast ht
  have hOwner : VotesCastByOwner M A x := (votesCastByOwner_of_unforgeability M F) S A x R E
  rcases (rootsNameBlocksUntil_or_collision M) x t with hRootsT | hCol
  swap
  · exact Or.inr (Or.inl hCol)
  -- Lemma 89, with its two rows at the last honest round opening slot's support cutoff: roots up to `t`
  -- restricted to each tick's real time, and the end from `hSeq.lastTick`
  have hLastR : ((M.supportCutoff S.C (r m * S.C.R) : ℕ) : ℝ) ≤ t := by
    have := hSeq.last
    exact_mod_cast le_trans this ht
  rcases (lem89_phase M F U Fx) S A x R GST tGAT tAwakeEnd m r E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs
      Sy_F hΔs_F hHoldF ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hLastR hRootsT)
      (fun k u c hk hc => (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
        (le_trans (hSeq.lastTick k u c hk hc) htR) hRootsT)
      hParent hGST hThird hAwake hActive (CommitteeSleepinessUntil.mono M hCommittees ht) hSeq
      (fun k u c hk hc => hSeq.lastTick k u c hk hc) hOpenings with
    hCol | ⟨j, s₀, B₀, hjm, hs₀, hBase, hBaseSaved, hB₀, hOld, hPhase, hCachesVt, hLast⟩
  · exact Or.inl hCol
  right; right
  have hmono := r_lt_of_lt_of_mono r m hSeq.mono
  -- the first slot of the last opening is at least two slots after `s₀`
  have hsm : s₀ + 2 ≤ r m * S.C.R := by
    have h1 : (r j + 1) * S.C.R ≤ r m * S.C.R := Nat.mul_le_mul_right _ (hmono j m hjm le_rfl)
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega
  -- the first opening's slot is at most `s₀`
  have h0 : r 0 * S.C.R ≤ s₀ := by
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      omega
    · rw [hs₀]
      exact Nat.mul_le_mul_right _ (hmono 0 j hjpos (by omega)).le
  have hfirst := hSeq.first
  unfold healFrontSlots at hfirst
  rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)] at hfirst
  have e0 : 4 * Δ S * (r 0 * S.C.R) ≤ 4 * Δ S * s₀ := Nat.mul_le_mul_left _ h0
  have ek : 4 * Δ S * (S.C.k + 2) ≤ 4 * Δ S * (3 * S.C.k + 1) := Nat.mul_le_mul_left _ (by omega)
  have hGST' : GST ≤ M.voteTime S.C s₀ := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)]
    omega
  have hAnc : anchorCW S tGAT ≤ M.slotStart S.C (s₀ + 1) := by
    rw [anchorCW_eq]
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add_one (4 * Δ S) s₀]
    omega
  have hGSTs : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀ := (gst_sync_of_anchor M F U) S hGST hΔs hAnc (by linarith)
  have hB₀slot : s₀ ≤ B₀.slot := hB₀.ge
  -- the updaters of `s₀`: every validator honest at the support cutoff of slot `s₀ + 1` (`hActive`)
  have hscE : M.supportCutoff S.C (s₀ + 1) ≤ tAwakeEnd := le_trans (hcm _ _ (by omega)) hSeq.last
  have hdw0 : tGAT ≤ M.dutyWindowStart S.C s₀ := by
    have := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT s₀ hAnc
    omega
  have hUpd : ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1)) → v ∈ updaterAt M S A x s₀ :=
    fun v hv => (hActive s₀ hdw0 hscE v hv).2
  -- the step `i₂`: the tick of the last opening's proposer to that opening's support cutoff, an updater of the
  -- slot before (`hActive`), at a real time at most `tAwakeEnd` (`hSeq.lastTick`)
  have hsm1 : r m * S.C.R - 1 + 1 = r m * S.C.R := by omega
  have hdwm : tGAT ≤ M.dutyWindowStart S.C (r m * S.C.R - 1) := by
    have := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT
      (r m * S.C.R - 1) (by
        rw [hsm1]
        exact le_trans hAnc ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
          (by omega)))
    omega
  obtain ⟨-, hpU⟩ := hActive (r m * S.C.R - 1) hdwm (by rw [hsm1]; exact hSeq.last)
    (S.P.proposer (r m * S.C.R)) (by rw [hsm1]; exact hSeq.honest m le_rfl)
  have hpU' := hpU
  unfold updaterAt at hpU'
  obtain ⟨i₂, hi₂l, -⟩ := (Activity.mem_activeThroughoutToTick).1 hpU'
  rw [hsm1] at hi₂l
  have hi₂a := (E.tick_active i₂ _ _ hi₂l).2
  have hi₂E : x.time i₂ ≤ tAwakeEnd := hSeq.lastTick i₂ _ _ hi₂l le_rfl
  have hsc : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) < x.time i₂ := by
    obtain ⟨-, hc1, -, hs1⟩ := hT (s₀ + 1)
    obtain ⟨-, hcm', -, -⟩ := hT (r m * S.C.R)
    have := hssm (s₀ + 1 + 1) (r m * S.C.R) (by omega)
    linarith [hi₂a.1]
  -- every tick to the healed slot's update is before `i₂`: at most `cut(s₀ + 1) + ΔClockBehind`,
  -- while `i₂` is at least `cut(s_m) − ΔClockAhead` with `s₀ + 2 ≤ s_m`
  have hscTick : ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (s₀ + 1)) →
      x.time k < x.time i₂ := by
    intro k u hk
    have h1 := (E.tick_active k u _ hk).2.2
    obtain ⟨-, hc1, -, hs1⟩ := hT (s₀ + 1)
    obtain ⟨-, hcm', -, -⟩ := hT (r m * S.C.R)
    have := hssm (s₀ + 1 + 1) (r m * S.C.R) (by omega)
    linarith [hi₂a.1]
  have hx2s : ∀ s : ℕ, tAwakeEnd ≤ M.slotStart S.C s → x.time i₂ < M.slotStart S.C s ∧
      ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.slotStart S.C s) → x.time i₂ < x.time k := by
    intro s hs
    have hlt : r m * S.C.R < s := by
      by_contra hle
      push_neg at hle
      have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hle
      have h2 := hSeq.last
      obtain ⟨-, h3, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S
        (r m * S.C.R)
      omega
    have hss := hssm (r m * S.C.R + 1) s hlt
    obtain ⟨-, hc, -, h4⟩ := hT (r m * S.C.R)
    refine ⟨by linarith [hi₂a.2], fun k u hk => ?_⟩
    -- a tick to the start of slot `s` is at least `st(s) − ΔClockAhead`
    have h1 := (E.tick_active k u _ hk).2.1
    linarith [hi₂a.2]
  have hi₂vf : x.time i₂ < M.viewFreeze S.C (r m * S.C.R) := by
    obtain ⟨-, hc, hvf, -⟩ := hT (r m * S.C.R)
    linarith [hi₂a.2]
  -- the caches: each validator honest at a step `j` from `i₂` on ticked to the vote time of slot `s_m` before
  -- `i₂` (awake and honest through that tick's window, `hAwake`), where Lemma 89 puts its caches on the chain;
  -- Lemma 84 from that tick on
  have hcut0 : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) ≤ t := le_trans hsc.le (le_trans hi₂E htR)
  have hvt_lt : ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.voteTime S.C (r m * S.C.R)) →
      x.time k < x.time i₂ := by
    intro k u hk
    have h1 := (E.tick_active k u _ hk).2.2
    obtain ⟨hv, hc, -, -⟩ := hT (r m * S.C.R)
    linarith [hi₂a.1]
  have hfirstm : (tGAT : ℝ) ≤ M.slotStart S.C (r m * S.C.R) := by
    have h1 : tGAT ≤ M.slotStart S.C (r m * S.C.R) :=
      le_trans (le_trans (Nat.le_add_right _ _) hSeq.first)
        ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
    exact_mod_cast h1
  have hvt1 : 1 ≤ M.voteTime S.C (r m * S.C.R) := by
    obtain ⟨h1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (r m * S.C.R)
    omega
  have hCachesBoth : ∀ (j : ℕ) (u : V), x.time i₂ ≤ x.time j → x.time j ≤ t →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ (M.chainStateOf S.C B₀).h (x.st j u) ∧
        CachesOnChain M S A x s₀ (M.chainStateOf S.C B₀).h (x.st (j + 1) u) := by
    intro j u hj hjt hu
    obtain ⟨hv, hc, -, -⟩ := hT (r m * S.C.R)
    have hwin : ∀ i : ℕ, ((M.voteTime S.C (r m * S.C.R) : ℕ) : ℝ) - ΔClockAhead ≤ x.time i →
        x.time i ≤ ((M.voteTime S.C (r m * S.C.R) : ℕ) : ℝ) + ΔClockBehind → u ∈ A.active i := by
      intro i h1 h2
      have hij : i < j := (lt_of_time_lt M) x R (by linarith [hi₂a.1])
      have hui : u ∉ A.corrupted i := E.not_mem_corrupted_of_le hij.le hu
      have hti := (time_le_succ M) x R i
      exact Activity.mem_active.2 ⟨hAwake i u (by linarith) (by linarith) hui, hui⟩
    obtain ⟨ku, hku, -, -⟩ := E.tick_of_active _ hvt1 u hwin
    have hkui := hvt_lt ku u hku
    have hkuj : ku < j := (lt_of_time_lt M) x R (lt_of_lt_of_le hkui hj)
    have hke : x.tickStep u (M.voteTime S.C (r m * S.C.R)) = ku := (tickStep_eq_of_lbl M) x E hku
    have hStart : CachesOnChain M S A x s₀ (M.chainStateOf S.C B₀).h (x.st ku u) := by
      have h1 := hCachesVt u (by rw [hke]; exact hku) (by
        rw [hke]
        exact Activity.not_mem_corruptedAtTime.2 fun k hk => E.not_mem_corrupted_of_le
          ((lt_of_time_lt M) x R (lt_of_le_of_lt hk (lt_of_lt_of_le hkui hj))).le hu)
      rwa [show x.tickInput u (M.voteTime S.C (r m * S.C.R)) = x.st ku u by
        unfold Trace.tickInput; rw [hke]] at h1
    have hFrom := (lem84_caches_stay_on_chain_from M F U Fx) S A x R s₀ (M.supportCutoff S.C (s₀ + 1))
      (M.chainStateOf S.C B₀).h ku t u E hRootsT (hAdvQ.mono (max_le le_rfl hcut0))
      ((lem82_honest_attestations_on_chain M F U) S A x R s₀ E) hOld hStart
    -- the state at step `j`, and the state step `j` leaves
    refine ⟨hFrom j hkuj.le hjt hu, ?_⟩
    rcases (step_succ_cases M F) x R E j with ⟨-, h⟩ | ⟨ht₁, hc₁⟩
    · rw [h u]
      exact hFrom j hkuj.le hjt hu
    · exact hFrom (j + 1) (by omega) (by rw [ht₁]; exact hjt) (by rw [hc₁]; exact hu)
  have hCaches : ∀ (j : ℕ) (u : V), x.time i₂ ≤ x.time j → x.time j ≤ t →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ (M.chainStateOf S.C B₀).h (x.st (j + 1) u) :=
    fun j u h1 h2 h3 => (hCachesBoth j u h1 h2 h3).2
  -- the frames at the slots after `s₀`
  have hStay₀ : ∀ σ : ℕ, s₀ ≤ σ → M.supportCutoff S.C (σ + 1) ≤ t → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs) := fun σ h1 => hStay σ (le_trans h0 h1)
  have hFr := (frames_after_healed_slot_until M F U Fx) S A x R GST s₀ (r m * S.C.R) i₂
    (M.chainStateOf S.C B₀).h (anchorCW S tGAT) t B₀ E hNet hSkew hRedeliver Sy hΔs hRootsT hParent hAdvQ hGSTs
    hCommittees hCommitteesTick hStay₀ hAnc hB₀slot hBase hBaseSaved hOld hi₂vf hCaches hPhase hLast
  have hKey := (frames_at_slot_after_healed_until M F U Fx) S A x R GST s₀ (r m * S.C.R) i₂
    (M.chainStateOf S.C B₀).h (anchorCW S tGAT) t B₀ E hNet hSkew hRedeliver Sy hΔs hRootsT hParent hAdvQ hGSTs
    hCommittees hStay₀ hAnc hB₀slot hBase hBaseSaved hOld hi₂vf hCaches hPhase hLast
  refine ⟨s₀, i₂, B₀, ⟨hsc, hscTick⟩, hi₂E, hx2s, h0, hGST', hAnc, hB₀slot, hBase, hBaseSaved, hUpd, hOld,
    fun j u h1 h2 h3 => (hCachesBoth j u h1 h2 h3).1, hCaches, hFr.1, hFr.2, ?_⟩
  -- the chain clause, at a slot `σ` some validator updated by `t`
  intro σ k u hk hkt
  have hka := E.tick_active k u _ hk
  have hcsR : ((M.supportCutoff S.C σ : ℕ) : ℝ) + ΔClockBehind ≤ t := by
    obtain ⟨-, hc, -, hs⟩ := hT σ
    obtain ⟨-, hc1, -, -⟩ := hT (σ + 1)
    linarith [hka.2.1]
  have hKs := hCommitteesTick k u _ hk hkt
  -- roots up to every tick to a clock value at most the support cutoff of slot `σ`
  have hRootsσ : ∀ (k' : ℕ) (u' : V) (c : ℕ), x.lbl k' = Event.tick u' c → c ≤ M.supportCutoff S.C σ →
      RootsNameBlocksUntil M A x (x.time k') := fun k' u' c hk' hc => by
    have h1 := (E.tick_active k' u' c hk').2.2
    have h2 : (c : ℝ) ≤ M.supportCutoff S.C σ := by exact_mod_cast hc
    exact (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (by linarith) hRootsT
  -- two confirmations of slot `σ ≥ s₀` saved by updaters that ticked by `t` are compatible (Lemma 32)
  have hCompat : s₀ ≤ σ → ∀ v ∈ updaterAt M S A x σ, x.time (x.tickStep v (M.supportCutoff S.C (σ + 1))) ≤ t →
      ∀ C' : Block V, (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C' →
      ∀ v' ∈ updaterAt M S A x σ, x.time (x.tickStep v' (M.supportCutoff S.C (σ + 1))) ≤ t →
      ∀ C'' : Block V, (x.tickOutput v' (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C'' →
      C'.compatible C'' = true := by
    intro hσ v hv hvt C' hC' v' hv' hv't C'' hC''
    refine (GoldilocksCorrectness.Record.Proofs.Executions.lem32_saved_confirmations_compatible_state M F U) S A x R
      GST σ v v' C' C'' E hNet hSkew hRedeliver Sy hΔs
      ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (max_le hvt hv't) hRootsT)
      ?_ hv hv' hC' hC''
    have := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
    have := hcm _ _ hσ
    omega
  rcases Nat.lt_or_ge s₀ σ with hσ | hσ
  · -- after the healed slot: the frames up to `σ` (`frames_at_slot_after_healed_until`), the chain before `σ`
    -- (`lem81_chain_before`), and the slot-`σ` confirmations extending it (Lemma 78 from the votes clause)
    have hcσt : M.supportCutoff S.C σ ≤ t := by
      have : ((M.supportCutoff S.C σ : ℕ) : ℝ) ≤ t := by linarith
      exact_mod_cast this
    have hFrσ : ∀ σ' : ℕ, s₀ < σ' → σ' ≤ σ →
        (∀ w ∈ honestActiveAt M S A x σ', VoterFrameOnChainAt M S A x s₀ σ' w) ∧
        (∀ v ∈ updaterAt M S A x σ', x.time (x.tickStep v (M.supportCutoff S.C (σ' + 1))) ≤ t →
          UpdaterFinalizedOnChainAt M S A x s₀ σ' v) := fun σ' h1 h2 =>
      hKey σ' h1 (by
          have : ((M.supportCutoff S.C σ' : ℕ) : ℝ) ≤ M.supportCutoff S.C σ := by exact_mod_cast hcm _ _ h2
          linarith)
        (CommitteeSleepinessUntil.mono M hKs (hcm _ _ (by omega)))
    -- an updater of a slot before `σ` ticks to the next support cutoff by `t`
    have hUpdBefore : ∀ σ' : ℕ, σ' < σ → ∀ v ∈ updaterAt M S A x σ',
        x.time (x.tickStep v (M.supportCutoff S.C (σ' + 1))) ≤ t := by
      intro σ' h v hv
      have hv' := hv
      unfold updaterAt at hv'
      obtain ⟨k', hk', -⟩ := (Activity.mem_activeThroughoutToTick).1 hv'
      rw [(tickStep_eq_of_lbl M) x E hk']
      have h1 := (E.tick_active k' v _ hk').2.2
      have h2 : ((M.supportCutoff S.C (σ' + 1) : ℕ) : ℝ) ≤ M.supportCutoff S.C σ := by exact_mod_cast hcm _ _ h
      linarith
    have hChainσ : ConfirmationsChainBefore M S A x s₀ σ :=
      (lem81_chain_before M F U) S A x R GST s₀ (anchorCW S tGAT) σ B₀ E hNet hSkew hRedeliver Sy hΔs hRootsσ hParent
        hOwner hGSTs (CommitteeSleepinessUntil.mono M hCommittees hcσt) hAnc hB₀slot hBase hBaseSaved
        (fun s h1 h2 => (hFrσ s h1 h2.le).1) (fun s h1 h2 v hv => (hFrσ s h1 h2.le).2 v hv (hUpdBefore s h2 v hv))
    refine ⟨hChainσ, fun v hv hvt C' hC' => ⟨fun C hC => ?_, fun hs₀σ => hCompat hs₀σ v hv hvt C' hC'⟩⟩
    obtain ⟨σ₁, rfl⟩ : ∃ σ₁, σ = σ₁ + 1 := ⟨σ - 1, by omega⟩
    have hCom := (committee_majority_of_sleepiness M F) S A x (anchorCW S tGAT) (σ₁ + 1) hKs
      (le_trans hAnc ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
        (by omega))) le_rfl
    have hVotes := (votes_clause_after_healed_slot M F U) S A x R GST s₀ (anchorCW S tGAT) σ₁ B₀ E hNet hSkew
      hRedeliver Sy hΔs ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
        (by exact_mod_cast hcσt) hRootsT) hRootsσ hParent hGSTs hKs hAnc hB₀slot hBase hBaseSaved (by omega)
      (fun s h1 h2 => (hFrσ s h1 h2).1)
      (fun s h1 h2 v hv => (hFrσ s h1 (by omega)).2 v hv (hUpdBefore s (by omega) v hv))
    exact (votes_clause_updater_confirmation M F U) S A x R GST (σ₁ + 1) (honestActiveAt M S A x (σ₁ + 1))
      (OnHonestChainBefore M S A x s₀ (σ₁ + 1)) v E hNet hSkew hRedeliver Sy hΔs hRootsσ hParent hOwner
      (le_trans hGSTs (hcm _ _ (by omega))) (subset_refl _) hCom hVotes hv ((hFrσ (σ₁ + 1) hσ le_rfl).2 v hv hvt)
      C hC C' hC'
  · -- at or before the healed slot: the chain before `σ` and the honest chain before `σ` are empty
    refine ⟨by intro s s'' v v' C C' hs hss hs''; exact absurd hs'' (by omega), fun v hv hvt C' hC' =>
      ⟨fun C hC => by obtain ⟨σ', hlt, hs, -⟩ := hC; omega, fun hs₀σ => hCompat hs₀σ v hv hvt C' hC'⟩⟩

/-! ## Lemma 85, with the updater that witnesses the honest chain named -/

/-- **Kit fact, the certificate route with a general `t₀`, with the attester's own saved
confirmation.** As `cert_entry_held_of_agree` (`Lemma84.lean`), with the confirmation of slot `sₐ`
that the attester `uₐ` itself saved at its tick to `M.supportCutoff S.C (sₐ + 1)` named: the entry
`E` is that confirmation or an ancestor of it. `cert_entry_held_of_agree`'s conclusion
`OnHonestChainAt` names some updater of slot `sₐ`; the chain clause of `healed_handover_facts_until`
 reads only the updaters whose tick is by a time `t`, so Lemma 86 needs the attester's own.

Why: `cert_entry_held_of_agree`'s proof, whose witness for `OnHonestChainAt` is the attester itself.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `s₀`: the healed slot; `t₀`: the time
  from which the honest attestations name the honest chain; `H`: the threshold; `j`: the step; `w`:
  the holder; `Y`: the held block; `T`: the justified block; `h`: its height.

Read aloud: a justification certificate above the threshold on a held chain names, by root, an entry
that an honest attester held when it ran the update of a slot `sₐ` at a tick before `j`, and that
entry is the attester's own saved confirmation of `sₐ` or an ancestor of it. -/
theorem cert_entry_held_of_agree_saved (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ t₀ H j : ℕ) (w : V) (Y T : Block V) (h : Height)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time j) t₀))
    (hAgree : HonestAttestationsOnChain M S A x s₀ t₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ t₀ H)
    (hY : Y ∈ (x.st j w).tree)
    (hJ : GoldilocksCorrectness.Record.Statements.Routines.JustificationCertOn M Y h T) (hH : H < h) :
    ∃ (s_a : ℕ) (uₐ : V) (E : Block V), x.tickStep uₐ (M.supportCutoff S.C (s_a + 1)) < j ∧
      x.lbl (x.tickStep uₐ (M.supportCutoff S.C (s_a + 1))) = Event.tick uₐ (M.supportCutoff S.C (s_a + 1)) ∧
      uₐ ∈ updaterAt M S A x s_a ∧ uₐ ∉ A.corruptedAtTime x (x.time j) ∧
      E ∈ (x.tickInput uₐ (M.supportCutoff S.C (s_a + 1))).tree ∧
      s₀ ≤ s_a ∧ IsEntry M S.C E ∧ (M.chainStateOf S.C E).h = h ∧
      T.root = E.root ∧
      ∃ C : Block V, (x.tickOutput uₐ (M.supportCutoff S.C (s_a + 1))).savedConfirmation s_a = some C ∧
        E.AncestorEq C := by
  obtain ⟨X₁, hX₁Y, Q, hqA, hQ⟩ := hJ
  rw [GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched X₁] at hqA
  obtain ⟨u, hu, hhonM⟩ : ∃ u ∈ Q, A.HonestThroughTime x (max (x.time j) t₀) u := by
    by_contra hno
    have hall : ∀ v ∈ Q, ∃ i : ℕ, x.time i ≤ max (x.time j) t₀ ∧ v ∈ A.corrupted i := by
      intro v hv
      by_contra hn
      exact hno ⟨v, hv, fun i hi ha => hn ⟨i, hi, ha⟩⟩
    have h3 := hAdvQ Q hall
    omega
  have hhon : x.HonestThrough A j u :=
    fun i' hi' => hhonM i' (le_trans ((time_mono M) x R hi') (le_max_left _ _))
  obtain ⟨a, hau, hah, haT, -, hon⟩ := hQ u hu
  have hrec : a.content ∈ (x.st j a.val_index).sentAttestations :=
    (GoldilocksCorrectness.Record.Statements.Executions.lem74_honest_attestations_recorded M F) S A x R E j w Y a hY
      ((GoldilocksCorrectness.Record.Proofs.Routines.on_chain_mono M F) a hX₁Y hon)
      (by rw [hau]; exact hhon)
  rw [hau] at hrec
  obtain ⟨j', t', a', hj', hl, -, hsent, -, hcont, -⟩ :=
    (record_content_sent_step M F) S A x R E u j _ hrec
  have hh' : a'.h = h := by
    rw [← hah]
    exact congrArg AttestationContent.h hcont
  have hT' : a'.T = T.root := by
    rw [← haT]
    exact congrArg AttestationContent.T hcont
  obtain ⟨sₐ, source, C, ht, hv, -, hsT, hSaved, hsrcC, hh, hT⟩ :=
    (attest_tick_update_source M F U) S A x R j' t' u a' E hl hsent
  have hge : t₀ ≤ t' := by
    by_contra hlt
    have hle := hOld j' t' u a' hl (by exact_mod_cast (Nat.lt_of_not_le hlt))
      (Activity.not_mem_corruptedAtTime.2 fun k hk => hhonM k (le_trans hk (le_max_right _ _))) hsent
    rw [hh'] at hle
    exact absurd hle (Nat.not_le.mpr hH)
  have hs₀ : s₀ ≤ sₐ := by
    obtain ⟨s, -, hs, ht'', -⟩ := hAgree j' t' u a' hl hge
      (Activity.not_mem_corruptedAtTime.2 fun k hk =>
        hhonM k (le_trans hk (le_trans ((time_mono M) x R (Nat.le_of_lt hj')) (le_max_left _ _)))) hsent
    rw [ht] at ht''
    have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.slot_lt_of_supportCutoff_le M.toSlotLayout F.sched) S (le_of_eq ht''.symm)
    omega
  subst ht
  obtain ⟨hE1, hE2, hE3⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.isEntry_T_h M F) S.C source
  have hET : (M.chainStateOf S.C source).T_h ∈ (x.st j' u).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E j' u
      source _ hsT hE3
  have hts := (tickStep_eq_of_lbl M) x E hl
  have hTI : (M.chainStateOf S.C source).T_h ∈
      (x.tickInput u (M.supportCutoff S.C (sₐ + 1))).tree := by
    unfold Trace.tickInput
    rw [hts]
    exact hET
  exact ⟨sₐ, u, (M.chainStateOf S.C source).T_h, by rw [hts]; exact hj', by rw [hts]; exact hl, hv,
    Activity.not_mem_corruptedAtTime.2 fun k hk => hhonM k (le_trans hk (le_max_left _ _)), hTI,
    hs₀, hE1, hE2.trans (hh.trans hh'), hT'.symm.trans hT, C, hSaved, ancestorEq_trans hE3 hsrcC⟩

/-- **Kit fact, the justified block of an honest state is on the chain, with the updater that
witnesses it.** As `justified_onHonestChainAt_of_caches` (`Lemma85.lean`), with the witness named:
the justified block is an ancestor of, or equal to, the confirmation of slot `s_a` that an updater
`uₐ` of slot `s_a` saved at its own tick to the support cutoff of slot `s_a + 1`, a step before `i`.

Why: `justified_onHonestChainAt_of_caches`'s proof, through `cert_entry_held_of_agree_saved`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `s₀`: the healed slot; `t₀`: the time
  from which the honest attestations name the honest chain; `H`: the threshold; `i`: the step;
  `v`: the validator.

Read aloud: an honest justified block above the threshold is an ancestor of, or equal to, the
confirmation an updater saved at its tick before `i`. -/
theorem justified_onHonestChainAt_of_caches_saved (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ t₀ H i : ℕ) (v : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hRoots : RootsNameBlocksUntil M A x (x.time i))
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time i) t₀))
    (hAgree : HonestAttestationsOnChain M S A x s₀ t₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ t₀ H)
    (hv : v ∉ A.corrupted i)
    (hH : H < (x.st i v).justifiedHeight) :
    ∃ (s_a : ℕ) (uₐ : V), x.tickStep uₐ (M.supportCutoff S.C (s_a + 1)) < i ∧
      x.lbl (x.tickStep uₐ (M.supportCutoff S.C (s_a + 1))) = Event.tick uₐ (M.supportCutoff S.C (s_a + 1)) ∧
      uₐ ∈ updaterAt M S A x s_a ∧ s₀ ≤ s_a ∧
      ∃ C : Block V, (x.tickOutput uₐ (M.supportCutoff S.C (s_a + 1))).savedConfirmation s_a = some C ∧
        (x.st i v).justified.AncestorEq C := by
  obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E i v
  have h1 : 1 ≤ (M.chainStateOf S.C D).h_j := by
    rw [← hhjD]; exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H) hH)
  obtain ⟨hJC, -, -⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).1 h1
  rw [← hJD, ← hhjD] at hJC
  obtain ⟨s_a, uₐ, Eb, hk, hl, hu, -, hEb, hs₀, -, -, hroot, C, hC, hEC⟩ :=
    (cert_entry_held_of_agree_saved M F U Fx) S A x R s₀ t₀ H i v D _ _ E hAdvQ hAgree hOld hD hJC hH
  have hJT : (x.st i v).justified ∈ (x.st i v).tree :=
    ((GoldilocksCorrectness.Record.Statements.Executions.lem57_justification_cache_and_record M F) S A x R E i v).2.2.1
  have hEq : (x.st i v).justified = Eb := hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := i) (v := v) hv le_rfl hJT)
    ((onHonestChainAt_inHonestTreeBy M F U) S A x R E _ uₐ (M.supportCutoff S.C (s_a + 1)) _ Eb hl
      ((time_mono M) x R hk.le) hEb) hroot
  exact ⟨s_a, uₐ, hk, hl, hu, hs₀, C, hC, by rw [hEq]; exact hEC⟩

/-- **Lemma 85, keeping the slot and the updater that witnesses it.** As
`lem85_honest_finalized_on_chain_at` (`Lemma85.lean`), with the witness of `OnHonestChainAt` named:
the finalized block of a validator honest at a step at a time at most `t` is an ancestor of, or
equal to, the confirmation of a slot `s_a` from `s₀` on that an updater `uₐ` of slot `s_a` saved at
its own tick to the support cutoff of slot `s_a + 1`, a step before that step, or before step `i₁`
when that is later. Lemma 86 reads the chain clause of `healed_handover_facts_until` for the
updaters whose tick is by `t`; this names one.

Why: `lem85_honest_finalized_on_chain_at`'s proof, through `justified_onHonestChainAt_of_caches_saved`
and `cert_entry_held_of_agree_saved`, whose witnesses are the certificates' attesters.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `s₀`: the healed slot; `t₀`: the time
  from which the honest attestations name the honest chain; `H`: the threshold; `i₁`: the step
  from which the caches are on the chain; `t`: the bound on the times of the steps.

Read aloud: the block finalized in the node state of a validator honest at a step at a time at most
`t` is an ancestor of, or equal to, the confirmation an updater saved at its tick before that step,
or before step `i₁` when that is later. -/
theorem lem85_honest_finalized_on_chain_at_saved (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ t₀ H i₁ t : ℕ)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hRoots : RootsNameBlocksUntil M A x (max t (x.time i₁)))
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) (x.time i₁))
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (max t (x.time i₁)) t₀))
    (hAgree : HonestAttestationsOnChain M S A x s₀ t₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ t₀ H)
    (hStart : ∀ v : V, v ∉ A.corruptedAtTime x (x.time i₁) →
      CachesOnChain M S A x s₀ H (x.st i₁ v)) :
    ∀ (i : ℕ) (v : V), x.time i ≤ t → v ∉ A.corrupted i →
      ∃ (s_a : ℕ) (uₐ : V), x.tickStep uₐ (M.supportCutoff S.C (s_a + 1)) < max i i₁ ∧
        x.lbl (x.tickStep uₐ (M.supportCutoff S.C (s_a + 1))) = Event.tick uₐ (M.supportCutoff S.C (s_a + 1)) ∧
        uₐ ∈ updaterAt M S A x s_a ∧ s₀ ≤ s_a ∧
        ∃ C : Block V, (x.tickOutput uₐ (M.supportCutoff S.C (s_a + 1))).savedConfirmation s_a = some C ∧
          (x.st i v).finalized.AncestorEq C := by
  intro i v ht hv
  have hit : x.time i ≤ max (t : ℝ) (x.time i₁) := le_trans ht (le_max_left _ _)
  rcases lt_or_ge (x.time i₁) (x.time i) with hgt | hle₁
  · have hge : i₁ ≤ i := ((lt_of_time_lt M) x R hgt).le
    have hv₁ : v ∉ A.corruptedAtTime x (x.time i₁) := Activity.not_mem_corruptedAtTime.2 fun k hk =>
      E.not_mem_corrupted_of_le ((lt_of_time_lt M) x R (lt_of_le_of_lt hk hgt)).le hv
    have hC := (lem84_caches_stay_on_chain_of_honest M F U Fx) S A x R s₀ t₀ H i₁ t E
      ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (le_max_left _ _) hRoots) (hAdvQ.mono (max_le_max (le_max_left _ _) le_rfl)) hAgree hOld hStart i v hv₁ hge ht hv
    obtain ⟨s_a, uₐ, hk, hl, hu, hs₀, C, hC', hJ⟩ := (justified_onHonestChainAt_of_caches_saved M F U Fx) S A x R s₀ t₀ H i v E
      ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hit hRoots) (hAdvQ.mono (max_le_max hit le_rfl)) hAgree hOld hv hC.1
    exact ⟨s_a, uₐ, lt_of_lt_of_le hk (le_max_left _ _), hl, hu, hs₀, C, hC',
      ancestorEq_trans hC.2.2.2.2 hJ⟩
  · obtain ⟨B, hB, hFB⟩ :=
      (GoldilocksCorrectness.Record.Statements.Executions.finalizedFromChain_of_exec M F) S A x R E i v
    rw [hFB]
    rcases Nat.lt_or_ge H (M.chainStateOf S.C B).h_F with hgt | hle
    · obtain ⟨hcert, -, hFBanc, -⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C B).2.2
        (Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le H) hgt))
      obtain ⟨s_a, uₐ, Eb, hk, hl, hu, -, hEb, hs₀, -, -, hroot, C, hC, hEC⟩ :=
        (cert_entry_held_of_agree_saved M F U Fx) S A x R s₀ t₀ H i v B _ _ E
          (hAdvQ.mono (max_le_max hit le_rfl)) hAgree hOld hB hcert hgt
      have hFT := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E i v B _ hB hFBanc
      have hEq : (M.chainStateOf S.C B).F = Eb := hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := i) (v := v) hv hit hFT)
        ((onHonestChainAt_inHonestTreeBy M F U) S A x R E _ uₐ (M.supportCutoff S.C (s_a + 1)) _ Eb hl
          (le_trans ((time_mono M) x R hk.le) hit) hEb) hroot
      rw [hEq]
      exact ⟨s_a, uₐ, lt_of_lt_of_le hk (le_max_left _ _), hl, hu, hs₀, C, hC, hEC⟩
    · obtain ⟨w, hwT⟩ : ∃ w : V, w ∉ A.corruptedAtTime x (x.time i₁) := by
        by_contra hall
        have hall' : ∀ w ∈ (Finset.univ : Finset V),
            ∃ k : ℕ, x.time k ≤ x.time i₁ ∧ w ∈ A.corrupted k := by
          intro w _
          by_contra hn
          exact hall ⟨w, fun hadv => by
            obtain ⟨k, hk, hkc⟩ := Activity.mem_corruptedAtTime.1 hadv
            exact hn ⟨k, hk, hkc⟩⟩
        have h3 := hThird Finset.univ hall'
        have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨v⟩
        rw [Finset.card_univ] at h3
        unfold validator_count at h3
        omega
      have hw : w ∉ A.corrupted i₁ := Activity.not_mem_corruptedAtTime.1 hwT i₁ le_rfl
      obtain ⟨hHw, -, -, hJh, -⟩ := hStart w hwT
      obtain ⟨s_a, uₐ, hk, hl, hu, hs₀, C, hC, hJw⟩ := (justified_onHonestChainAt_of_caches_saved M F U Fx) S A x R s₀ t₀ H i₁ w
        E ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (le_max_right _ _) hRoots) (hAdvQ.mono (max_le_max (le_max_right _ _) le_rfl)) hAgree hOld hw hHw
      have hJT : (x.st i₁ w).justified ∈ (x.st i₁ w).tree :=
        ((GoldilocksCorrectness.Record.Statements.Executions.lem57_justification_cache_and_record M F) S A x R E i₁ w).2.2.1
      have hmax : max (x.time i) (x.time i₁) = x.time i₁ :=
        max_eq_right hle₁
      have hF := (honest_past_finalized_real M F Fx) S A x R E
        hRoots i i₁ v w B _ (by rw [hmax]; exact hThird) hv hw hB hJT
        (by rw [hJh]; exact lt_of_le_of_lt hle hHw) (max_le hit (le_max_right _ _))
      exact ⟨s_a, uₐ, lt_of_lt_of_le hk (le_max_right _ _), hl, hu, hs₀, C, hC,
        ancestorEq_trans hF hJw⟩

/-- **Kit fact, two blocks under confirmations saved by updaters that ticked by `t` are
compatible**, under the chain clause of `healed_handover_facts_until`: for every
slot `σ` whose update some validator ran at a step by `t`, the slot-`σ` confirmations of the updaters
whose tick is by `t` extend the honest chain before `σ` and, when `σ` is `s₀` or a later slot, are
compatible with each other.

Why: for the later of the two slots, the earlier block's confirmation is on the chain before it (or,
at one slot, compatible with the later block's confirmation), and both blocks are ancestors of, or
equal to, their confirmations (`compatible_of_ancestorEq_both`).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `A`, `x`: the setup, the activity, the execution; `s₀`: the healed slot; `t`: the bound;
  `σ`, `σ'`: the two slots; `v`, `v'`: the two updaters; `C`, `C'`: their confirmations; `B`, `B'`:
  the two blocks.

Read aloud: two blocks that are ancestors of confirmations saved by updaters that ticked by `t` are
compatible. -/
theorem compatible_of_saved_by (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (s₀ t σ σ' : ℕ) (v v' : V) (C C' B B' : Block V)
    -- the chain clause of `healed_handover_facts_until`
    (hChain : ∀ (σ k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1)) →
      x.time k ≤ t → ConfirmationsChainBefore M S A x s₀ σ ∧
      ∀ v ∈ updaterAt M S A x σ, x.time (x.tickStep v (M.supportCutoff S.C (σ + 1))) ≤ t →
      ∀ C' : Block V, (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C' →
      (∀ C : Block V, OnHonestChainBefore M S A x s₀ σ C → C.AncestorEq C') ∧
      (s₀ ≤ σ → ∀ v' ∈ updaterAt M S A x σ, x.time (x.tickStep v' (M.supportCutoff S.C (σ + 1))) ≤ t →
      ∀ C'' : Block V, (x.tickOutput v' (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C'' →
      C'.compatible C'' = true))
    -- `v` is an updater of slot `σ` from `s₀` on, its tick to the cutoff by `t`, its confirmation `C`
    (hl : x.lbl (x.tickStep v (M.supportCutoff S.C (σ + 1))) = Event.tick v (M.supportCutoff S.C (σ + 1)))
    (ht : x.time (x.tickStep v (M.supportCutoff S.C (σ + 1))) ≤ t)
    (hv : v ∈ updaterAt M S A x σ) (hs : s₀ ≤ σ)
    (hC : (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C)
    (hBC : B.AncestorEq C)
    -- the same for `v'` at slot `σ'`
    (hl' : x.lbl (x.tickStep v' (M.supportCutoff S.C (σ' + 1))) = Event.tick v' (M.supportCutoff S.C (σ' + 1)))
    (ht' : x.time (x.tickStep v' (M.supportCutoff S.C (σ' + 1))) ≤ t)
    (hv' : v' ∈ updaterAt M S A x σ') (hs' : s₀ ≤ σ')
    (hC' : (x.tickOutput v' (M.supportCutoff S.C (σ' + 1))).savedConfirmation σ' = some C')
    (hBC' : B'.AncestorEq C') :
    B.compatible B' = true := by
  rcases Nat.lt_trichotomy σ σ' with hlt | heq | hgt
  · have hCC := ((hChain σ' _ v' hl' ht').2 v' hv' ht' C' hC').1 C ⟨σ, hlt, hs, v, hv, C, hC, ancestorEq_refl C⟩
    exact GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_both (ancestorEq_trans hBC hCC) hBC'
      ((compatible_iff _ _).2 (Or.inl (ancestorEq_refl C')))
  · subst heq
    exact GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_both hBC hBC'
      (((hChain σ _ v hl ht).2 v hv ht C hC).2 hs v' hv' ht' C' hC')
  · have hCC := ((hChain σ _ v hl ht).2 v hv ht C hC).1 C' ⟨σ', hgt, hs', v', hv', C', hC', ancestorEq_refl C'⟩
    exact GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_both hBC (ancestorEq_trans hBC' hCC)
      ((compatible_iff _ _).2 (Or.inl (ancestorEq_refl C)))

/-! ## Lemma 86, finality safety after healing -/

/-- **Lemma 86, for the readings up to a time `t`.** The proof; the audited statement is in
`Statements/Executions/HealedTopStatements.lean`. Why: for `t ≥ tAwakeEnd`, either a root collision
has hit two blocks honest validators hold by `t`, or roots name blocks up to `t`; then the facts
after the hand-over up to `t` (`healed_handover_facts_until`); Lemma 85 at `i₂`, keeping the slot
and the updater that witnesses it (`lem85_honest_finalized_on_chain_at_saved`), makes every finalized block of a validator honest at a step
at a time at most `t` an ancestor of, or equal to, the confirmation an updater saved at its own tick
by `t`; two such blocks are compatible.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `m`, `r`: the index of the last honest round opening slot and the rounds of the honest round opening slots.

Read aloud: for every time `t` after the phase, unless a collision has hit by `t`, no two honest
validators have finalized conflicting blocks by `t`. -/
theorem lem86_healed_finality_safety_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (r : ℕ → ℕ)
    (hGST : GST ≤ tGAT)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot, every validator outside the adversary set at the support cutoff of the slot
    -- after its first slot is active through the attestations' sync delay after the later of that first slot's duty
    -- window's start and `GST`
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (r i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    -- the time up to which the execution is read, after the phase
    (t : ℕ) (ht : tAwakeEnd ≤ t)
    -- committee sleepiness from `anchorCW S tGAT`, for the slots whose update is at most `t`
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) t)
    -- every tick at a real time at most `t`, to a clock value `c`: committee sleepiness from `anchorCW S tGAT` read up
    -- to `c`
    (hCommitteesTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → (x.time k : ℝ) ≤ t →
      CommitteeSleepinessUntil M S A x (anchorCW S tGAT) c)
    -- every updater of a slot from the first honest round opening slot `r 0 * S.C.R` on, whose update is at
    -- most `t`, is active for the sync delay after the real time of its own tick to the support cutoff of the
    -- next slot
    (hStay : ∀ σ : ℕ, r 0 * S.C.R ≤ σ → M.supportCutoff S.C (σ + 1) ≤ t → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hSeq : HonestOpeningSeq M S A x r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hOpenings : OpeningsOutsideWaitsAndWindows S r m)
    -- fewer than two thirds of the validators corrupted up to `t`
    (hAdvQ : A.AdversaryFewerThanTwoThirdsUntil x (validator_count V) t) :
    RootCollisionAtOpening M S A x r m ∨ RootCollisionHeldBy M S A x t ∨
      ∀ (v₁ v₂ : V) (i j : ℕ), x.HonestThrough A i v₁ → x.HonestThrough A j v₂ →
        x.time i ≤ t → x.time j ≤ t →
        (x.st i v₁).finalized.compatible (x.st j v₂).finalized = true := by
  have hAdvQ' := (adversaryFewerThanQuorumUntil_of_adversaryFewerThanTwoThirdsUntil M F) A x _ hAdvQ
  rcases (rootsNameBlocksUntil_or_collision M) x t with hRootsT | hCol
  swap
  · exact Or.inr (Or.inl hCol)
  rcases (healed_handover_facts_until M F U Fx) S A x R GST tGAT tAwakeEnd m r hGST E
      hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hHoldF hParent hThird hAwake hActive t ht hCommittees hCommitteesTick hStay hSeq hOpenings hAdvQ' with
    hCol | hCol | ⟨s₀, i₂, B₀, ⟨hsc, -⟩, hx2, -, -, -, -, -, -, -, -, hOld, -, hCaches, -, -, hChain⟩
  · exact Or.inl hCol
  · exact Or.inr (Or.inl hCol)
  right; right
  have hx2t : x.time i₂ ≤ t := le_trans hx2 (by exact_mod_cast ht)
  -- the caches row read at step `i₂` is about the state `i₂` leaves: that state is the one after
  -- `i₂` steps, or step `i₂` keeps the time and the adversary set (`step_succ_cases`)
  suffices key : ∀ i₃ : ℕ, x.time i₃ = x.time i₂ →
      (∀ v : V, v ∉ A.corruptedAtTime x (x.time i₃) →
        CachesOnChain M S A x s₀ (M.chainStateOf S.C B₀).h (x.st i₃ v)) →
      ∀ (v₁ v₂ : V) (i j : ℕ), x.HonestThrough A i v₁ → x.HonestThrough A j v₂ →
        x.time i ≤ t → x.time j ≤ t →
        (x.st i v₁).finalized.compatible (x.st j v₂).finalized = true by
    rcases (step_succ_cases M F) x R E i₂ with ⟨-, h⟩ | ⟨ht₂, hc₂⟩
    · exact key i₂ rfl fun v hv => by
        rw [← h v]
        exact hCaches i₂ v le_rfl hx2t (Activity.not_mem_corruptedAtTime.1 hv i₂ le_rfl)
    · exact key (i₂ + 1) ht₂ fun v hv => hCaches i₂ v le_rfl hx2t
        (Activity.not_mem_corruptedAtTime.1 (by rw [← ht₂]; exact hv) i₂ le_rfl)
  intro i₃ hx3 hStart
  have hx3t : x.time i₃ ≤ t := by rw [hx3]; exact hx2t
  have hThird₃ : A.AdversaryFewerThanThirdUntil x (validator_count V) (x.time i₃) :=
    hThird.mono (by rw [hx3]; exact hx2)
  -- Lemma 85 at `i₃`, keeping the slot, read up to `t`
  have hFin := (lem85_honest_finalized_on_chain_at_saved M F U Fx) S A x R s₀
    (M.supportCutoff S.C (s₀ + 1)) (M.chainStateOf S.C B₀).h i₃ t E
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M (max_le le_rfl hx3t) hRootsT) hThird₃
    (hAdvQ'.mono (max_le (max_le le_rfl hx3t) (le_trans hsc.le hx2t)))
    ((lem82_honest_attestations_on_chain M F U) S A x R s₀ E) hOld hStart
  -- the later of two steps at times at most `t` is at a time at most `t`
  have hmx : ∀ a b : ℕ, x.time a ≤ (t : ℝ) → x.time b ≤ (t : ℝ) → x.time (max a b) ≤ (t : ℝ) :=
    fun a b ha hb => by
      rcases le_total a b with h | h
      · rw [max_eq_right h]; exact hb
      · rw [max_eq_left h]; exact ha
  intro v₁ v₂ i j h₁ h₂ hit hjt
  obtain ⟨σ, u, hk, hl, hu, hs, C, hC, hB⟩ := hFin i v₁ hit (h₁ _ le_rfl)
  obtain ⟨σ', u', hk', hl', hu', hs', C', hC', hB'⟩ := hFin j v₂ hjt (h₂ _ le_rfl)
  exact (compatible_of_saved_by M F) S A x s₀ t σ σ' u u' C C' _ _ hChain
    hl (le_trans ((time_mono M) x R hk.le) (hmx i i₃ hit hx3t)) hu hs hC hB
    hl' (le_trans ((time_mono M) x R hk'.le) (hmx j i₃ hjt hx3t)) hu' hs' hC' hB'

/-- **Lemma 86.** The proof; the audited statement is in
`Statements/Executions/HealedTopStatements.lean`. Why: derived from Lemma 86 read up to a time
. For two steps `i` and `j`, at
`t := max tAwakeEnd (max x[i].time x[j].time)`, with the premises bounded at `t` from the unbounded
ones (`committeeSleepinessUntil_of_committeeSleepiness`, `hAdvQ t`): a collision at an opening is
the first disjunct; a collision among the blocks held by `t` contradicts roots naming blocks for all
time (`rootsNameBlocksUntil_of_rootsNameBlocks`, `not_rootsNameBlocksUntil_iff_collision`);
otherwise the two finalized blocks are compatible.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `m`, `r`: the index of the last honest round opening slot and the rounds of the honest round opening slots.

Read aloud: once the phase has lasted through enough honest round opening slots, two honest validators never
finalize conflicting blocks, at any two steps, unless a digest collision hit an honest proposal. -/
theorem lem86_healed_finality_safety
    (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (r : ℕ → ℕ)
    (hGST : GST ≤ tGAT)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot, every validator outside the adversary set at the support cutoff of the slot
    -- after its first slot is active through the attestations' sync delay after the later of that first slot's duty
    -- window's start and `GST`
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (r i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hRoots : RootsNameBlocks M A x)
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepiness M S A x (anchorCW S tGAT))
    -- every updater of a slot from the first honest round opening slot `r 0 * S.C.R` on is active for the
    -- sync delay after the real time of its own tick to the support cutoff of the next slot
    --
    (hStay : ∀ σ : ℕ, r 0 * S.C.R ≤ σ → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hSeq : HonestOpeningSeq M S A x r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hOpenings : OpeningsOutsideWaitsAndWindows S r m)
    (hAdvQ : ∀ t : ℕ, A.AdversaryFewerThanTwoThirdsUntil x (validator_count V) t) :
    RootCollisionAtOpening M S A x r m ∨
      ∀ (v₁ v₂ : V) (i j : ℕ), x.HonestThrough A i v₁ → x.HonestThrough A j v₂ →
        (x.st i v₁).finalized.compatible (x.st j v₂).finalized = true := by
  by_cases hO : RootCollisionAtOpening M S A x r m
  · exact Or.inl hO
  right
  intro v₁ v₂ i j h₁ h₂
  -- the premises read up to a natural number at least `tAwakeEnd` and the times of `i` and `j`
  obtain ⟨T, hT⟩ := exists_nat_ge (max (x.time i) (x.time j))
  have ht : tAwakeEnd ≤ max tAwakeEnd T := le_max_left _ _
  have hTt : ((T : ℕ) : ℝ) ≤ ((max tAwakeEnd T : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
  rcases (lem86_healed_finality_safety_until M F U Fx) S A x R GST tGAT tAwakeEnd m r hGST E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy
      hΔs Sy_F hΔs_F hHoldF hParent hThird hAwake hActive _ ht
      (committeeSleepinessUntil_of_committeeSleepiness M S A x _ _ hCommittees)
        (fun _ _ _ _ _ => committeeSleepinessUntil_of_committeeSleepiness M S A x _ _ hCommittees) (fun σ h1 _ => hStay σ h1) hSeq hOpenings
      (hAdvQ _) with hc | hc | h
  · exact absurd hc hO
  · exact absurd ((rootsNameBlocksUntil_of_rootsNameBlocks M) x F R E _ hRoots)
      (((not_rootsNameBlocksUntil_iff_collision M) x _).2 hc)
  · exact h v₁ v₂ i j h₁ h₂ (by have := le_max_left (x.time i) (x.time j); linarith)
      (by have := le_max_right (x.time i) (x.time j); linarith)

/-!-/

/-- **A slot start at least `t` at which no slot's update is half run**.
The start of slot `t`, `M.slotStart S.C t = 4Δ · t`, is at least `t`, and `TicksToUpdatesBy` holds
there: for a slot `σ` with `σ + 2 ≤ t`, every tick to a clock value at most the support cutoff of
slot `σ + 1` is at most `ΔClockBehind` after it, and that cutoff is at least `2Δ` before the start
of slot `t`; for a slot `σ` with `t ≤ σ + 1`, that cutoff is at least `2Δ` after the start of slot
`t`, and every tick to it at most `ΔClockAhead` before it, so neither trigger fires.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `A`, `x`: the activity, the execution; `E`: the environment's facts; `t`: the time.

Read aloud: every time is followed by a slot start at which every update due or begun is complete. -/
theorem exists_ticksBy_ge (U : UniformSchedule M.toSlotLayout) (S : Setup V) {A : Activity V}
    (x : Trace V (NamedObject V) M.N)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release
      ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (t : ℕ) :
    t ≤ M.slotStart S.C t ∧ TicksToUpdatesBy M S x (M.slotStart S.C t) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hst : ∀ s : ℕ, M.slotStart S.C s = 4 * Δ S * s :=
    fun s => (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hcut : ∀ s : ℕ, M.supportCutoff S.C s = 4 * Δ S * s + 2 * Δ S := fun s => by
    obtain ⟨-, h2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s
    rw [h2, hst]
  refine ⟨by rw [hst]; nlinarith, ?_⟩
  intro σ k u c htrig hk hc
  have hcR : (c : ℝ) ≤ ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) := by exact_mod_cast hc
  rcases Nat.lt_or_ge (σ + 1) t with hlt | hge
  · -- slot `σ + 1` starts before slot `t`: its support cutoff is at least `2Δ` before the start of slot `t`
    have h1 : M.supportCutoff S.C (σ + 1) + 2 * Δ S ≤ M.slotStart S.C t := by
      have := Nat.mul_le_mul_left (4 * Δ S) (show σ + 2 ≤ t by omega)
      rw [hcut, hst]
      nlinarith
    have h1R : ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) + 2 * Δ S ≤ ((M.slotStart S.C t : ℕ) : ℝ) := by
      exact_mod_cast h1
    have hka := (E.tick_active k u c hk).2.2
    linarith
  · -- slot `t` starts at or before slot `σ + 1`: the support cutoff of slot `σ + 1` is at least `2Δ` after it
    exfalso
    have h1 : M.slotStart S.C t + 2 * Δ S ≤ M.supportCutoff S.C (σ + 1) := by
      have := Nat.mul_le_mul_left (4 * Δ S) hge
      rw [hcut, hst]
      nlinarith
    have h1R : ((M.slotStart S.C t : ℕ) : ℝ) + 2 * Δ S ≤ ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) := by
      exact_mod_cast h1
    rcases htrig with h | ⟨k', u', hk', hk't⟩
    · omega
    · have := (E.tick_active k' u' _ hk').2.1
      linarith

/-- **The confirmations chain before the slot after a slot updated by `t`, at a time `t` at which
no slot's update is half run**. From the hand-over facts' chain clause
read up to `t` (the chain before slot `σ` and, for the updaters of `σ` whose tick to its update is
by `t`, their confirmations extending it and compatible with each other) and `TicksToUpdatesBy M S x t`:
at a slot `σ` to whose update some validator ticked by `t`, every updater of `σ` ticked to it by
`t`, so the clause's halves cover every pair of slot `σ`.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `A`, `x`: the activity, the execution; `E`: the environment's facts;
- `s₀`: the first slot of the chain; `t`: the time;
- `hClause`: the hand-over facts' chain clause; `hTicks`: no slot's update is half run at `t`.

Read aloud: at a time at which no update is half run, the updaters' confirmations of the slots from
`s₀` up to and including every slot updated by then form one chain. -/
theorem confirmationsChainBefore_succ_of_handover (S : Setup V) {A : Activity V}
    (x : Trace V (NamedObject V) M.N)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release
      ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (s₀ t : ℕ)
    (hClause : ∀ (σ k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1)) →
      x.time k ≤ t → ConfirmationsChainBefore M S A x s₀ σ ∧
      ∀ v ∈ updaterAt M S A x σ, x.time (x.tickStep v (M.supportCutoff S.C (σ + 1))) ≤ t →
      ∀ C' : Block V, (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C' →
      (∀ C : Block V, OnHonestChainBefore M S A x s₀ σ C → C.AncestorEq C') ∧
      (s₀ ≤ σ → ∀ v' ∈ updaterAt M S A x σ, x.time (x.tickStep v' (M.supportCutoff S.C (σ + 1))) ≤ t →
      ∀ C'' : Block V, (x.tickOutput v' (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C'' →
      C'.compatible C'' = true))
    (hTicks : TicksToUpdatesBy M S x t) :
    ∀ (σ k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1)) → x.time k ≤ t →
      ConfirmationsChainBefore M S A x s₀ (σ + 1) := by
  intro σ k u hk hkt
  obtain ⟨hChain, hHalf⟩ := hClause σ k u hk hkt
  -- every updater of `σ` ticked to its update by `t`
  have hBy : ∀ v ∈ updaterAt M S A x σ, x.time (x.tickStep v (M.supportCutoff S.C (σ + 1))) ≤ t := by
    intro v hv
    have hv' := hv
    unfold updaterAt at hv'
    obtain ⟨K, hK, -⟩ := (Activity.mem_activeThroughoutToTick).1 hv'
    rw [(tickStep_eq_of_lbl M) x E hK]
    exact hTicks σ K v _ (Or.inr ⟨k, u, hk, hkt⟩) hK le_rfl
  intro s s'' v v' C C' hs hss hs'' hv hv' hC hC'
  rcases Nat.lt_or_ge s'' σ with hlt | hge
  · exact hChain s s'' v v' C C' hs hss hlt hv hv' hC hC'
  obtain rfl : s'' = σ := by omega
  obtain ⟨hAnc, -⟩ := hHalf v' hv' (hBy v' hv') C' hC'
  refine ⟨fun hlt => hAnc C ⟨s, hlt, hs, v, hv, C, hC, ancestorEq_refl C⟩, fun heq => ?_⟩
  subst heq
  obtain ⟨-, hComp⟩ := hHalf v hv (hBy v hv) C hC
  exact hComp hs v' hv' (hBy v' hv') C' hC'

/-- **The confirmations chain before the slot after every slot whose update is at most `t`, at a time `t` at
which no slot's update is half run**. As `confirmationsChainBefore_succ_of_handover`,
for a slot `σ` whose update is at most `t`: by induction on `σ`; a slot some validator ticked to the update of is
the case of `confirmationsChainBefore_succ_of_handover` (that tick is by `t`, `TicksToUpdatesBy`'s first trigger),
and a slot no validator ticked to the update of has no updater, so the chain before it is the chain before the
slot after it.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `A`, `x`: the activity, the execution; `E`: the environment's facts;
- `s₀`: the first slot of the chain; `t`: the time;
- `hClause`: the hand-over facts' chain clause; `hTicks`: no slot's update is half run at `t`.

Read aloud: at a time at which no update is half run, the updaters' confirmations of the slots from `s₀` up to
every slot whose update is due by then form one chain. -/
theorem confirmationsChainBefore_of_handover_le (S : Setup V) {A : Activity V}
    (x : Trace V (NamedObject V) M.N)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release
      ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (s₀ t : ℕ)
    (hClause : ∀ (σ k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1)) →
      x.time k ≤ t → ConfirmationsChainBefore M S A x s₀ σ ∧
      ∀ v ∈ updaterAt M S A x σ, x.time (x.tickStep v (M.supportCutoff S.C (σ + 1))) ≤ t →
      ∀ C' : Block V, (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C' →
      (∀ C : Block V, OnHonestChainBefore M S A x s₀ σ C → C.AncestorEq C') ∧
      (s₀ ≤ σ → ∀ v' ∈ updaterAt M S A x σ, x.time (x.tickStep v' (M.supportCutoff S.C (σ + 1))) ≤ t →
      ∀ C'' : Block V, (x.tickOutput v' (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C'' →
      C'.compatible C'' = true))
    (hTicks : TicksToUpdatesBy M S x t) :
    ∀ σ : ℕ, M.supportCutoff S.C (σ + 1) ≤ t → ConfirmationsChainBefore M S A x s₀ (σ + 1) := by
  have step : ∀ σ : ℕ, ConfirmationsChainBefore M S A x s₀ σ → M.supportCutoff S.C (σ + 1) ≤ t →
      ConfirmationsChainBefore M S A x s₀ (σ + 1) := by
    intro σ hC hσ
    by_cases hex : ∃ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1))
    · obtain ⟨k, u, hk⟩ := hex
      exact (confirmationsChainBefore_succ_of_handover M F) S x E s₀ t hClause hTicks σ k u hk
        (hTicks σ k u _ (Or.inl hσ) hk le_rfl)
    · intro s s'' v v' C C' hs hss hs'' hv hv' hC₁ hC₂
      rcases Nat.lt_or_ge s'' σ with hlt | hge
      · exact hC s s'' v v' C C' hs hss hlt hv hv' hC₁ hC₂
      obtain rfl : s'' = σ := by omega
      unfold updaterAt at hv'
      obtain ⟨K, hK, -⟩ := (Activity.mem_activeThroughoutToTick).1 hv'
      exact absurd ⟨K, v', hK⟩ hex
  intro σ
  induction σ with
  | zero =>
    intro h
    exact step 0 (fun s s'' v v' C C' _ _ h3 => absurd h3 (Nat.not_lt_zero _)) h
  | succ n ih =>
    intro h
    exact step (n + 1) (ih (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono
      M.toSlotLayout F.sched) S (Nat.le_succ _)) h)) h

/-! ## Lemma 90, the confirmed tip after healing -/

/-- **Lemma 90, for the readings up to a time `t`.** The proof; the audited statement is in
`Statements/Executions/HealedTopStatements.lean`. Why: for `t ≥ tAwakeEnd`, either a root collision
has hit two blocks honest validators hold by `t`, or roots name blocks up to `t`; then the facts
after the hand-over up to `t` (`healed_handover_facts_until`); every honest record after the support
cutoff of slot `s₀ + 1` is the confirmation of a slot whose update ran by then
(`lem90a_latest_confirmed_honest_at`); the chain invariant and the lock invariant at every slot
whose update is at most `t` (`lem81_inv_before`); Lemma 90's agreement, growth and inclusion on the
chain before a slot from the time of `i₂` to `t` (`lem90_confirmed_agree_before`,
`lem90_confirmed_monotone_before`, `lem90_confirmed_included_before`); the agreement and the growth
moved from the time of `i₂` to `tAwakeEnd`, and the inclusion read from `tAwakeEnd` itself
; the fourth from the agreement and the inclusion
(`confirmedExtendedBetween_of_agree_included`), every slot starting after `tAwakeEnd` being at least
`2` (`two_le_of_after_phase`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `m`, `r`: the index of the last honest round opening slot and the rounds of the honest round opening slots.

Read aloud: for every time `t` after the phase, unless a collision has hit by `t`, up to `t` honest
validators agree on the confirmed tip, it only grows, and every honest proposal joins it and
strictly extends what was confirmed before it. -/
theorem lem90_healed_confirmed_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (r : ℕ → ℕ)
    (hGST : GST ≤ tGAT)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot, every validator outside the adversary set at the support cutoff of the slot
    -- after its first slot is active through the attestations' sync delay after the later of that first slot's duty
    -- window's start and `GST`
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (r i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    -- the time up to which the execution is read, after the phase
    (t : ℕ) (ht : tAwakeEnd ≤ t)
    -- `t` is not inside any slot's update: at every slot whose update is at most `t`, or to whose update some
    -- validator ticked at a real time at most `t`, every tick to a clock value at most that update is at a real
    -- time at most `t`
    (hTicksBy : TicksToUpdatesBy M S x t)
    -- committee sleepiness from `anchorCW S tGAT`, for the slots whose update is at most `t`
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) t)
    -- every tick at a real time at most `t`, to a clock value `c`: committee sleepiness from `anchorCW S tGAT` read up
    -- to `c`
    (hCommitteesTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → (x.time k : ℝ) ≤ t →
      CommitteeSleepinessUntil M S A x (anchorCW S tGAT) c)
    -- every updater of a slot from the first honest round opening slot `r 0 * S.C.R` on, whose update is at
    -- most `t`, is active for the sync delay after the real time of its own tick to the support cutoff of the
    -- next slot
    (hStay : ∀ σ : ℕ, r 0 * S.C.R ≤ σ → M.supportCutoff S.C (σ + 1) ≤ t → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hSeq : HonestOpeningSeq M S A x r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hOpenings : OpeningsOutsideWaitsAndWindows S r m)
    -- fewer than two thirds of the validators corrupted up to `t`
    (hAdvQ : A.AdversaryFewerThanTwoThirdsUntil x (validator_count V) t)
    -- at every slot whose next slot starts at or after `tAwakeEnd` and whose update is at most `t`, the honest active committee
    -- members are active through the sync delay after Lemma 12's read time of the slot; at every such slot with an
    -- honest opener, its proposer through the sync delay after one delay or one sync delay before its start
    --
    (hHold : ∀ s' : ℕ, tAwakeEnd ≤ M.slotStart S.C (s' + 1) → M.supportCutoff S.C (s' + 1) ≤ t →
      ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : ∀ s : ℕ, tAwakeEnd ≤ M.slotStart S.C s → M.supportCutoff S.C (s + 1) ≤ t → HonestOpenerAt M S A x s →
      S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
        (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs)) :
    RootCollisionAtOpening M S A x r m ∨ RootCollisionHeldBy M S A x t ∨
      (ConfirmedAgreeBetween M S A x tAwakeEnd t ∧
        ConfirmedMonotoneBetween M S A x tAwakeEnd t ∧
        ConfirmedIncludedBetween M S A x tAwakeEnd t ∧
        ConfirmedExtendedByHonestProposalsBetween M S A x tAwakeEnd t) := by
  have hAdvQ' := (adversaryFewerThanQuorumUntil_of_adversaryFewerThanTwoThirdsUntil M F) A x _ hAdvQ
  rcases (rootsNameBlocksUntil_or_collision M) x t with hRootsT | hCol
  swap
  · exact Or.inr (Or.inl hCol)
  have hOwner : VotesCastByOwner M A x :=
    (votesCastByOwner_of_unforgeability M F) S A x R E
  rcases (healed_handover_facts_until M F U Fx) S A x R GST tGAT tAwakeEnd m r hGST E
      hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hHoldF hParent hThird hAwake hActive t ht hCommittees
      hCommitteesTick hStay hSeq hOpenings hAdvQ' with
    hCol | hCol | ⟨s₀, i₂, B₀, ⟨hsc, hscTick⟩, hx2, hx2s, -, hGST', hAnc, hB₀slot, hBase, hBaseSaved, hUpd, hOld,
      -, hCaches, hVF, hUF, hChain⟩
  · exact Or.inl hCol
  · exact Or.inr (Or.inl hCol)
  right; right
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have htR : (tAwakeEnd : ℝ) ≤ t := by exact_mod_cast ht
  have hcm : ∀ a b : ℕ, a ≤ b → M.supportCutoff S.C a ≤ M.supportCutoff S.C b := fun a b h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h
  have hGSTs : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀ :=
    gst_sync_of_anchor M F U S hGST hΔs hAnc (by linarith)
  -- the support cutoff of slot `s₀ + 1` is at most `t`
  have hc0t : M.supportCutoff S.C (s₀ + 1) ≤ t := by
    have : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) ≤ t := by linarith
    exact_mod_cast this
  -- the records, on the chain at a slot whose update ran by then
  have hLatest0 := (lem90a_latest_confirmed_honest_at M F U) S A x R s₀ B₀ E hSkew
    hB₀slot hBase hBaseSaved hUpd
  have hLatest : ∀ (i : ℕ) (v : V), x.time i₂ ≤ x.time i → x.time i ≤ t →
      v ∉ A.corrupted i → (∃ σ : ℕ, x.lbl (x.tickStep v (M.supportCutoff S.C (σ + 1))) = Event.tick v (M.supportCutoff S.C (σ + 1)) ∧
        x.tickStep v (M.supportCutoff S.C (σ + 1)) < i + 1 ∧
        OnHonestChainAt M S A x s₀ σ (x.st (i + 1) v).latestConfirmed) ∧
        (x.st (i + 1) v).latestConfirmed ∈ (x.st (i + 1) v).tree := by
    intro i v h _ hv
    classical
    have hvU : v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1)) := Activity.not_mem_corruptedAtTime.2
      fun k hk => E.not_mem_corrupted_of_le ((lt_of_time_lt M) x R (lt_of_le_of_lt hk (lt_of_lt_of_le hsc h))).le hv
    have hvS : v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1)) ∪
        Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
          x.lbl k = Event.tick w (M.supportCutoff S.C (s₀ + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k) := by
      rw [Finset.mem_union, not_or]
      refine ⟨hvU, fun hm => ?_⟩
      obtain ⟨-, k, w, hk, -, hvk⟩ := Finset.mem_filter.1 hm
      exact E.not_mem_corrupted_of_le ((lt_of_time_lt M) x R (lt_of_lt_of_le (hscTick k w hk) h)).le hv hvk
    have hvu := hUpd v hvU
    unfold updaterAt at hvu
    obtain ⟨K, hK, -⟩ := (Activity.mem_activeThroughoutToTick).1 hvu
    have hKi : x.tickStep v (M.supportCutoff S.C (s₀ + 1)) < i := by
      rw [(tickStep_eq_of_lbl M) x E hK]
      exact (lt_of_time_lt M) x R (lt_of_lt_of_le (hscTick K v hK) h)
    rcases (step_succ_cases M F) x R E i with ⟨-, hst⟩ | ⟨-, hc₁⟩
    · rw [hst v]
      obtain ⟨⟨σ, hσ, hl, hlt, u, hu, hsv⟩, hmem⟩ := hLatest0 i v hvS hKi hv
      exact ⟨⟨σ, hl, by omega, hσ, u, hu, _, hsv, ancestorEq_refl _⟩, hmem⟩
    · obtain ⟨⟨σ, hσ, hl, hlt, u, hu, hsv⟩, hmem⟩ :=
        hLatest0 (i + 1) v hvS (by omega) (by rw [hc₁]; exact hv)
      exact ⟨⟨σ, hl, hlt, hσ, u, hu, _, hsv, ancestorEq_refl _⟩, hmem⟩
  -- the chain invariant and the lock invariant at the slots whose update is at most `t`
  have hInvT : ∀ s : ℕ, s₀ < s → M.supportCutoff S.C (s + 1) ≤ t →
      ChainInvFor M S A x (honestActiveAt M S A x s)
        (OnHonestChainBefore M S A x s₀ s) s ∧
      ∀ u ∈ honestActiveAt M S A x s,
        LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u := by
    intro s hs hst
    have hsr : M.supportCutoff S.C (s + 1 - 1) ≤ t := by
      rw [Nat.add_sub_cancel]
      exact le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ s)) hst
    exact (lem81_inv_before M F U) S A x R GST s₀ (anchorCW S tGAT) (s + 1) B₀ E hNet hSkew hRedeliver Sy hΔs
       ((GoldilocksCorrectness.Record.Statements.Executions.RootsNameBlocksUntil.mono M) hsr hRootsT)
       (fun k u c hk hc => (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
          ((tick_time_le_of_clock_le M F) x E (T := (t : ℝ)) (c₀ := M.supportCutoff S.C (s + 1 - 1))
            (by
              rw [Nat.add_sub_cancel]
              obtain ⟨-, h2, -, h4, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s
              obtain ⟨-, h2', -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s + 1)
              have hst' : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ t := by exact_mod_cast hst
              have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast one_le_Δ S
              rw [h2', h4] at hst'
              rw [h2]
              push_cast at hst' ⊢
              linarith) k u c hk hc) hRootsT) hParent hOwner hGSTs (hCommittees.mono M hst) hAnc hB₀slot
      hBase hBaseSaved
      (fun s' h₁ h₂ => hVF s' h₁ (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hst))
      (fun s' h₁ h₂ v hv => hUF s' h₁ v hv (by
        have hv' := hv
        unfold updaterAt at hv'
        obtain ⟨K, hK, -⟩ := (Activity.mem_activeThroughoutToTick).1 hv'
        rw [(tickStep_eq_of_lbl M) x E hK]
        exact hTicksBy s K v _ (Or.inl hst) hK (hcm _ _ (by omega)))) s hs
      (Nat.lt_succ_self s)
  have hChainK : ∀ (σ k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1)) →
      x.time k ≤ t → ConfirmationsChainBefore M S A x s₀ (σ + 1) :=
    (confirmationsChainBefore_succ_of_handover M F) S x E s₀ t hChain hTicksBy
  have hAnc₂ : anchorCW S tGAT ≤ x.time i₂ := by
    have h1 : M.slotStart S.C (s₀ + 1) ≤ M.supportCutoff S.C (s₀ + 1) := by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U),
        (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U)]
      omega
    have h2 : ((anchorCW S tGAT : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) := by
      exact_mod_cast le_trans hAnc h1
    linarith
  suffices h3 : ConfirmedAgreeBetween M S A x tAwakeEnd t ∧
      ConfirmedMonotoneBetween M S A x tAwakeEnd t ∧
      ConfirmedIncludedBetween M S A x tAwakeEnd t from
    ⟨h3.1, h3.2.1, h3.2.2, (confirmedExtendedBetween_of_agree_included M F U) S A x R E hSkew
      tAwakeEnd t ((two_le_of_after_phase M F U) hSeq) h3.1 h3.2.2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro v₁ v₂ i j h₁ h₂ hi hj hit hjt
    exact (lem90_confirmed_agree_before M F U Fx) S A x R s₀ (M.chainStateOf S.C B₀).h i₂ t
      E hRootsT (hAdvQ'.mono (max_le le_rfl (by exact_mod_cast hc0t))) hOld hChainK (fun i v h₁ h₂ hv => (hLatest i v h₁ h₂ hv).1)
      hCaches v₁ v₂ i j h₁ h₂ (le_trans hx2 hi) (le_trans hx2 hj) hit hjt
  · intro v i j hij hj hi hjt
    exact (lem90_confirmed_monotone_before M F U Fx) S A x R s₀ (M.chainStateOf S.C B₀).h i₂
      t E hRootsT (hAdvQ'.mono (max_le le_rfl (by exact_mod_cast hc0t))) hOld hChainK hLatest hCaches v i j hij hj (le_trans hx2 hi) hjt
  · intro s hs hst hp
    exact (lem90_confirmed_included_before M F U Fx) S A x R GST s₀ (anchorCW S tGAT) i₂
      (M.chainStateOf S.C B₀).h t tAwakeEnd E hNet hSkew hRedeliver Sy hΔs hRootsT hParent hAdvQ'
      hCommittees hAnc₂ hGSTs hsc.le (fun s hs => ⟨(hx2s s hs).1, fun k hk => (hx2s s hs).2 k _ hk⟩) hChainK (fun s hs hst => (hInvT s hs hst).1)
      (fun s hs hst => (hInvT s hs hst).2)
      (fun u hu => (base_locks_on_chain M F U) S A x R s₀ (anchorCW S tGAT) B₀ u E
        (hCommittees.mono M hc0t) hAnc hB₀slot hBase hBaseSaved hu)
      hOld hHold hHoldP hCaches hLatest s hs hst hp

/-- **Lemma 90.** The proof; the audited statement is in
`Statements/Executions/HealedTopStatements.lean`. Why: derived from Lemma 90 read up to a time
. At every `t ≥ tAwakeEnd`, with the premises bounded at
`t` from the unbounded ones (`committeeSleepinessUntil_of_committeeSleepiness`, `hAdvQ t`): a
collision at an opening is the first disjunct; a collision among the blocks held by `t` contradicts
roots naming blocks for all time (`rootsNameBlocksUntil_of_rootsNameBlocks`,
`not_rootsNameBlocksUntil_iff_collision`); otherwise the agreement, the growth and the inclusion hold
from `tAwakeEnd` to `t`. The agreement and the growth from `tAwakeEnd` on are those read at the later
step's time; the inclusion from `tAwakeEnd` on is the inclusion read up to every time
(`confirmedIncludedAfterHealing_iff`, a reading up to `t < tAwakeEnd` from the one up to
`tAwakeEnd`); the fourth from the agreement and the inclusion (`confirmedExtended_of_agree_included`),
every slot starting after `tAwakeEnd` being at least `2` (`two_le_of_after_phase`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `m`, `r`: the index of the last honest round opening slot and the rounds of the honest round opening slots.

Read aloud: after the phase, honest validators agree on the confirmed tip, it only grows, every
honest proposal joins it and strictly extends what was confirmed before it, unless a digest
collision hit an honest proposal. -/
theorem lem90_healed_confirmed
    (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (r : ℕ → ℕ)
    (hGST : GST ≤ tGAT)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot, every validator outside the adversary set at the support cutoff of the slot
    -- after its first slot is active through the attestations' sync delay after the later of that first slot's duty
    -- window's start and `GST`
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (r i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hRoots : RootsNameBlocks M A x)
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepiness M S A x (anchorCW S tGAT))
    -- every updater of a slot from the first honest round opening slot `r 0 * S.C.R` on is active for the
    -- sync delay after the real time of its own tick to the support cutoff of the next slot
    --
    (hStay : ∀ σ : ℕ, r 0 * S.C.R ≤ σ → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hSeq : HonestOpeningSeq M S A x r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hOpenings : OpeningsOutsideWaitsAndWindows S r m)
    (hAdvQ : ∀ t : ℕ, A.AdversaryFewerThanTwoThirdsUntil x (validator_count V) t)
    -- at every slot whose next slot starts at or after `tAwakeEnd`, the honest active committee
    -- members are active through the sync delay after Lemma 12's read time of the slot; at every such slot with an
    -- honest opener, its proposer through the sync delay after one delay or one sync delay before its start
    --
    (hHold : ∀ s' : ℕ, tAwakeEnd ≤ M.slotStart S.C (s' + 1) →
      ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : ∀ s : ℕ, tAwakeEnd ≤ M.slotStart S.C s → HonestOpenerAt M S A x s →
      S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
        (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs)) :
    RootCollisionAtOpening M S A x r m ∨
      (ConfirmedAgreeAfterHealing M S A x tAwakeEnd ∧
        ConfirmedMonotoneAfterHealing M S A x tAwakeEnd ∧
        ConfirmedIncludedAfterHealing M S A x tAwakeEnd ∧
        ConfirmedExtendedByHonestProposals M S A x tAwakeEnd) := by
  by_cases hO : RootCollisionAtOpening M S A x r m
  · exact Or.inl hO
  right
  -- Lemma 90 read up to every `t ≥ tAwakeEnd`, its collisions refuted
  have hall : ∀ t : ℕ, tAwakeEnd ≤ t → TicksToUpdatesBy M S x t →
      ConfirmedAgreeBetween M S A x tAwakeEnd t ∧ ConfirmedMonotoneBetween M S A x tAwakeEnd t ∧
        ConfirmedIncludedBetween M S A x tAwakeEnd t ∧
        ConfirmedExtendedByHonestProposalsBetween M S A x tAwakeEnd t := by
    intro t ht hTk
    rcases (lem90_healed_confirmed_until M F U Fx) S A x R GST tGAT tAwakeEnd m r hGST E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs
        Sy_F hΔs_F hHoldF hParent hThird hAwake hActive t ht hTk
        (committeeSleepinessUntil_of_committeeSleepiness M S A x _ _ hCommittees)
        (fun _ _ _ _ _ => committeeSleepinessUntil_of_committeeSleepiness M S A x _ _ hCommittees) (fun σ h1 _ => hStay σ h1) hSeq hOpenings
        (hAdvQ _) (fun s' h1 _ => hHold s' h1) (fun s h1 _ => hHoldP s h1) with hc | hc | h
    · exact absurd hc hO
    · exact absurd ((rootsNameBlocksUntil_of_rootsNameBlocks M) x F R E _ hRoots)
        (((not_rootsNameBlocksUntil_iff_collision M) x _).2 hc)
    · exact h
  -- a slot start at least `tAwakeEnd` and `T` at which no slot's update is half run
  have hT₂ : ∀ T : ℕ, ∃ t₂ : ℕ, tAwakeEnd ≤ t₂ ∧ T ≤ t₂ ∧ TicksToUpdatesBy M S x t₂ := fun T => by
    obtain ⟨h1, h2⟩ := (exists_ticksBy_ge M F U) S x E hSkew (max tAwakeEnd T)
    exact ⟨_, le_trans (le_max_left _ _) h1, le_trans (le_max_right _ _) h1, h2⟩
  have hAgree : ConfirmedAgreeAfterHealing M S A x tAwakeEnd := by
    intro v₁ v₂ i j h₁ h₂ hi hj
    obtain ⟨T, hT⟩ := exists_nat_ge (max (x.time i) (x.time j))
    obtain ⟨t₂, ht₂, hTt₂, hTk⟩ := hT₂ T
    have hTt : ((T : ℕ) : ℝ) ≤ ((t₂ : ℕ) : ℝ) := by exact_mod_cast hTt₂
    exact (hall t₂ ht₂ hTk).1 v₁ v₂ i j h₁ h₂
      hi hj (le_trans (le_trans (le_max_left (x.time i) (x.time j)) hT) hTt)
      (le_trans (le_trans (le_max_right (x.time i) (x.time j)) hT) hTt)
  have hMono : ConfirmedMonotoneAfterHealing M S A x tAwakeEnd := by
    intro v i j hij hj hi
    obtain ⟨T, hT⟩ := exists_nat_ge (x.time j)
    obtain ⟨t₂, ht₂, hTt₂, hTk⟩ := hT₂ T
    have hTt : ((T : ℕ) : ℝ) ≤ ((t₂ : ℕ) : ℝ) := by exact_mod_cast hTt₂
    exact (hall t₂ ht₂ hTk).2.1 v i j hij hj hi (le_trans hT hTt)
  have hIncl : ConfirmedIncludedAfterHealing M S A x tAwakeEnd := by
    refine ((confirmedIncludedAfterHealing_iff M) S A x tAwakeEnd).2 fun t => ?_
    -- the reading up to `t` from the one up to a later slot start `t₂` at which no update is half run
    obtain ⟨t₂, ht₂, htt₂, hTk⟩ := hT₂ t
    have h := (hall t₂ ht₂ hTk).2.2.1
    intro s hs hst hp
    obtain ⟨h1, h2⟩ := h s hs (le_trans hst htt₂) hp
    refine ⟨h1, fun b hb => ?_⟩
    rcases h2 b hb with hc | ⟨h3, h4⟩
    · exact Or.inl hc
    · exact Or.inr ⟨fun v hv hvt => h3 v hv (le_trans hvt (by exact_mod_cast htt₂)),
        fun v j s' hv hss' hact hlt hct hjt =>
        h4 v j s' hv hss' hact hlt (le_trans hct htt₂) (le_trans hjt (by exact_mod_cast htt₂))⟩
  exact ⟨hAgree, hMono, hIncl, (confirmedExtended_of_agree_included M F U) S A x R E hSkew tAwakeEnd
    ((two_le_of_after_phase M F U) hSeq) hAgree hIncl⟩

end GoldilocksCorrectness.Record.Proofs.Executions

