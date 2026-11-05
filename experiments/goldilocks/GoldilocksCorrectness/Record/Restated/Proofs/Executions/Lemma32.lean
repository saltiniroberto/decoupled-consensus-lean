module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma31
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ConfirmationSteps
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickUpdateState
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickWindowKit
public import GoldilocksCorrectness.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma31
public import GoldilocksCorrectness.Proofs.Executions.ConfirmationSteps
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma32, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma32.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: a confirmation saved right after the support
cutoff of slot `s + 1` is saved by an outcome of the tick at that cutoff, and Lemma 32, the saved
confirmations of two honest validators are compatible. The page's routine-level theorems are the
facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart one_le_Δ
  slotStart_eq slot_eq_of_mem supportCutoff_cast supportCutoff_eq viewFreeze_eq voteTime_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Statements.Routines (expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- A block saved as the confirmation of slot `s` in the state `v`'s tick to the support cutoff of slot
`s + 1` leaves is saved by an outcome of that tick, from the state it starts from, awake for slot
`s + 1`, when `v` is active from one clock bound `ΔClockAhead` before the duty window's start of slot
`s + 1` to one clock bound `ΔClockBehind` after that cutoff.

Why: that window makes `v` an updater of slot `s`, active up to its tick to the cutoff
(`activeThroughoutToTick_of_dutyWindow`), and an updater's saved confirmation is what its update
saved (`update_of_saved_confirmation_of_updater`). The window is widened by the two clock bounds
because the tick to a clock value runs at a real time up to `ΔClockAhead` before or `ΔClockBehind`
after that value; the outcome is read from the tick's input, where the
update runs (rule R3).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, its facts; `s`: the slot;
  `v`: the validator; `C`: the confirmation.

Read aloud: a block `v` has saved as the confirmation of slot `s` right after its tick to the support
cutoff of slot `s + 1` is saved by the outcome of that tick, when `v` is active through the duty
window of slot `s + 1` widened by the two clock bounds. -/
theorem update_of_saved_confirmation (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ) (v : V) (C : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hw : v ∈ A.activeThroughout x ((M.dutyWindowStart S.C (s + 1) : ℝ) - ΔClockAhead)
      ((M.supportCutoff S.C (s + 1) : ℝ) + ΔClockBehind))
    (hSaved : (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C) :
    ∃ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) ∧
      AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1) ∧
      M.savedConfirmation n' s = some C :=
  (update_of_saved_confirmation_of_updater M F U) S A x R s v C E
    ((activeThroughoutToTick_of_dutyWindow M F U) R E hw) hSaved

/-- **Lemma 32, the saved confirmations of two honest validators are compatible.** In an
execution synchronous from the support cutoff of slot `s`, the blocks `C₁` and `C₂` that `v₁` and
`v₂` have saved as the confirmation of slot `s` on their states before `t₂ + 1`, `t₂` the support
cutoff of slot `s + 1`, are compatible, when each validator is awake and honest from the duty
window's start of slot `s + 1` to `t₂`.

Why: the wake window makes the tick at `t₂` run the confirmation update of slot `s + 1` (Lemma
15), whose saved confirmation the state before `t₂ + 1` keeps; the window contains Lemma 31's,
since the duty window of slot `s + 1` starts no later than slot `s`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot confirmed;
- `v₁`, `v₂`: the two validators; `C₁`, `C₂`: the blocks saved.

Read aloud: if two validators, each awake and honest from the duty window's start of slot `s + 1`
to its support cutoff, have `C₁` and `C₂` saved as their confirmation of slot `s` right after that
cutoff, then `C₁` and `C₂` are on one chain.

Roots name blocks until the later real time of `v₁`'s and `v₂`'s ticks to the support cutoff of slot
`s + 1`: Lemma 31, which the proof calls, compares the
frame trees on the states before the support cutoff of slot `s + 1`. -/
theorem lem32_saved_confirmations_compatible_state (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (v₁ v₂ : V) (C₁ C₂ : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- a root names one block among what honest validators hold, until the later real time of the two
    -- validators' ticks to the support cutoff of slot `s + 1`
    (hRoots : RootsNameBlocksUntil M A x (max (x.time (x.tickStep v₁ (M.supportCutoff S.C (s + 1))))
      (x.time (x.tickStep v₂ (M.supportCutoff S.C (s + 1))))))
    -- the network is synchronous from the support cutoff of slot `s` on
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s)
    -- `v₁` is awake and honest from the duty window's start of slot `s + 1` up to its tick to its
    -- support cutoff
    (hw₁ : v₁ ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    -- `v₂` likewise
    (hw₂ : v₂ ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    -- `v₁`'s state before `t₂ + 1` has `C₁` saved as the confirmation of slot `s`
    (hSaved₁ : (x.tickOutput v₁ (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C₁)
    -- `v₂`'s state before `t₂ + 1` has `C₂` saved as the confirmation of slot `s`
    (hSaved₂ : (x.tickOutput v₂ (M.supportCutoff S.C (s + 1))).savedConfirmation s =
      some C₂) :
    -- then `C₁` and `C₂` are compatible
    C₁.compatible C₂ = true := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hk2 := S.C.k_ge_two
  obtain ⟨hvt, hct, hft, hss, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s
  obtain ⟨hvt1, hct1, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s + 1)
  have hs0 : M.slotStart S.C s = 4 * Δ S * s := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk2R : (2 : ℝ) ≤ S.C.k := by exact_mod_cast hk2
  have hvfR : ((M.viewFreeze S.C s : ℕ) : ℝ) = 4 * Δ S * s + 3 * Δ S := by rw [hft, hs0]; push_cast; ring
  have hc1R : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = 4 * Δ S * s + 6 * Δ S := by
    rw [hct1, hss, hs0]; push_cast; ring
  have hm1le : max (Δ S) Δs ≤ M.viewFreeze S.C s := by omega
  -- the duty window of slot `s + 1` starts more than both clock bounds before
  -- `M.viewFreeze S.C s − max (3 * Δ S) Δs − ΔClockAhead` (`hΔs`, `hSkew`, `k ≥ 2`)
  have haB : ((duty_window_start S.C (s + 1) : ℤ) : ℝ) + ΔClockBehind <
      (M.viewFreeze S.C s : ℝ) - max (3 * Δ S) Δs - ΔClockAhead := by
    rw [duty_window_start_real S (s + 1), hvfR]
    have hkk : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by nlinarith
    push_cast
    rcases le_total (3 * Δ S) Δs with h | h
    · have hm1 : max ((Δ S : ℕ) : ℝ) (Δs : ℝ) = Δs := max_eq_right (by exact_mod_cast (by omega : Δ S ≤ Δs))
      have hm3 : max (3 * ((Δ S : ℕ) : ℝ)) (Δs : ℝ) = Δs := max_eq_right (by exact_mod_cast h)
      rw [hm1] at hΔs
      rw [hm3]
      linarith
    · have hm3 : max (3 * ((Δ S : ℕ) : ℝ)) (Δs : ℝ) = 3 * Δ S := max_eq_left (by exact_mod_cast h)
      rw [hm3]
      linarith
  -- each validator ticks to the support cutoff of slot `s + 1` and to the view freeze of slot `s`, active from
  -- one clock-ahead bound before `M.viewFreeze S.C s − max (3 * Δ S) Δs` up to the latter tick
  have hwin : ∀ u : V,
      u ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)) →
      ∃ (kc kF : ℕ), x.lbl kc = Event.tick u (M.supportCutoff S.C (s + 1)) ∧
        x.lbl kF = Event.tick u (M.viewFreeze S.C s) ∧
        ∀ i : ℕ, (M.viewFreeze S.C s : ℝ) - max (3 * Δ S) Δs - ΔClockAhead ≤ x.time i → i ≤ kF →
          u ∈ A.active i := by
    intro u hu
    obtain ⟨kc, hkc, hact⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hu haB
    have hkcT := (E.tick_active kc u _ hkc).2.1
    have hmx : (0 : ℝ) ≤ ((max (3 * Δ S) Δs : ℕ) : ℝ) := Nat.cast_nonneg _
    obtain ⟨kF, hkF, -, -⟩ := E.tick_of_active (M.viewFreeze S.C s) (by omega) u (fun i h1 h2 =>
      hact i (by linarith) ((lt_of_time_lt M) x R (by linarith)).le)
    exact ⟨kc, kF, hkc, hkF, fun i h1 h2 =>
      hact i h1 (le_trans h2 (tick_step_le_of_le M F E hkF hkc (by omega)))⟩
  -- each validator is active at every step whose real time is in the sync delay after the earliest re-send
  have hv₀ : ∀ u : V,
      u ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)) →
      u ∈ A.activeThroughout x ((M.viewFreeze S.C s) - (max (Δ S) Δs))
        (((M.viewFreeze S.C s) - (max (Δ S) Δs)) + Δs) := by
    intro u hu
    have h := (activeThroughout_of_dutyWindow_ofTick M F U) R E hΔs (s := s + 1) (b := M.viewFreeze S.C s)
      (e := M.supportCutoff S.C (s + 1)) hu (by omega) hm1le (by linarith)
    refine Activity.mem_activeThroughout.2 fun i h1 h2 => Activity.mem_activeThroughout.1 h i ?_ h2
    have : (Δs : ℝ) ≤ ((max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
    linarith
  -- each validator's update of slot `s + 1` saves its confirmation of slot `s`
  have hUpd : ∀ (u : V) (C : Block V),
      u ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)) →
      (x.tickOutput u (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C →
      ∃ n' : M.N, ConfirmationUpdated M S.C S.P (x.tickInput u (M.supportCutoff S.C (s + 1)))
          ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n' ∧ n'.savedConfirmation s = some C := by
    intro u C hu hC
    obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hu
    obtain ⟨n'', sent, hrun, hAw, hsave, -, -, -⟩ := (update_state_of_tick M F U) S A x R s u E hk'
      ((tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hu
        ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_lt_supportCutoff M.toSlotLayout
          F.sched U) S (s + 1)))
    have hCU := (confirmationUpdated_of_cutoff_tickInput M F U) x R s u n'' sent hrun hAw
    rw [hsave] at hC
    exact ⟨n'', hCU, hC⟩
  obtain ⟨k₁, kF₁, hk₁, hkF₁, hwin₁⟩ := hwin v₁ hw₁
  obtain ⟨k₂, kF₂, hk₂, hkF₂, hwin₂⟩ := hwin v₂ hw₂
  obtain ⟨n₁', hUpdate₁, hSaved₁'⟩ := hUpd v₁ C₁ hw₁ hSaved₁
  obtain ⟨n₂', hUpdate₂, hSaved₂'⟩ := hUpd v₂ C₂ hw₂ hSaved₂
  have hts₁ : x.tickStep v₁ (M.supportCutoff S.C (s + 1)) = k₁ := (tickStep_eq_of_lbl M) x E hk₁
  have hts₂ : x.tickStep v₂ (M.supportCutoff S.C (s + 1)) = k₂ := (tickStep_eq_of_lbl M) x E hk₂
  rw [hts₁, hts₂] at hRoots
  exact (lem31_saved_confirmations_compatible M F U) S A x R GST s v₁ v₂ n₁' n₂' C₁ C₂ E hNet hSkew hRedeliver Sy hGST
    kF₁ hkF₁ hwin₁ (hv₀ v₁ hw₁) kF₂ hkF₂ hwin₂ (hv₀ v₂ hw₂) k₁ hk₁ k₂ hk₂ hRoots
    hUpdate₁ hSaved₁' hUpdate₂ hSaved₂'

end GoldilocksCorrectness.Record.Proofs.Executions

