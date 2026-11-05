module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ConfirmationCompatibilityStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.LockProvenanceStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma33
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma34
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma42
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma45
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ACStore
public import GoldilocksCorrectness.Statements.Executions.ConfirmationCompatibilityStatements
public import GoldilocksCorrectness.Statements.Executions.LockProvenanceStatements
public import GoldilocksCorrectness.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma33
public import GoldilocksCorrectness.Proofs.Executions.Lemma34
public import GoldilocksCorrectness.Proofs.Executions.Lemma42
public import GoldilocksCorrectness.Proofs.Executions.Lemma45
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.Blocks
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma43, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma43.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: Lemma 43, two live locks made after `GST` are
compatible, and its case where one entry's deadline is at most the other's. The page's routine-level
theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff
  dutyWindowStart_succ_le_supportCutoff duty_window_start_mono one_le_Δ slotStart_cast
  slotStart_eq slotStart_mono slot_le_of_t_lt supportCutoff_cast supportCutoff_eq
  supportCutoff_lt_of_lt t_lt_of_lt viewFreeze_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_both
  compatible_of_compatible_ancestorEq compatible_symm')

open GoldilocksCorrectness.Proofs.Routines (duty_window_start_le_dutyWindowStart)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated LocksRevoked)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans compatible_iff
  compatible_of_ancestorEq_compatible)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## Times -/

/-! ## Blocks -/

variable {S : Setup V} {A : Activity V}

/-! ## The ordered case -/

/-- **The times of Lemma 43's fast case, over the natural numbers.** For slots `s₁ ≤ s' < s''`, with
`GST` at least `max (Δ S) Δs` before the support cutoff of slot `s₁`: the order of the times of slots
`s' + 1`, `s''` and `s'' + 1` that Lemma 42's windows at slot `s''` read.

Why: the slots are `4 * Δ S` long (`times_eq`), and slot `s''` starts no earlier than slot `s₁ + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `S`: the setup; `Δs`: the sync
  delay; `GST`: the time from which the network is synchronous; `s₁ ≤ s' < s''`: the slots.

Read aloud: in Lemma 43's fast case, the times Lemma 42 reads at slot `s''` come in their order, and
after `GST` by the recovery delay. -/
theorem fast_case_times_nat (U : UniformSchedule M.toSlotLayout) (S : Setup V) {Δs GST s₁ s' s'' : ℕ}
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₁) (hs₁w : s₁ ≤ s') (hlt : s' < s'') :
    M.viewFreeze S.C s'' + 3 * Δ S = M.supportCutoff S.C (s'' + 1) ∧
    M.voteTime S.C (s'' + 1) + Δ S = M.supportCutoff S.C (s'' + 1) ∧
    M.supportCutoff S.C (s' + 1) < M.voteTime S.C (s'' + 1) ∧
    M.viewFreeze S.C s'' ≤ M.voteTime S.C (s'' + 1) ∧
    1 ≤ M.viewFreeze S.C s'' ∧
    GST + max (Δ S) Δs ≤ M.viewFreeze S.C s'' ∧
    Δs ≤ max (Δ S) Δs ∧
    Δ S ≤ M.supportCutoff S.C (s'' + 1) := by
  obtain ⟨-, -, hft₂, hst₂, hΔ⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s''
  obtain ⟨hvt₃, hct₃, -, -, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s'' + 1)
  obtain ⟨-, hct₁, -, -, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s' + 1)
  obtain ⟨-, hcg, -, hsg, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s₁
  have hP₂ := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
    (show s' + 1 ≤ s'' by omega)
  have hP₃ := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
    (show s₁ + 1 ≤ s'' by omega)
  have hm1' := le_max_right (Δ S) Δs
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, hm1', by omega⟩

/-- **The duty window's start of slot `s'' + 1` against Lemma 42's opening for `v`.** For slots
`s₁ < s''`, with the sync bound `hΔs` over the natural numbers and `GST` at least `max (Δ S) Δs` before
the support cutoff of slot `s₁`, the duty window of slot `s'' + 1` starts at least one delay before
`M.supportCutoff S.C (s'' + 1) − max (6 * Δ S) Δs`.

Why: when it is positive it is `4 * Δ S * S.C.k − Δ S` before slot `s'' + 1`, and `max (6 * Δ S) Δs`
is at most `4 * Δ S * S.C.k`; when it is `0`, that cutoff is at least `8 * Δ S` after the support cutoff
of slot `s₁`, which is at least `Δs` (`hGST`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `S`: the setup; `Δs`: the sync
  delay; `GST`: the time from which the network is synchronous; `s₁ < s''`: the slots.

Read aloud: the duty window of slot `s'' + 1` opens more than one delay before the window Lemma 42
reads `v` from. -/
theorem fast_case_dws_cut (U : UniformSchedule M.toSlotLayout) (S : Setup V) {Δs GST s₁ s'' : ℕ}
    (h8 : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₁) (hs : s₁ < s'') :
    M.dutyWindowStart S.C (s'' + 1) + Δ S ≤ M.supportCutoff S.C (s'' + 1) - max (6 * Δ S) Δs := by
  have h9 := Nat.mul_le_mul_left (4 * Δ S) S.C.k_ge_two
  obtain ⟨-, -, -, hst₂, hΔ⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s''
  obtain ⟨-, hct₃, -, -, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s'' + 1)
  obtain ⟨-, hcg, -, hsg, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s₁
  have hP₃ := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
    (show s₁ + 1 ≤ s'' by omega)
  have hdc := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout
    F.sched U) S (s'' + 1)
  have hse := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)
    S (s'' + 1)
  have hm1' := le_max_right (Δ S) Δs
  have hmax6 : max (6 * Δ S) Δs = 6 * Δ S ∨ max (6 * Δ S) Δs = Δs := max_choice _ _
  generalize 4 * Δ S * S.C.k = K at *
  generalize 4 * Δ S * (s'' + 1) = Q at *
  rcases hmax6 with h | h <;> rw [h] <;> omega

/-- **The duty window's start of slot `s' + 1` against Lemma 42's opening for `w`.** For slots
`s₁ ≤ s' < s''`, with the sync bound `hΔs` over the natural numbers and `GST` at least `max (Δ S) Δs`
before the support cutoff of slot `s₁`, the duty window of slot `s' + 1` starts at least one delay
before `M.viewFreeze S.C s'' − max (3 * Δ S) Δs`.

Why: as `fast_case_dws_cut`, with the view freeze of slot `s''` at least `3 * Δ S` after the start of
slot `s' + 1` and at least `5 * Δ S` after the support cutoff of slot `s₁`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `S`: the setup; `Δs`: the sync
  delay; `GST`: the time from which the network is synchronous; `s₁ ≤ s' < s''`: the slots.

Read aloud: the duty window of slot `s' + 1` opens more than one delay before the window Lemma 42
reads `w` from. -/
theorem fast_case_dws_vf (U : UniformSchedule M.toSlotLayout) (S : Setup V) {Δs GST s₁ s' s'' : ℕ}
    (h8 : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₁) (hs₁w : s₁ ≤ s') (hlt : s' < s'') :
    M.dutyWindowStart S.C (s' + 1) + Δ S ≤ M.viewFreeze S.C s'' - max (3 * Δ S) Δs := by
  have h9 := Nat.mul_le_mul_left (4 * Δ S) S.C.k_ge_two
  obtain ⟨-, -, hft₂, -, hΔ⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s''
  obtain ⟨-, hcg, -, hsg, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s₁
  have hP₂ := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
    (show s' + 1 ≤ s'' by omega)
  have hP₃ := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
    (show s₁ + 1 ≤ s'' by omega)
  have hdc := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout
    F.sched U) S (s' + 1)
  have hse := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)
    S (s' + 1)
  have hm1' := le_max_right (Δ S) Δs
  have hmax3 : max (3 * Δ S) Δs = 3 * Δ S ∨ max (3 * Δ S) Δs = Δs := max_choice _ _
  generalize 4 * Δ S * S.C.k = K at *
  generalize 4 * Δ S * (s' + 1) = Q at *
  rcases hmax3 with h | h <;> rw [h] <;> omega

/-- **The duty windows' starts, integers, in Lemma 43's fast case.** For slots `s₁ ≤ s' < s''`, with
the sync bound `hΔs` over the natural numbers and `GST` at least `max (Δ S) Δs` before the support
cutoff of slot `s₁`: the spec's duty window starts of slots `s' + 1` and `s'' + 1` (integers, negative
for the early slots) at least one delay before the windows Lemma 42's holders and `w`'s ticks read.

Why: `duty_window_start S.C σ` is `4 * Δ S * S.C.k − Δ S` before the start of slot `σ`
(`duty_window_start_eq`, `slotStart_cast`), with `max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `S`: the setup; `Δs`: the sync
  delay; `GST`: the time from which the network is synchronous; `s₁ ≤ s' < s''`: the slots.

Read aloud: the two duty windows open more than one delay before what Lemma 43's fast case reads. -/
theorem fast_case_times_int (U : UniformSchedule M.toSlotLayout) (S : Setup V) {Δs GST s₁ s' s'' : ℕ}
    (h8 : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₁) (hs₁w : s₁ ≤ s') (hlt : s' < s'') :
    @LE.le Int _ (duty_window_start S.C (s'' + 1) + (Δ S : ℤ))
      ((M.viewFreeze S.C s'' - max (Δ S) Δs : ℕ) : ℤ) ∧
    @LE.le Int _ (duty_window_start S.C (s' + 1) + (Δ S : ℤ))
      ((M.supportCutoff S.C (s'' + 1) - max (Δ S) Δs : ℕ) : ℤ) ∧
    @LE.le Int _ (duty_window_start S.C (s' + 1) + (Δ S : ℤ)) ((M.viewFreeze S.C s'' : ℕ) : ℤ) ∧
    @LT.lt Int _ (duty_window_start S.C (s'' + 1)) ((M.voteTime S.C (s'' + 1) : ℕ) : ℤ) := by
  have h9 := Nat.mul_le_mul_left (4 * Δ S) S.C.k_ge_two
  obtain ⟨-, -, hft₂, hst₂, hΔ⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s''
  obtain ⟨hvt₃, hct₃, -, -, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s'' + 1)
  obtain ⟨-, hcg, -, hsg, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s₁
  have hP₂ := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
    (show s' + 1 ≤ s'' by omega)
  have hP₃ := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
    (show s₁ + 1 ≤ s'' by omega)
  have hm1' := le_max_right (Δ S) Δs
  have hm1 := le_max_left (Δ S) Δs
  have hD : ∀ σ : ℕ, @Eq Int (duty_window_start S.C σ + ((4 * Δ S * S.C.k : ℕ) : ℤ))
      (((M.slotStart S.C σ : ℕ) : ℤ) + (Δ S : ℤ)) := by
    intro σ
    rw [GoldilocksCorrectness.Proofs.Routines.duty_window_start_eq,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_cast M.toSlotLayout F.sched U) S σ,
      ← GoldilocksCorrectness.Proofs.Routines.Δ_cast S]
    push_cast
    ring
  have hD₁ := hD (s' + 1)
  have hD₃ := hD (s'' + 1)
  clear hD
  generalize 4 * Δ S * S.C.k = K at *
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- **The times of Lemma 43's fast case.** `fast_case_times_nat`, `fast_case_dws_cut`,
`fast_case_dws_vf` and `fast_case_times_int` together, for slots `s₁ ≤ s' < s''`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `S`: the setup; `Δs`: the sync
  delay; `GST`: the time from which the network is synchronous; `s₁ ≤ s' < s''`: the slots.

Read aloud: in Lemma 43's fast case, each window Lemma 42 reads at slot `s''` starts more than one delay
after the duty window it is read from, and the times come in their order. -/
theorem fast_case_times (U : UniformSchedule M.toSlotLayout) (S : Setup V) {Δs GST s₁ s' s'' : ℕ}
    (h8 : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₁) (hs₁w : s₁ ≤ s') (hlt : s' < s'') :
    M.dutyWindowStart S.C (s'' + 1) + Δ S ≤ M.supportCutoff S.C (s'' + 1) - max (6 * Δ S) Δs ∧
    M.dutyWindowStart S.C (s' + 1) + Δ S ≤ M.viewFreeze S.C s'' - max (3 * Δ S) Δs ∧
    @LE.le Int _ (duty_window_start S.C (s'' + 1) + (Δ S : ℤ))
      ((M.viewFreeze S.C s'' - max (Δ S) Δs : ℕ) : ℤ) ∧
    @LE.le Int _ (duty_window_start S.C (s' + 1) + (Δ S : ℤ))
      ((M.supportCutoff S.C (s'' + 1) - max (Δ S) Δs : ℕ) : ℤ) ∧
    @LE.le Int _ (duty_window_start S.C (s' + 1) + (Δ S : ℤ)) ((M.viewFreeze S.C s'' : ℕ) : ℤ) ∧
    @LT.lt Int _ (duty_window_start S.C (s'' + 1)) ((M.voteTime S.C (s'' + 1) : ℕ) : ℤ) ∧
    M.viewFreeze S.C s'' + 3 * Δ S = M.supportCutoff S.C (s'' + 1) ∧
    M.voteTime S.C (s'' + 1) + Δ S = M.supportCutoff S.C (s'' + 1) ∧
    M.supportCutoff S.C (s' + 1) < M.voteTime S.C (s'' + 1) ∧
    M.viewFreeze S.C s'' ≤ M.voteTime S.C (s'' + 1) ∧
    1 ≤ M.viewFreeze S.C s'' ∧
    GST + max (Δ S) Δs ≤ M.viewFreeze S.C s'' ∧
    Δs ≤ max (Δ S) Δs ∧
    Δ S ≤ M.supportCutoff S.C (s'' + 1) := by
  obtain ⟨T3, T4, T5, T6⟩ := (fast_case_times_int M F U) S h8 hGST hs₁w hlt
  obtain ⟨T7, T8, T9, T10, T11, T12, T15, T16⟩ := (fast_case_times_nat M F U) S hGST hs₁w hlt
  exact ⟨(fast_case_dws_cut M F U) S h8 hGST (by omega), (fast_case_dws_vf M F U) S h8 hGST hs₁w hlt,
    T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T15, T16⟩

/-- **The revocation a tick to a vote time ran.** When `w` ticks to the vote time of slot `σ` at the
step `kV`, from a node state awake for slot `σ`, the node state after that step is what the revocation
of the locks of slot `σ` leaves from the state the tick starts from (`LocksRevoked`).

Why: the step's outcome is an outcome of the tick from `w`'s state at `kV` (`R.tick`); the field
`tick_voteTime_locks_of_core` of `F.tk2` at the node invariant (Lemma 11's core), the spec's slot of the
vote time being `σ`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `σ`: the slot; `w`: the
  validator; `kV`: the step of its tick to the vote time.

Read aloud: a tick to a vote time, from a state awake for the slot, ran the revocation of that slot. -/
theorem locksRevoked_at_vote_tick (U : UniformSchedule M.toSlotLayout)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (σ : ℕ) (w : V) (kV : ℕ) (hkV : x.lbl kV = Event.tick w (M.voteTime S.C σ))
    (hAw : GoldilocksCorrectness.Record.Statements.Routines.AwakeFor M S.C
      (x.tickInput w (M.voteTime S.C σ)) σ) :
    LocksRevoked M S.P (x.tickInput w (M.voteTime S.C σ)) ((M.voteTime S.C σ : ℕ) : Int) σ
      (x.st (kV + 1) w) := by
  obtain ⟨n'', sent'', hok, hst, -⟩ := R.tick kV w _ hkV
  have hkVS : x.tickStep w (M.voteTime S.C σ) = kV := (tickStep_eq_of_lbl M) x E hkV
  have hin : x.tickInput w (M.voteTime S.C σ) = x.st kV w := by unfold Trace.tickInput; rw [hkVS]
  obtain ⟨hvt, -, -, hss, hΔ⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
  have hsl : S.C.slot ((M.voteTime S.C σ : ℕ) : Int) = σ := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S
      (by omega) (by omega)
  have hInv := (lem11_node_invariantCore_of_run M F S x R kV w).1
  rw [hin] at hAw ⊢
  have h := F.tk2.tick_voteTime_locks_of_core S.C S.P S.X _ _ n'' sent'' hok hInv
    (by rw [hsl]; exact (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout
      F.sched U) S σ)
    (by rw [hsl]; exact hAw)
  rw [hsl] at h
  rw [hst]
  exact h

/-- **Lemma 43's fast case.** When `v`'s update of slot `s'' + 1`, at its tick to the support cutoff
of that slot past the duty test, makes `L` a fast block, `w` has passed the duty test of slot `s' + 1`
at its tick to the support cutoff of that slot (`s' < s''`), is active after that tick up to its tick
to `c` (`hw`) and in the delay before the real time `c` (`hHoldW`), its finalized block at its tick to
`c` is `L` or an ancestor of `L`, and the block `B` is an ancestor-or-equal of a lock entry `w` holds
after every step from that update to its tick to `c`, then `L` is compatible with `B`.

Why: `w` ticks to the view freeze of slot `s''` and to the vote time of slot `s'' + 1` inside its window
(`mem_activeThroughoutToTick_of_inside`), the second from a state awake for slot `s'' + 1`; that tick ran
the revocation of slot `s'' + 1` (`locksRevoked_at_vote_tick`), whose every lock entry is compatible
with `L` (Lemma 42, its windows read off the two duty tests, `hw` and `hHoldW`, the times by
`fast_case_times`); the entry `B` descends to is one of them.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `GST`: the time from which
  the network is synchronous; `s₁`: a slot whose support cutoff is `max (Δ S) Δs` after `GST`; `s'`,
  `s''`: the slots of the two locks; `c`: the clock value of the read; `v`, `w`: the two validators;
  `kv`, `kw`: the steps of their ticks to `c`; `tStart`: the clock value `w`'s window opens at; `τv`,
  `τw`: the times since which the states the two updates start from are awake; `nv`: the state `v`'s
  update leaves; `L`: its fast block; `B`: the block.

Read aloud: a fast block of `v`'s update of slot `s'' + 1` is compatible with every block under a lock
`w` keeps from its earlier update of slot `s' + 1` up to its tick to `c`, when `w`'s finalized block
at that tick is that fast block or an ancestor of it. -/
theorem live_locks_fast_case (U : UniformSchedule M.toSlotLayout)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s₁ s' s'' c : ℕ) (v w : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (max (x.time (x.tickStep v c)) (x.time (x.tickStep w c))))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₁)
    (hs₁w : s₁ ≤ s') (hlt : s' < s'')
    (kv : ℕ) (hkv : x.lbl kv = Event.tick v c) (kw : ℕ) (hkw : x.lbl kw = Event.tick w c)
    (tStart : ℕ) (htS : tStart < M.supportCutoff S.C (s' + 1))
    (hw : w ∈ A.activeThroughoutToTick x (tStart : ℤ) c)
    (hHoldW : w ∈ A.activeThroughout x ((c - Δ S : ℕ) : ℝ) (c : ℝ))
    (hcv' : M.supportCutoff S.C (s'' + 1) < c)
    (hlv : x.lbl (x.tickStep v (M.supportCutoff S.C (s'' + 1))) =
      Event.tick v (M.supportCutoff S.C (s'' + 1)))
    {τv : Time} (hτv : (x.tickInput v (M.supportCutoff S.C (s'' + 1))).awakeSince = some τv)
    (hτvle : τv ≤ duty_window_start S.C (s'' + 1))
    (hlw' : x.lbl (x.tickStep w (M.supportCutoff S.C (s' + 1))) =
      Event.tick w (M.supportCutoff S.C (s' + 1)))
    {τw : Time} (hτw : (x.tickInput w (M.supportCutoff S.C (s' + 1))).awakeSince = some τw)
    (hτwle : τw ≤ duty_window_start S.C (s' + 1))
    {nv : M.N} (hU_v : GoldilocksCorrectness.Record.Statements.Routines.ConfirmationUpdated M S.C S.P
      (x.tickInput v (M.supportCutoff S.C (s'' + 1))) ((M.supportCutoff S.C (s'' + 1) : ℕ) : Int)
      (s'' + 1) nv)
    {L : Block V} (hFast : L ∈ M.fastBlocks nv)
    (hFL : (x.tickInput w c).finalized.AncestorEq L)
    {B : Block V}
    (htrack : ∀ i' : ℕ, x.tickStep w (M.supportCutoff S.C (s' + 1)) < i' → i' ≤ kw →
      ∃ e' ∈ (x.st i' w).lockEntries, B.AncestorEq e'.B) :
    L.compatible B = true := by
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have htime : Monotone x.time := fun _ _ h => (time_mono M) x R h
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hkvS : x.tickStep v c = kv := (tickStep_eq_of_lbl M) x E hkv
  have hkwS : x.tickStep w c = kw := (tickStep_eq_of_lbl M) x E hkw
  have hkvT := E.tick_active kv v c hkv
  have hkwT := E.tick_active kw w c hkw
  -- two ticks of one validator to `b < b'` are in that order (`clock_mono` at the later, `tick_unique`)
  have before : ∀ {u : V} {ku k b b' : ℕ}, x.lbl ku = Event.tick u b' → x.lbl k = Event.tick u b →
      b < b' → k < ku := by
    intro u ku k b b' hku hk hbb
    by_contra h
    rcases Nat.lt_or_ge ku k with hlt | hge
    · have := E.clock_mono ku k u b' b hlt (E.not_mem_corrupted_of_tick hk) (Or.inl hku) (Or.inl hk)
      omega
    · have hkk : k = ku := by omega
      rw [hkk, hku] at hk
      have := (Event.tick.inj hk).2
      omega
  -- the times
  have h8 : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have hR : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hR
  obtain ⟨T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T15, T16⟩ :=
    (fast_case_times M F U) S h8 hGST hs₁w hlt
  have hvc : M.voteTime S.C (s'' + 1) < c := by omega
  have hcw' : M.supportCutoff S.C (s' + 1) < c := by omega
  have hcw : x.tickStep w (M.supportCutoff S.C (s' + 1)) < kw := before hkw hlw' hcw'
  -- `w` is active from its tick to a value at most the duty window's start of slot `s' + 1` up
  -- to its tick to `c` (its update's duty test, then `hw`)
  have WW := (mem_activeThroughoutToTick_of_awakeSince_of_window M F) x R E hw hlw' htS hcw'.le
    hτw hτwle
  -- real-time bounds
  have hD₁R : ((duty_window_start S.C (s' + 1) : ℤ) : ℝ) + Δ S ≤ ((M.viewFreeze S.C s'' : ℕ) : ℝ) := by
    exact_mod_cast T5
  have hfvR : ((M.viewFreeze S.C s'' : ℕ) : ℝ) + Δ S ≤ (c : ℝ) := by
    exact_mod_cast (show M.viewFreeze S.C s'' + Δ S ≤ c by omega)
  have hvvR : ((M.voteTime S.C (s'' + 1) : ℕ) : ℝ) + Δ S ≤ (c : ℝ) := by
    exact_mod_cast (show M.voteTime S.C (s'' + 1) + Δ S ≤ c by omega)
  have hfvv : ((M.viewFreeze S.C s'' : ℕ) : ℝ) ≤ ((M.voteTime S.C (s'' + 1) : ℕ) : ℝ) := by
    exact_mod_cast T10
  -- `w` ticks to the view freeze of slot `s''` and to the vote time of slot `s'' + 1`, inside
  have WF := (mem_activeThroughoutToTick_of_inside M F) R E WW (c := M.viewFreeze S.C s'')
    T11 (by linarith) (by linarith)
  have WV := (mem_activeThroughoutToTick_of_inside M F) R E WW (c := M.voteTime S.C (s'' + 1))
    (le_trans T11 T10) (by linarith) (by linarith)
  obtain ⟨kV, hkV, -⟩ := Activity.mem_activeThroughoutToTick.1 WV
  -- the duty test of `w`'s revocation of slot `s'' + 1`
  have WV' := Activity.mem_activeThroughoutToTick_of_le
    (GoldilocksCorrectness.Proofs.Routines.duty_window_start_mono S (show s' + 1 ≤ s'' + 1 by omega)) WV
  obtain ⟨τD, hτD, hτDle⟩ := (tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E WV' T6
  -- the order of `w`'s ticks: to the cutoff of slot `s' + 1`, to the vote time, to `c`
  have hkVkw : kV < kw := before hkw hkV hvc
  have hkCkV : x.tickStep w (M.supportCutoff S.C (s' + 1)) < kV := before hkV hlw' T9
  -- the lock entry `B` descends to, after `w`'s tick to the vote time of slot `s'' + 1`
  obtain ⟨e'w, he'w, hB'w⟩ := htrack (kV + 1) (by omega) (by omega)
  -- that tick ran the revocation of slot `s'' + 1`
  have hLR := (locksRevoked_at_vote_tick M F U) x R E (s'' + 1) w kV hkV ⟨τD, hτD, hτDle⟩
  -- `w`'s finalized block at that tick is an ancestor of its finalized block at its tick to `c`
  have hF : (x.tickInput w (M.voteTime S.C (s'' + 1))).finalized.compatible L = true := by
    have hin : x.tickInput w (M.voteTime S.C (s'' + 1)) = x.st kV w := by
      unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hkV]
    have hc : x.tickInput w c = x.st kw w := by unfold Trace.tickInput; rw [hkwS]
    have hmono := (F_ancestorEq_of_le M F) x R E w (le_of_lt hkVkw)
    rw [← hin, ← hc] at hmono
    exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hmono hFL))
  -- Lemma 42's windows
  have htStartV : ((M.dutyWindowStart S.C (s'' + 1) : ℕ) : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s'' + 1) - max (6 * Δ S) Δs : ℕ) : ℝ) := by
    have hR : ((M.dutyWindowStart S.C (s'' + 1) + Δ S : ℕ) : ℝ) ≤
        ((M.supportCutoff S.C (s'' + 1) - max (6 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast T1
    rw [Nat.cast_add] at hR
    linarith
  have htStartW : ((M.dutyWindowStart S.C (s' + 1) : ℕ) : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.viewFreeze S.C s'' - max (3 * Δ S) Δs : ℕ) : ℝ) := by
    have hR : ((M.dutyWindowStart S.C (s' + 1) + Δ S : ℕ) : ℝ) ≤
        ((M.viewFreeze S.C s'' - max (3 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast T2
    rw [Nat.cast_add] at hR
    linarith
  have hVv := (mem_activeThroughoutToTick_of_awakeSince_steps M F) x R E hlv hτv hτvle hlv le_rfl
    (fun j h1 h2 => absurd h2 (by omega))
  have hVv' := Activity.mem_activeThroughoutToTick_of_le
    ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_le_dutyWindowStart
      M.toSlotLayout F.sched U) S (s'' + 1)) hVv
  have WF' := Activity.mem_activeThroughoutToTick_of_le
    ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_le_dutyWindowStart
      M.toSlotLayout F.sched U) S (s' + 1)) WF
  have hv₀ : v ∈ A.activeThroughout x ((M.viewFreeze S.C s'' - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s'' - max (Δ S) Δs : ℕ) : ℝ) + Δs) := by
    have hT3 : ((duty_window_start S.C (s'' + 1) : ℤ) : ℝ) + Δ S ≤
        ((M.viewFreeze S.C s'' - max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast T3
    have hN : M.viewFreeze S.C s'' - max (Δ S) Δs + Δs + Δ S ≤ M.supportCutoff S.C (s'' + 1) := by
      omega
    have hR : ((M.viewFreeze S.C s'' - max (Δ S) Δs + Δs + Δ S : ℕ) : ℝ) ≤
        ((M.supportCutoff S.C (s'' + 1) : ℕ) : ℝ) := by exact_mod_cast hN
    rw [Nat.cast_add (M.viewFreeze S.C s'' - max (Δ S) Δs + Δs) (Δ S)] at hR
    have hw' := (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E hVv
      (a' := M.viewFreeze S.C s'' - max (Δ S) Δs) (e := M.viewFreeze S.C s'' - max (Δ S) Δs + Δs)
      (by linarith) (by linarith)
    rw [Nat.cast_add] at hw'
    exact hw'
  have hw₀ : w ∈ A.activeThroughout x ((M.supportCutoff S.C (s'' + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s'' + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) := by
    obtain ⟨k', hk', hcase⟩ := Activity.mem_activeThroughoutToTick.1 WW
    have hk'kw : k' = kw := E.tick_unique k' kw w c hk' hkw
    subst hk'kw
    have hendR : ((M.supportCutoff S.C (s'' + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs ≤ (c : ℝ) := by
      have hR : ((M.supportCutoff S.C (s'' + 1) - max (Δ S) Δs + Δs : ℕ) : ℝ) ≤ (c : ℝ) := by
        exact_mod_cast (show M.supportCutoff S.C (s'' + 1) - max (Δ S) Δs + Δs ≤ c by omega)
      rw [Nat.cast_add] at hR
      exact hR
    have hT4 : ((duty_window_start S.C (s' + 1) : ℤ) : ℝ) + Δ S ≤
        ((M.supportCutoff S.C (s'' + 1) - max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast T4
    have hcΔ : (((c - Δ S : ℕ) : ℝ)) = (c : ℝ) - Δ S := by
      rw [Nat.cast_sub (show Δ S ≤ c by omega)]
    refine Activity.mem_activeThroughout_of_forall fun i h1 h2 => ?_
    rcases Nat.lt_or_ge k' i with hgt | hle''
    · -- after `w`'s tick to `c`: `hHoldW`
      refine Activity.mem_activeThroughout.1 hHoldW i (by linarith) ?_
      have := htime (show k' ≤ i + 1 by omega)
      rw [hcΔ]
      linarith [hkwT.2.1]
    · rcases hcase with h | ⟨k₀, -, c₀, hc₀, hk₀, h⟩
      · exact h i hle''
      · refine h i ?_ hle''
        by_contra hlt'
        have hk₀a := (E.tick_active k₀ w c₀ hk₀).2.2
        have := htime (show i + 1 ≤ k₀ by omega)
        have hc₀R : ((c₀ : ℤ) : ℝ) ≤ ((duty_window_start S.C (s' + 1) : ℤ) : ℝ) := by
          exact_mod_cast hc₀
        push_cast at hc₀R
        linarith
  -- roots up to `ΔClockBehind` after the view freeze of slot `s''`, before `v`'s tick to `c`
  have hR42 : RootsNameBlocksUntil M A x ((M.viewFreeze S.C s'' : ℝ) + ΔClockBehind) := by
    refine (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) ?_ hRoots
    rw [hkvS, hkwS]
    have := hkvT.2.1
    exact le_trans (by linarith) (le_max_left _ _)
  have h42 := (lem42_fast_lock_clears_conflicting_locks M F U) S A x R GST s'' L v w nv E
    hNet hSkew hRedeliver Sy hΔs hR42 hParent T12 (M.dutyWindowStart S.C (s'' + 1)) htStartV
    hVv' (M.dutyWindowStart S.C (s' + 1)) htStartW WF' hv₀ hw₀ hU_v hFast kV hkV hF
  have hc42 := h42 (x.st (kV + 1) w) hLR e'w he'w
  exact compatible_of_compatible_ancestorEq (compatible_symm' hc42) hB'w

/-- Lemma 43 when `e_w`'s deadline is at most `e_v`'s: the two live lock entries are on compatible
blocks. The hypotheses are those of `lem43_live_locks_after_GST_compatible`, with `v`'s window
replaced by `v`'s tick to `c` (the only part of it the case reads), without `v`'s window after its
tick (`hHoldV`) and without the finalized-block condition at `v` (`hFvw`), which this case does not read.

Every state is read at its validator's own tick to the clock value `c`. Lemma 39
gives the slot `s''` of `e_v` and the slot `s'` of `e_w`, `s' ≤ s''` by the deadlines, with the two
validators' updates at their ticks to the support cutoffs of slots `s'' + 1` and `s' + 1`, both
before their ticks to `c` and past the duty test. Lemma 31's windows at slot `s'` are read off those
duty tests (`lem31_windows_of_duty_test`). When `s' < s''` and `e_v`'s block is fast in `v`'s update,
`w`'s revocation at its tick to the vote time of slot `s'' + 1` (Lemma 42, its windows from the duty
tests and from `hw` after `w`'s tick to the support cutoff of slot `s' + 1`, and from `hHoldW` after
`w`'s tick to `c`) leaves `e_w` traced (Lemma 39) to an entry compatible with `e_v`'s; when it is slow,
`v`'s confirmation of slot `s'` extends it (Lemmas 37, 40) and Lemma 31 applies.

The variables: those of `lem43_live_locks_after_GST_compatible`, and `kv`: the step of `v`'s tick to `c`.

Read aloud: two lock entries held by `v` and `w` at their own ticks to the clock value `c`, `e_w`
live at `c` by `w`'s clock, `e_w`'s deadline at most `e_v`'s, are on compatible blocks, when `w`'s
finalized block at that tick is compatible with `e_v`'s block. -/
theorem live_locks_compatible_of_deadline_le (U : UniformSchedule M.toSlotLayout)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s₁ s c : ℕ) (v w : V) (e_v e_w : M.LE)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (max (x.time (x.tickStep v c)) (x.time (x.tickStep w c))))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₁)
    (hsc : M.slotStart S.C s ≤ c)
    (kv : ℕ) (hkv : x.lbl kv = Event.tick v c)
    (tStart : ℕ) (htStart : tStart < M.supportCutoff S.C (s - S.C.k))
    (hw : w ∈ A.activeThroughoutToTick x (tStart : ℤ) c)
    (hHoldW : w ∈ A.activeThroughout x ((c - Δ S : ℕ) : ℝ) (c : ℝ))
    (he_v : e_v ∈ (x.tickInput v c).lockEntries)
    (hd_v : S.C.t_ (s₁ + S.C.k) + 5 * S.C.Δ ≤ e_v.d)
    (he_w : e_w ∈ (x.tickInput w c).lockEntries)
    (hlive_w : M.is_live (x.tickInput w c) (c : Int) e_w = true)
    (hd_w : S.C.t_ (s₁ + S.C.k) + 5 * S.C.Δ ≤ e_w.d)
    (hFwv : (x.tickInput w c).finalized.compatible e_v.B = true)
    (hle : e_w.d ≤ e_v.d) :
    e_v.B.compatible e_w.B = true := by
  have hΔ := one_le_Δ S
  have hΔi : (0 : Int) < S.C.Δ := S.C.Δ_pos
  have hk2 := S.C.k_ge_two
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have htime : Monotone x.time := fun _ _ h => (time_mono M) x R h
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  -- the two ticks to `c`
  obtain ⟨kw, hkw, -⟩ := Activity.mem_activeThroughoutToTick.1 hw
  have hkvS : x.tickStep v c = kv := (tickStep_eq_of_lbl M) x E hkv
  have hkwS : x.tickStep w c = kw := (tickStep_eq_of_lbl M) x E hkw
  have hkvT := E.tick_active kv v c hkv
  have hkwT := E.tick_active kw w c hkw
  -- two ticks of one validator to `b < b'` are in that order (`clock_mono` at the later, `tick_unique`)
  have before : ∀ {u : V} {ku k b b' : ℕ}, x.lbl ku = Event.tick u b' → x.lbl k = Event.tick u b →
      b < b' → k < ku := by
    intro u ku k b b' hku hk hbb
    by_contra h
    rcases Nat.lt_or_ge ku k with hlt | hge
    · have := E.clock_mono ku k u b' b hlt (E.not_mem_corrupted_of_tick hk) (Or.inl hku) (Or.inl hk)
      omega
    · have hkk : k = ku := by omega
      rw [hkk, hku] at hk
      have := (Event.tick.inj hk).2
      omega
  -- and a tick of `u` before its tick to `b'` is to a value less than `b'`
  have after_lt : ∀ {u : V} {ku k b b' : ℕ}, x.lbl ku = Event.tick u b' → x.lbl k = Event.tick u b →
      k < ku → b < b' := by
    intro u ku k b b' hku hk hlt
    have hbc := E.clock_mono k ku u b b' hlt (E.not_mem_corrupted_of_tick hku) (Or.inl hk) (Or.inl hku)
    rcases Nat.lt_or_ge b b' with h | h
    · exact h
    · have hbb : b = b' := le_antisymm hbc h
      rw [hbb] at hk
      exact absurd (E.tick_unique k ku u b' hk hku) (by omega)
  -- the liveness of `e_w`
  have hlw : (c : Int) < e_w.d ∧ e_w.B ∈ (M.fg_to_ac (x.tickInput w c)).tree :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F) _ _ _).1 hlive_w
  -- Lemma 39 on both entries
  obtain ⟨s'', hdv, hcv, hlv, ⟨τv, hτv, hτvle⟩, h39v⟩ :=
    (lem39_lock_entry_provenance M F U) S A x R (x.tickStep v c) v e_v E he_v
  obtain ⟨s', hdw, hcw, hlw', ⟨τw, hτw, hτwle⟩, h39w⟩ :=
    (lem39_lock_entry_provenance M F U) S A x R (x.tickStep w c) w e_w E he_w
  rw [hkvS] at hcv
  rw [hkwS] at hcw
  -- both cutoffs are before `c` by the validators' clocks
  have hcv' : M.supportCutoff S.C (s'' + 1) < c := after_lt hkv hlv hcv
  have hcw' : M.supportCutoff S.C (s' + 1) < c := after_lt hkw hlw' hcw
  -- the deadlines and the liveness at `Int`, where `omega` reads them
  have hdv' : @Eq Int e_v.d (S.C.t_ (s'' + S.C.k) + 5 * S.C.Δ) := hdv
  have hdw' : @Eq Int e_w.d (S.C.t_ (s' + S.C.k) + 5 * S.C.Δ) := hdw
  have hle' : @LE.le Int _ e_w.d e_v.d := hle
  have hd_v' : @LE.le Int _ (S.C.t_ (s₁ + S.C.k) + 5 * S.C.Δ) e_v.d := hd_v
  have hd_w' : @LE.le Int _ (S.C.t_ (s₁ + S.C.k) + 5 * S.C.Δ) e_w.d := hd_w
  have hlw1 : @LT.lt Int _ (c : Int) e_w.d := hlw.1
  -- the slots
  have hbwv : s' ≤ s'' := by
    have h := slot_le_of_t_lt S (s := s' + S.C.k) (s' := s'' + S.C.k) (n := 0)
      (r := 4 * S.C.Δ) (by omega) (by omega)
    omega
  have hs₁v : s₁ ≤ s'' := by
    have h := slot_le_of_t_lt S (s := s₁ + S.C.k) (s' := s'' + S.C.k) (n := 0)
      (r := 4 * S.C.Δ) (by omega) (by omega)
    omega
  have hs₁w : s₁ ≤ s' := by
    have h := slot_le_of_t_lt S (s := s₁ + S.C.k) (s' := s' + S.C.k) (n := 0)
      (r := 4 * S.C.Δ) (by omega) (by omega)
    omega
  -- `s ≤ s' + k + 1`: `e_w` is live at `c ≥ slotStart S s`
  have hsw : s ≤ s' + S.C.k + 1 := by
    have h1 : @LE.le Int _ (S.C.t_ s) (c : Int) := by
      rw [← (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_cast M.toSlotLayout F.sched U)]
      exact_mod_cast hsc
    exact slot_le_of_t_lt S (s := s) (s' := s' + S.C.k) (n := 1) (r := 5 * S.C.Δ)
      (by omega) (by omega)
  -- `s'' + 1 ≤ s' + k`: `e_w` is live at `c`, after the support cutoff of slot `s'' + 1`
  have hvw : s'' + 1 ≤ s' + S.C.k := by
    have h1 : @LT.lt Int _ (S.C.t_ (s'' + 1) + 2 * S.C.Δ) (c : Int) := by
      rw [← (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U)]
      exact_mod_cast hcv'
    exact slot_le_of_t_lt S (s := s'' + 1) (s' := s' + S.C.k) (n := 0) (r := 3 * S.C.Δ)
      (by omega) (by omega)
  -- the slot times
  obtain ⟨hvt₀, hct₀, hft₀, hst₀, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s'
  obtain ⟨hvt₁, hct₁, hft₁, hst₁, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s' + 1)
  obtain ⟨-, hcg, -, hsg, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s₁
  have hP₁ := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hs₁w
  have hGSTw : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s' := by omega
  have hcb : Δs ≤ M.viewFreeze S.C s' := by
    have := le_max_right (Δ S) Δs
    omega
  -- the updates of slots `s'' + 1` (at `v`) and `s' + 1` (at `w`), at their ticks to the cutoffs
  obtain ⟨nv, sentv, hrunv, hAwv, -⟩ :=
    (update_state_of_tick M F U) S A x R s'' v E hlv ⟨τv, hτv, hτvle⟩
  have hU_v := (confirmationUpdated_of_cutoff_tickInput M F U) x R s'' v nv sentv hrunv hAwv
  obtain ⟨e₀v, -, -, -, -, ⟨C₀v, hC₀v, hB₀v⟩, hFS_v, hBv₀, -⟩ := h39v nv sentv hrunv hAwv
  obtain ⟨nw, sentw, hrunw, hAww, -⟩ :=
    (update_state_of_tick M F U) S A x R s' w E hlw' ⟨τw, hτw, hτwle⟩
  have hU_w := (confirmationUpdated_of_cutoff_tickInput M F U) x R s' w nw sentw hrunw hAww
  obtain ⟨e₀w, -, -, -, -, ⟨C₀w, hC₀w, hB₀w⟩, -, hBw₀, htrack_w⟩ := h39w nw sentw hrunw hAww
  have hBw : e_w.B.AncestorEq C₀w := ancestorEq_trans hBw₀ hB₀w
  -- Lemma 31's windows of `w` at slot `s'`, from the duty test of its update
  obtain ⟨kF₂, hkF₂, -, hwin₂, hv₂₀⟩ :=
    (lem31_windows_of_duty_test M F U) x R E hSkew hΔs hcb hlw' hτw hτwle
  -- the comparison through slot `s'`, given `v`'s update of slot `s' + 1` saving `C₁`
  have key : ∀ (k₁ : ℕ) (n₁ : M.N) (C₁ : Block V) (τ₁ : Time),
      x.lbl k₁ = Event.tick v (M.supportCutoff S.C (s' + 1)) → k₁ ≤ kv →
      (x.tickInput v (M.supportCutoff S.C (s' + 1))).awakeSince = some τ₁ →
      τ₁ ≤ duty_window_start S.C (s' + 1) →
      GoldilocksCorrectness.Record.Statements.Routines.ConfirmationUpdated M S.C S.P
        (x.tickInput v (M.supportCutoff S.C (s' + 1))) ((M.supportCutoff S.C (s' + 1) : ℕ) : Int)
        (s' + 1) n₁ →
      n₁.savedConfirmation s' = some C₁ →
      e_v.B.AncestorEq C₁ → e_v.B.compatible e_w.B = true := by
    intro k₁ n₁ C₁ τ₁ hk₁ hk₁v hτ₁ hτ₁le hU₁ hS₁ hB₁
    obtain ⟨kF₁, hkF₁, -, hwin₁, hv₁₀⟩ :=
      (lem31_windows_of_duty_test M F U) x R E hSkew hΔs hcb hk₁ hτ₁ hτ₁le
    have hR31 : RootsNameBlocksUntil M A x
        (max (x.time k₁) (x.time (x.tickStep w (M.supportCutoff S.C (s' + 1))))) := by
      refine (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) ?_ hRoots
      rw [hkvS, hkwS]
      exact max_le_max (htime hk₁v) (htime hcw.le)
    have hcomp := (lem31_saved_confirmations_compatible M F U) S A x R GST s' v w n₁ nw C₁ C₀w E
      hNet hSkew hRedeliver Sy hGSTw kF₁ hkF₁ hwin₁ hv₁₀ kF₂ hkF₂ hwin₂ hv₂₀ k₁ hk₁ _ hlw' hR31
      hU₁ hS₁ hU_w hC₀w
    exact compatible_of_ancestorEq_both hB₁ hBw hcomp
  rcases Nat.lt_or_ge s' s'' with hlt | hge
  · rcases hFS_v with hFast | hSlow
    · rcases (compatible_iff _ _).1 hFwv with hFe | heF
      · -- the fast case: through `w`'s revocation of slot `s'' + 1` (`live_locks_fast_case`)
        have htS : tStart < M.supportCutoff S.C (s' + 1) :=
          lt_of_lt_of_le htStart
            ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
              (show s - S.C.k ≤ s' + 1 by omega))
        have hLB := (live_locks_fast_case M F U) x R GST s₁ s' s'' c v w E hNet hSkew hRedeliver Sy
          hΔs hRoots hParent hGST hs₁w hlt kv hkv kw hkw tStart htS hw hHoldW hcv' hlv hτv hτvle hlw'
          hτw hτwle hU_v hFast (ancestorEq_trans hFe hBv₀)
          (fun i' h1 h2 => by
            obtain ⟨e', he', -, hB, -⟩ := htrack_w i' h1 (by rw [hkwS]; exact h2)
            exact ⟨e', he', hB⟩)
        exact compatible_symm' (compatible_of_compatible_ancestorEq (compatible_symm' hLB) hBv₀)
      · -- `e_v`'s block is an ancestor-or-equal of `w`'s finalized block, hence of `e_w`'s
        have hFe_w := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1
          hlw.2).2
        exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans heF hFe_w))
    · -- the slow case: `e₀v`'s block is `v`'s saved confirmation of slot `s'` or an ancestor of it
      obtain ⟨-, hj⟩ :=
        (GoldilocksCorrectness.Record.Statements.Routines.lem37_slow_test_saved_confirmations F) S.C _ s''
          e₀v.B hSlow
      obtain ⟨Cj, hCj, -, hBj⟩ := hj s' (show s'' + 1 - S.C.k ≤ s' by omega) hlt
      obtain ⟨hlt40, hl40, ⟨τ₁, hτ₁, hτ₁le⟩, hS40, -⟩ :=
        (lem40_saved_confirmation_provenance M F U) S A x R
          (x.tickStep v (M.supportCutoff S.C (s'' + 1))) v s' Cj E hCj
      obtain ⟨n₁, sent₁, hrun₁, hAw₁, -⟩ :=
        (update_state_of_tick M F U) S A x R s' v E hl40 ⟨τ₁, hτ₁, hτ₁le⟩
      have hU₁ := (confirmationUpdated_of_cutoff_tickInput M F U) x R s' v n₁ sent₁ hrun₁ hAw₁
      exact key _ n₁ Cj τ₁ hl40 (by omega) hτ₁ hτ₁le hU₁ (hS40 n₁ sent₁ hrun₁ hAw₁)
        (ancestorEq_trans hBv₀ hBj)
  · -- the same slot
    have hbb : s' = s'' := le_antisymm hbwv hge
    subst hbb
    exact key _ nv C₀v τv hlv hcv.le hτv hτvle hU_v hC₀v (ancestorEq_trans hBv₀ hB₀v)

/-- **Lemma 43, two live locks made after `GST` are compatible.** The proof; the audited
statement is in `Statements/Executions/HealingStatements.lean`.

Every state is read at its validator's own tick to the clock value `c`;
`live_locks_compatible_of_deadline_le`, applied in the order of the two deadlines, is the proof.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: at the clock value `c` of a slot `s` that has started, two lock entries held by `v` and
`w` at their own ticks to `c`, live at `c` by their clocks, the two validators active from their
ticks to a clock value at most `tStart` (before the support cutoff of slot `s − S.C.k`) up to their
ticks to `c` and in the delay before the real time `c`, each the lock of a slot at least `s₁`, are on
compatible blocks, when `GST` is at most the vote time of slot `s₁` and each validator's finalized
block at its tick to `c` is compatible with the other's lock block. -/
theorem lem43_live_locks_after_GST_compatible (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s₁ s c : ℕ) (v w : V) (e_v e_w : M.LE)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (max (x.time (x.tickStep v c)) (x.time (x.tickStep w c))))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₁)
    (hsc : M.slotStart S.C s ≤ c)
    (tStart : ℕ) (htStart : tStart < M.supportCutoff S.C (s - S.C.k))
    (hv : v ∈ A.activeThroughoutToTick x (tStart : ℤ) c)
    (hw : w ∈ A.activeThroughoutToTick x (tStart : ℤ) c)
    (hHoldV : v ∈ A.activeThroughout x ((c - Δ S : ℕ) : ℝ) (c : ℝ))
    (hHoldW : w ∈ A.activeThroughout x ((c - Δ S : ℕ) : ℝ) (c : ℝ))
    (he_v : e_v ∈ (x.tickInput v c).lockEntries)
    (hlive_v : M.is_live (x.tickInput v c) (c : Int) e_v = true)
    (hd_v : S.C.t_ (s₁ + S.C.k) + 5 * S.C.Δ ≤ e_v.d)
    (he_w : e_w ∈ (x.tickInput w c).lockEntries)
    (hlive_w : M.is_live (x.tickInput w c) (c : Int) e_w = true)
    (hd_w : S.C.t_ (s₁ + S.C.k) + 5 * S.C.Δ ≤ e_w.d)
    (hFwv : (x.tickInput w c).finalized.compatible e_v.B = true)
    (hFvw : (x.tickInput v c).finalized.compatible e_w.B = true) :
    e_v.B.compatible e_w.B = true := by
  obtain ⟨kv, hkv, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  obtain ⟨kw, hkw, -⟩ := Activity.mem_activeThroughoutToTick.1 hw
  rcases le_total e_w.d e_v.d with hle | hle
  · exact (live_locks_compatible_of_deadline_le M F U) x R GST s₁ s c v w e_v e_w E hNet hSkew
      hRedeliver Sy hΔs hRoots hParent hGST hsc kv hkv tStart htStart hw hHoldW he_v hd_v he_w
      hlive_w hd_w hFwv hle
  · exact compatible_symm' ((live_locks_compatible_of_deadline_le M F U) x R GST s₁ s c w v e_w e_v E
      hNet hSkew hRedeliver Sy hΔs (by rwa [max_comm]) hParent hGST hsc kw hkw tStart htStart hv
      hHoldV he_w hd_w he_v hlive_v hd_v hFvw hle)

end GoldilocksCorrectness.Record.Proofs.Executions
