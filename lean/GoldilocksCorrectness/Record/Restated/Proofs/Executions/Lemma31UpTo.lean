module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma31
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Proofs.Executions.Lemma31
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma31UpTo, over a model

The theorem of `GoldilocksCorrectness/Proofs/Executions/Lemma31UpTo.lean` over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 31, two honest confirmation updates
of a slot save compatible blocks, with the delivery premises up to a bound. The page's routine-level
theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq supportCutoff_cast
  supportCutoff_eq viewFreeze_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (expireLocks_keepsVotes tau_of_keepsVotes)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (ConfirmationUpdated)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Lemma 31, two honest confirmation updates of a slot save compatible blocks.** In an
execution synchronous from the support cutoff of slot `s`, the confirmation updates of slot
`s + 1`, for the slot `s`, from the node states of `v₁` and `v₂` at their ticks to the support cutoff of
slot `s + 1`, that save `C₁` and `C₂` as the confirmation of slot `s`, save compatible blocks, when
each validator is awake and honest from the support cutoff of slot `s` to its view freeze and honest
at the support cutoff of slot `s + 1`.

Why: Lemma 30. A vote resolving early at one validator was held there before the support cutoff
of slot `s`, was re-sent then, and reaches the other within one delay, while it is awake; every
pool vote before the update is stamped before it; the two frame trees hold only blocks of honest
validators, where a root names one block.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot confirmed;
- `v₁`, `v₂`: the two validators; `n₁'`, `n₂'`: the node states the two updates leave;
- `C₁`, `C₂`: the blocks saved.

Read aloud: in a synchronous execution from the support cutoff of slot `s`, if two validators,
each awake and honest from that cutoff for one delay and ticking to the cutoff where the update for slot `s` runs,
have that update save `C₁` and `C₂`, then `C₁` and `C₂` are on one chain.

Roots name blocks until the later real time of the two ticks to the support cutoff of slot `s + 1`: the
proof compares the blocks of the two
frame trees on `v₁`'s and `v₂`'s states before the support cutoff of slot `s + 1`.

Restated with the delivery premises up to `M.supportCutoff S.C s + Δ S`: Lemma 62, in each
direction, reads the re-sends at the support cutoff of slot `s`, due one delay after it. -/
theorem lem31_saved_confirmations_compatible_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (v₁ v₂ : V) (n₁' n₂' : M.N)
    (C₁ C₂ : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s + Δ S)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s + Δ S))
    -- the network is synchronous from the support cutoff of slot `s` on
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s)
    -- `v₁` ticks to the view freeze of slot `s` at `kF₁`, and is active at every step up to that tick
    -- whose real time is at least `ΔClockAhead` before `M.viewFreeze S.C s − max (3 * Δ S) Δs`, and at every
    -- step whose real time is in the sync delay after the earliest re-send
    (kF₁ : ℕ) (hkF₁ : x.lbl kF₁ = Event.tick v₁ (M.viewFreeze S.C s))
    (hwin₁ : ∀ i : ℕ, (M.viewFreeze S.C s : ℝ) - max (3 * Δ S) Δs - ΔClockAhead ≤ x.time i → i ≤ kF₁ →
      v₁ ∈ A.active i)
    (hv₁₀ : v₁ ∈ A.activeThroughout x ((M.viewFreeze S.C s) - (max (Δ S) Δs)) (((M.viewFreeze S.C s) - (max (Δ S) Δs)) + Δs))
    -- `v₂` ticks to the view freeze of slot `s` at `kF₂`, and is active at every step up to that tick
    -- whose real time is at least `ΔClockAhead` before `M.viewFreeze S.C s − max (3 * Δ S) Δs`, and at every
    -- step whose real time is in the sync delay after the earliest re-send
    (kF₂ : ℕ) (hkF₂ : x.lbl kF₂ = Event.tick v₂ (M.viewFreeze S.C s))
    (hwin₂ : ∀ i : ℕ, (M.viewFreeze S.C s : ℝ) - max (3 * Δ S) Δs - ΔClockAhead ≤ x.time i → i ≤ kF₂ →
      v₂ ∈ A.active i)
    (hv₂₀ : v₂ ∈ A.activeThroughout x ((M.viewFreeze S.C s) - (max (Δ S) Δs)) (((M.viewFreeze S.C s) - (max (Δ S) Δs)) + Δs))
    -- `v₁` and `v₂` tick to the support cutoff of slot `s + 1` at `k₁`, `k₂`, where their updates run
    -- (the read point, T-RC10-1,)
    (k₁ : ℕ) (hk₁ : x.lbl k₁ = Event.tick v₁ (M.supportCutoff S.C (s + 1)))
    (k₂ : ℕ) (hk₂ : x.lbl k₂ = Event.tick v₂ (M.supportCutoff S.C (s + 1)))
    -- a root names one block among what honest validators hold, until the later real time of the two
    -- ticks to the support cutoff of slot `s + 1`
    (hRoots : RootsNameBlocksUntil M A x (max (x.time k₁) (x.time k₂)))
    -- the confirmation update of slot `s + 1` at `v₁`'s tick to the support cutoff of slot `s + 1` leaves `n₁'`,
    -- which saves `C₁` as the confirmation of slot `s`
    (hUpdate₁ : ConfirmationUpdated M S.C S.P (x.tickInput v₁ (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n₁')
    (hSaved₁ : n₁'.savedConfirmation s = some C₁)
    -- likewise at `v₂`
    (hUpdate₂ : ConfirmationUpdated M S.C S.P (x.tickInput v₂ (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n₂')
    (hSaved₂ : n₂'.savedConfirmation s = some C₂) :
    -- then `C₁` and `C₂` are compatible
    C₁.compatible C₂ = true := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hss2 : M.slotStart S.C (s + 2) = M.slotStart S.C (s + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1), Nat.mul_add, Nat.mul_add]
    omega
  have hv₁t : M.voteTime S.C s = M.slotStart S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hc : M.supportCutoff S.C s = M.voteTime S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have hv₂t : M.voteTime S.C (s + 1) = M.slotStart S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have ht₂ : M.supportCutoff S.C (s + 1) = M.voteTime S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  have hfr : M.viewFreeze S.C s = M.slotStart S.C s + 3 * Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
  have hfr' : M.supportCutoff S.C s + Δ S = M.viewFreeze S.C s := by omega
  have hfrR : ((M.viewFreeze S.C s : ℕ) : ℝ) = (M.supportCutoff S.C s : ℝ) + Δ S := by
    rw [← hfr']; push_cast; ring
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hscs : (M.slotStart S.C s : ℝ) < (M.supportCutoff S.C s : ℝ) := by
    exact_mod_cast (show M.slotStart S.C s < M.supportCutoff S.C s by omega)
  have h3a := le_max_left (3 * Δ S) Δs
  have h3b := le_max_right (3 * Δ S) Δs
  have h1a := le_max_left (Δ S) Δs
  have h1b := le_max_right (Δ S) Δs
  have hm1le : max (Δ S) Δs ≤ M.viewFreeze S.C s := by omega
  -- each validator's window, from one clock-ahead bound before `M.viewFreeze S.C s − max (3 * Δ S) Δs`, contains
  -- the window from one clock-ahead bound before the support cutoff of slot `s`, and Lemma 62's
  have hmR : (M.viewFreeze S.C s : ℝ) - max (3 * Δ S) Δs - ΔClockAhead ≤ (M.supportCutoff S.C s : ℝ) - ΔClockAhead := by
    have : (3 * Δ S : ℝ) ≤ ((max (3 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast le_max_left (3 * Δ S) Δs
    linarith
  have hlow : (M.viewFreeze S.C s : ℝ) - max (3 * Δ S) Δs ≤
      min (((M.supportCutoff S.C s : ℕ) : ℝ) + Δ S - max (Δ S) Δs) (M.slotStart S.C s) := by
    have h3 : ((max (Δ S) Δs : ℕ) : ℝ) ≤ ((max (3 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast max_le_max (by omega) le_rfl
    have h4 : (3 * Δ S : ℝ) ≤ ((max (3 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast le_max_left (3 * Δ S) Δs
    have hfR : ((M.viewFreeze S.C s : ℕ) : ℝ) = (M.slotStart S.C s : ℝ) + 3 * Δ S := by
      rw [hfr]; push_cast; ring
    exact le_min (by linarith) (by linarith)
  have hw₁ : ∀ j : ℕ, (M.supportCutoff S.C s : ℝ) - ΔClockAhead ≤ x.time j → j ≤ kF₁ → v₁ ∈ A.active j :=
    fun j hj hjk => hwin₁ j (le_trans hmR hj) hjk
  have hw₂ : ∀ j : ℕ, (M.supportCutoff S.C s : ℝ) - ΔClockAhead ≤ x.time j → j ≤ kF₂ → v₂ ∈ A.active j :=
    fun j hj hjk => hwin₂ j (le_trans hmR hj) hjk
  have hkF₁T := (E.tick_active kF₁ v₁ _ hkF₁).2.1
  have hkF₂T := (E.tick_active kF₂ v₂ _ hkF₂).2.1
  obtain ⟨kₑ₁, hkₑ₁, -, -⟩ := E.tick_of_active (M.supportCutoff S.C s) (by omega) v₁ fun j hj1 hj2 =>
    hw₁ j hj1 ((lt_of_time_lt M) x R (by linarith)).le
  obtain ⟨kₑ₂, hkₑ₂, -, -⟩ := E.tick_of_active (M.supportCutoff S.C s) (by omega) v₂ fun j hj1 hj2 =>
    hw₂ j hj1 ((lt_of_time_lt M) x R (by linarith)).le
  -- the early votes of each validator reach the other by its tick to the view freeze (Lemma 62, each way)
  have h12 := (lem62_early_vote_reaches_at M F U) S A x R GST s (M.supportCutoff S.C s)
    (M.supportCutoff S.C (s + 1)) (M.viewFreeze S.C s) (M.supportCutoff S.C s + Δ S) v₁ v₂ E hNet hSkew hRedeliver Sy
    (by omega) (by omega) kF₂ (by rw [hfr']; exact hkF₂)
    (fun i hi hik => hwin₂ i (by linarith [hlow]) hik) (by omega) kF₂ hkF₂
    (by rw [hfr', Nat.cast_sub hm1le]; exact hv₁₀) kₑ₁ hkₑ₁ k₁ hk₁ (by omega)
  have h21 := (lem62_early_vote_reaches_at M F U) S A x R GST s (M.supportCutoff S.C s)
    (M.supportCutoff S.C (s + 1)) (M.viewFreeze S.C s) (M.supportCutoff S.C s + Δ S) v₂ v₁ E hNet hSkew hRedeliver Sy
    (by omega) (by omega) kF₁ (by rw [hfr']; exact hkF₁)
    (fun i hi hik => hwin₁ i (by linarith [hlow]) hik) (by omega) kF₁ hkF₁
    (by rw [hfr', Nat.cast_sub hm1le]; exact hv₂₀) kₑ₂ hkₑ₂ k₂ hk₂ (by omega)
  exact (lem31_compatible_of_reach_at M F U) S A x R s v₁ v₂ n₁' n₂' C₁ C₂ E
    kF₁ hkF₁ (fun j hj hjk => hw₁ j (by linarith) hjk) kF₂ hkF₂ (fun j hj hjk => hw₂ j (by linarith) hjk)
    k₁ hk₁ k₂ hk₂ hRoots h12 h21 hUpdate₁ hSaved₁ hUpdate₂ hSaved₂

/-- Lemma 31 for a slot that starts after `GST`: two honest confirmation updates of slot `s + 1`
save compatible confirmations of slot `s`, when the network is synchronous from the start of slot
`s`, each validator is active from that start to the view freeze of slot `s` and honest at the
support cutoff of slot `s + 1`. No sync fact and no sync delay.

Restated with the delivery premises up to `M.supportCutoff S.C s + Δ S`, the deadline of the two
re-sends Lemma 62 reads. Why: `Lemma31.lean`'s proof, with Lemma 62 read through
`lem62_early_vote_reaches_of_slotStart_at` in each direction.

Read aloud: when slot `s` starts after `GST`, two validators active since it started, ticking to the cutoff where
the update for slot `s` runs, have that update save blocks of one chain.
 -/
theorem lem31_saved_confirmations_compatible_of_slotStart_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (v₁ v₂ : V) (n₁' n₂' : M.N)
    (C₁ C₂ : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks
      (M.supportCutoff S.C s + Δ S)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)

    -- the network is synchronous from the start of slot `s`
    (hGST : GST ≤ M.slotStart S.C s)
    -- `v₁` is active from `tStart₁`, more than both clock bounds before the start of slot `s`, up to
    -- its own tick to the view freeze of slot `s` (, Lemma 62's slot-start form), and from
    -- the start of slot `s` to its view freeze (the holder's window) (T-RC5-3)
    (tStart₁ : ℤ) (htStart₁ : (tStart₁ : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C s)
    (hv₁ : v₁ ∈ A.activeThroughoutToTick x tStart₁ (M.viewFreeze S.C s))
    (hv₁₀ : v₁ ∈ A.activeThroughout x (M.slotStart S.C s) (M.viewFreeze S.C s))
    -- `v₂` is active from `tStart₂`, more than both clock bounds before the start of slot `s`, up to
    -- its own tick to the view freeze of slot `s` (, Lemma 62's slot-start form), and from
    -- the start of slot `s` to its view freeze (the holder's window) (T-RC5-3)
    (tStart₂ : ℤ) (htStart₂ : (tStart₂ : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C s)
    (hv₂ : v₂ ∈ A.activeThroughoutToTick x tStart₂ (M.viewFreeze S.C s))
    (hv₂₀ : v₂ ∈ A.activeThroughout x (M.slotStart S.C s) (M.viewFreeze S.C s))
    -- `v₁` and `v₂` tick to the support cutoff of slot `s + 1` at `k₁`, `k₂`, where their updates run
    -- (the read point, T-RC10-1,)
    (k₁ : ℕ) (hk₁ : x.lbl k₁ = Event.tick v₁ (M.supportCutoff S.C (s + 1)))
    (k₂ : ℕ) (hk₂ : x.lbl k₂ = Event.tick v₂ (M.supportCutoff S.C (s + 1)))
    -- a root names one block among what honest validators hold, until the later real time of the two
    -- ticks to the support cutoff of slot `s + 1`
    (hRoots : RootsNameBlocksUntil M A x (max (x.time k₁) (x.time k₂)))
    (hUpdate₁ : ConfirmationUpdated M S.C S.P (x.tickInput v₁ (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n₁')
    (hSaved₁ : n₁'.savedConfirmation s = some C₁)
    (hUpdate₂ : ConfirmationUpdated M S.C S.P (x.tickInput v₂ (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n₂')
    (hSaved₂ : n₂'.savedConfirmation s = some C₂) :
    C₁.compatible C₂ = true := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hss2 : M.slotStart S.C (s + 2) = M.slotStart S.C (s + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1), Nat.mul_add, Nat.mul_add]
    omega
  have hv₁t : M.voteTime S.C s = M.slotStart S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hc : M.supportCutoff S.C s = M.voteTime S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have hv₂t : M.voteTime S.C (s + 1) = M.slotStart S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have ht₂ : M.supportCutoff S.C (s + 1) = M.voteTime S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  have hfr : M.viewFreeze S.C s = M.slotStart S.C s + 3 * Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
  have hfr' : M.supportCutoff S.C s + Δ S = M.viewFreeze S.C s := by omega
  have hfrR : ((M.viewFreeze S.C s : ℕ) : ℝ) = (M.supportCutoff S.C s : ℝ) + Δ S := by
    rw [← hfr']; push_cast; ring
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hscs : (M.slotStart S.C s : ℝ) < (M.supportCutoff S.C s : ℝ) := by
    exact_mod_cast (show M.slotStart S.C s < M.supportCutoff S.C s by omega)
  -- each validator's ticks to the view freeze of slot `s` and to the support cutoff of slot `s`
  obtain ⟨kF₁, hkF₁, hw₁⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hv₁
    (t₀ := (M.supportCutoff S.C s : ℝ) - ΔClockAhead) (by linarith)
  obtain ⟨kF₂, hkF₂, hw₂⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hv₂
    (t₀ := (M.supportCutoff S.C s : ℝ) - ΔClockAhead) (by linarith)
  have hkF₁T := (E.tick_active kF₁ v₁ _ hkF₁).2.1
  have hkF₂T := (E.tick_active kF₂ v₂ _ hkF₂).2.1
  obtain ⟨kₑ₁, hkₑ₁, -, -⟩ := E.tick_of_active (M.supportCutoff S.C s) (by omega) v₁ fun j hj1 hj2 =>
    hw₁ j hj1 ((lt_of_time_lt M) x R (by linarith)).le
  obtain ⟨kₑ₂, hkₑ₂, -, -⟩ := E.tick_of_active (M.supportCutoff S.C s) (by omega) v₂ fun j hj1 hj2 =>
    hw₂ j hj1 ((lt_of_time_lt M) x R (by linarith)).le
  -- the early votes of each validator reach the other by its tick to the view freeze (Lemma 62's slot-start
  -- form, each way)
  have h12 := (lem62_early_vote_reaches_of_slotStart_at M F U) S A x R GST s (M.supportCutoff S.C s)
    (M.supportCutoff S.C (s + 1)) (M.viewFreeze S.C s) (M.supportCutoff S.C s + Δ S) v₁ v₂ E hNet hSkew hRedeliver
    hGST (by omega) tStart₂ htStart₂ (by rw [hfr']; exact hv₂) (by omega) kF₂ hkF₂ kₑ₁ hkₑ₁ k₁ hk₁ (by omega)
  have h21 := (lem62_early_vote_reaches_of_slotStart_at M F U) S A x R GST s (M.supportCutoff S.C s)
    (M.supportCutoff S.C (s + 1)) (M.viewFreeze S.C s) (M.supportCutoff S.C s + Δ S) v₂ v₁ E hNet hSkew hRedeliver
    hGST (by omega) tStart₁ htStart₁ (by rw [hfr']; exact hv₁) (by omega) kF₁ hkF₁ kₑ₂ hkₑ₂ k₂ hk₂ (by omega)
  exact (lem31_compatible_of_reach_at M F U) S A x R s v₁ v₂ n₁' n₂' C₁ C₂ E
    kF₁ hkF₁ (fun j hj hjk => hw₁ j (by linarith) hjk) kF₂ hkF₂ (fun j hj hjk => hw₂ j (by linarith) hjk)
    k₁ hk₁ k₂ hk₂ hRoots h12 h21 hUpdate₁ hSaved₁ hUpdate₂ hSaved₂

end GoldilocksCorrectness.Record.Proofs.Executions

