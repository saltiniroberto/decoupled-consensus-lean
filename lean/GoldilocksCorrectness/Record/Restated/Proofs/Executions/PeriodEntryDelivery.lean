module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodCertificateEntry
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodBridges
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDeliveryBoundary
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodFastSupport
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodInduction
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89CountJUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma43
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma45
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89f
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Attestation
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Proofs.Executions.PeriodCertificateEntry
public import GoldilocksCorrectness.Proofs.Executions.PeriodFastSupport
public import GoldilocksCorrectness.Proofs.Executions.PeriodInduction
public import GoldilocksCorrectness.Proofs.Executions.Lemma89CountJUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Proofs.Executions.Lemma43
public import GoldilocksCorrectness.Proofs.Executions.Lemma45
public import GoldilocksCorrectness.Proofs.Executions.Lemma89f
public import GoldilocksCorrectness.Proofs.Routines.Attestation
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodEntryDeliveryLine
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# PeriodEntryDelivery, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/PeriodEntryDelivery.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: the fast blocks of an updater's
update are the confirmation it saved or ancestors of it, and kit fact K3, a certified block of a
chain an honest active voter holds before its vote reaches the voter's tree before its view freezes.
The page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff
  dutyWindowStart_succ_lt_supportCutoff one_le_Δ slotStart_eq slotStart_mono supportCutoff_eq
  supportCutoff_mono viewFreeze_eq voteTime_eq voteTime_mono)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

open GoldilocksCorrectness.Record.Statements.Routines (ProgressCertOn)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans compatible_of_ancestorEq_compatible)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **The fast blocks of an update are ancestors of its saved confirmation.** For an updater `u`
of slot `s'`, when the state right after its tick at `M.supportCutoff S.C (s' + 1)` has saved `C'`
as the confirmation of slot `s'`, every fast block of that state is `C'` or an ancestor of `C'`.

Why: the tick ran the confirmation update of slot `s' + 1`, whose answer's saved confirmation and
fast blocks are the state's (`update_state_of_duty`); the update's fast blocks are blocks of its
path, the ancestors of the confirmation it saves (`fast_blocks_ancestorEq_saved`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s'`: the slot; `u`: the updater;
  `C'`: the saved confirmation.

Read aloud: every fast block an updater of slot `s'` holds right after its update is the
confirmation `C'` it saved for `s'` or an ancestor of `C'`. -/
theorem fast_blocks_ancestorEq_saved_of_updater (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s' : ℕ) (u : V) (C' : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hu : u ∈ updaterAt M S A x s')
    (hSaved : (x.tickOutput u (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C')
      :
    ∀ D ∈ (x.tickOutput u (M.supportCutoff S.C (s' + 1))).fastBlocks, D.AncestorEq C' := by
  have hv := hu
  obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  obtain ⟨n'', sent, hrun, hA, hSv, hFb, -, -⟩ := (update_state_of_tick M F U) S A x R s' u E hk'
    ((tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hv
      ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_lt_supportCutoff M.toSlotLayout
        F.sched U) S (s' + 1)))
  have hcu := (confirmationUpdated_of_cutoff_tickInput M F U) x R s' u n'' sent hrun hA
  have hS : M.savedConfirmation n'' (s' + 1 - 1) = some C' := by
    rw [Nat.add_sub_cancel, ← hSv]; exact hSaved
  intro D hD
  rw [hFb] at hD
  exact GoldilocksCorrectness.Record.Proofs.Routines.fast_blocks_ancestorEq_saved (Nat.succ_ne_zero s') hcu hS D hD

/-- **Kit fact K3: the certified entry reaches the voter before its view freezes.** The proof;
the audited statement is in `Statements/Executions/PeriodEntryDeliveryStatements.lean`. With
`s' = σ + 1`: `u` ticks to the vote time of `s'` at a step `kv` whose real time is at most `ΔClockBehind`
after that vote time (`tick_of_honestActiveAt`). K1 (`cert_entry_held_by_attester`) at `kv` gives an honest
attester `uₐ` whose tick `ka` to the support cutoff of `sₐ + 1` is before `kv`, so `sₐ + 1 ≤ σ`, with `T` in
its tree at `ka` and `T` an ancestor of a fast block `F` of that update. A holder of `T` at a step whose time
is at most a bound `X` either reaches `u`'s tick to the view freeze of `σ` through the synchrony premise
`P.hSync`, or satisfies the antecedent of the bundle's delivery line `P.hDelT` (`held_reaches_voter_or_line`),
when the relay's suspended deadline is at most `ΔClockAhead` before that view freeze
(`deadlineOutsideR_le_of`). When `M.supportCutoff S.C σ ≤ b₀` the holder is taken by the support cutoff of
`σ − 1` plus the clock bound, so that the relay keeps its ordinary deadline: the attester when
`sₐ + 1 ≤ σ − 1`; when `sₐ + 1 = σ = s + 1`, `F` is an ancestor of the hand-over confirmation `B`, against
`hTB`; when `sₐ + 1 = σ ≥ s + 2`, an honest active supporter of `F` at slot `sₐ` (K2,
`fast_block_has_honest_supporter`), at its tick to the vote time of `sₐ`. When
`b₁ + max (Δ S) Δs ≤ M.supportCutoff S.C σ + Δ S`, the attester at its tick: the relay is due within the
network delay `ΔNet` of the latest of its time, `b₁` and `GST`, at most `ΔClockAhead` before the view freeze
of `σ` (`hNet`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `P`: the hypotheses; `s'`: the slot of the vote; `u`: the voter; `Y`: the held block; `T`: the
  certified block; `h`: its height.
- `Tb`: the time up to which `P`'s premises are read (`T` names the certified block); `hTb`: the later
  of the vote time of `s'` and the real time of `u`'s tick to it is at most `Tb`; `hRoots`: roots name blocks
  up to that real time.

Read aloud: at a slot `s'` whose previous votes were not owed inside the period, a certified block
`T` of a chain an honest active voter `u` holds before its vote, of chain-state height greater than
`B`'s and compatible with `u`'s finalized block, is in `u`'s tree before its view freezes. -/
theorem cert_entry_held_before_freeze (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs_F Tb : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotesUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F Tb (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet tW)
    (s' : ℕ) (u : V)
    (Y T : Block V) (h : Height)
    -- the later of the vote time of `s'` and the real time of `u`'s tick to it is at most `Tb`
    (hTb : max ((M.voteTime S.C s' : ℕ) : ℝ) (x.time (x.tickStep u (M.voteTime S.C s'))) ≤ Tb)
    (hRoots : RootsNameBlocksUntil M A x (max ((M.voteTime S.C s' : ℕ) : ℝ) (x.time (x.tickStep u (M.voteTime S.C s')))))
    (hs' : s + 2 ≤ s') (hgood : ¬ VotesOwedInPeriod M S Δs b₀ b₁ s')
    (hu : u ∈ honestActiveAt M S A x s')
    (hY : Y ∈ (x.tickInput u (M.voteTime S.C s')).tree) (hTY : T.AncestorEq Y)
    (hJ : ProgressCertOn M Y h T) (hTB : (M.chainStateOf S.C B).h < (M.chainStateOf S.C T).h)
    (hF : (x.tickInput u (M.viewFreeze S.C (s' - 1))).finalized.compatible T = true) :
    T ∈ (x.tickInput u (M.viewFreeze S.C (s' - 1))).tree := by
  have hΔ := one_le_Δ S
  have hk := S.C.k_ge_two
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔr : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  obtain ⟨σ, rfl⟩ : ∃ σ, s' = σ + 1 := ⟨s' - 1, by omega⟩
  have hTbv : ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) ≤ Tb := le_trans (le_max_left _ _) hTb
  -- the delivery line `DelTLine` of the period's bundle, at this voter and entry
  have hD := P.hDelT (σ + 1) u Y T h
    ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (le_max_left _ _) hRoots)
    hs' hgood hu hY hTY hJ hTB hF
  simp only [Nat.add_sub_cancel] at hF hD ⊢
  have hgood' : M.supportCutoff S.C σ ≤ b₀ ∨ b₁ + max (Δ S) Δs ≤ M.supportCutoff S.C σ + Δ S := by
    unfold VotesOwedInPeriod at hgood
    simp only [Nat.add_sub_cancel] at hgood
    omega
  -- the schedule, as real numbers
  have hss : ∀ t : ℕ, M.slotStart S.C t = 4 * Δ S * t :=
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S
  have hvtE : ∀ t : ℕ, M.voteTime S.C t = M.slotStart S.C t + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S
  have hscE : ∀ t : ℕ, M.supportCutoff S.C t = M.voteTime S.C t + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S
  have hvfE : ∀ t : ℕ, M.viewFreeze S.C t = M.slotStart S.C t + 3 * Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S
  have hscR : ∀ t : ℕ, ((M.supportCutoff S.C t : ℕ) : ℝ) = 4 * (Δ S : ℝ) * t + 2 * Δ S := fun t => by
    rw [hscE, hvtE, hss]; push_cast; ring
  have hvtR : ∀ t : ℕ, ((M.voteTime S.C t : ℕ) : ℝ) = 4 * (Δ S : ℝ) * t + Δ S := fun t => by
    rw [hvtE, hss]; push_cast; ring
  have hcR : ((M.viewFreeze S.C σ : ℕ) : ℝ) = 4 * (Δ S : ℝ) * σ + 3 * Δ S := by
    rw [hvfE, hss]; push_cast; ring
  have hΔ0 : (0 : ℝ) ≤ 4 * Δ S := by positivity
  have hdwsR : ∀ q : ℕ, ((M.dutyWindowStart S.C (q + 1) : ℕ) : ℝ) ≤ 4 * (Δ S : ℝ) * q := fun q => by
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_le_slotStart
      M.toSlotLayout F.sched) S q
    have h2 : ((M.dutyWindowStart S.C (q + 1) : ℕ) : ℝ) ≤ ((M.slotStart S.C q : ℕ) : ℝ) := by
      exact_mod_cast h1
    rw [hss] at h2; push_cast at h2; exact h2
  have hmul : ∀ a b : ℕ, a ≤ b → 4 * (Δ S : ℝ) * a ≤ 4 * Δ S * b := fun a b hab =>
    mul_le_mul_of_nonneg_left (by exact_mod_cast hab) hΔ0
  -- `u`'s tick `kv` to the vote time of `σ + 1`, at a real time at most `ΔClockBehind` after it
  obtain ⟨kv, hkv, -, hkv2⟩ := (tick_of_honestActiveAt M F U) R E (t := M.voteTime S.C (σ + 1)) hu
    (by rw [hvtE]; omega) (by rw [hvtR]; push_cast; have := hdwsR σ; linarith)
    (by rw [hvtR, hscR]; push_cast; linarith)
  have hkvu : u ∉ A.corrupted kv := E.not_mem_corrupted_of_tick hkv
  have htiv : x.tickInput u (M.voteTime S.C (σ + 1)) = x.st kv u := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hkv]
  have hYv : Y ∈ (x.st kv u).tree := htiv ▸ hY
  have hkvTb : x.time kv ≤ Tb := by
    have := le_trans (le_max_right _ _) hTb
    rwa [(tickStep_eq_of_lbl M) x E hkv] at this
  -- K1: the honest attester `uₐ`, whose tick `ka` to the support cutoff of `sₐ + 1` is before `kv`
  obtain ⟨sₐ, uₐ, Fₐ, htₐ, huₐ, -, hFₐ, hTF, hTₐ⟩ :=
    (cert_entry_held_by_attester M F U Fx) S A x R kv u Y T h E
      (P.hAdvQ.mono (by linarith))
      ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
        (by rw [(tickStep_eq_of_lbl M) x E hkv]; exact le_max_right _ _) hRoots)
      hkvu hYv hTY hJ
  obtain ⟨ka, hka, -⟩ := Activity.mem_activeThroughoutToTick.1 huₐ
  have htka : x.tickStep uₐ (M.supportCutoff S.C (sₐ + 1)) = ka := (tickStep_eq_of_lbl M) x E hka
  rw [htka] at htₐ
  have hTa : T ∈ (x.st ka uₐ).tree := by
    have : x.tickInput uₐ (M.supportCutoff S.C (sₐ + 1)) = x.st ka uₐ := by
      unfold Trace.tickInput; rw [htka]
    exact this ▸ hTₐ
  have hkat := (E.tick_active ka uₐ _ hka).2
  rw [hscR] at hkat
  push_cast at hkat
  have hkau : uₐ ∉ A.corrupted ka := E.not_mem_corrupted_of_tick hka
  -- its tick is at or before the support cutoff of slot `σ`
  have hsₐ : sₐ + 1 ≤ σ := by
    have h1 := htime htₐ.le
    have h2 : 4 * (Δ S : ℝ) * sₐ < 4 * Δ S * σ := by
      rw [hvtR] at hkv2; push_cast at hkv2; linarith
    have h3 : (sₐ : ℝ) < σ := lt_of_mul_lt_mul_left h2 hΔ0
    have : sₐ < σ := by exact_mod_cast h3
    omega
  -- the margins of the period
  have hGSTR : (GST : ℝ) + max ((Δ S : ℕ) : ℝ) (Δs : ℝ) ≤ 4 * (Δ S : ℝ) * s + 6 * Δ S := by
    have : ((GST + max (Δ S) Δs : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) := by
      exact_mod_cast P.hGST
    push_cast at this; rw [hscR] at this; push_cast at this; linarith
  have hb₀R : 4 * (Δ S : ℝ) * s + 6 * Δ S ≤ b₀ := by
    have : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ (b₀ : ℝ) := by exact_mod_cast P.hb₀
    rw [hscR] at this; push_cast at this; linarith
  have hmΔ : ((Δ S : ℕ) : ℝ) ≤ max ((Δ S : ℕ) : ℝ) (Δs : ℝ) := le_max_left _ _
  have hsσ := hmul (s + 1) σ (by omega)
  push_cast at hsσ
  have hGb : (GST : ℝ) + ΔNet ≤ b₀ := by linarith
  have hGc : (GST : ℝ) + ΔNet ≤ ((M.viewFreeze S.C σ : ℕ) : ℝ) - ΔClockAhead := by rw [hcR]; linarith
  have hRootsU : RootsNameBlocksUntil M A x (M.voteTime S.C (σ + 1)) :=
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (le_max_left _ _) hRoots
  -- a holder of `T` by a time at most `X` reaches `u`'s tick to the view freeze of `σ`, or the line's
  -- antecedent holds and the line puts `T` there
  have hreach : ∀ (j : ℕ) (w : V) (X : ℝ), w ∉ A.corrupted j → T ∈ (x.st j w).tree → x.time j ≤ X →
      X ≤ ((M.supportCutoff S.C σ : ℕ) : ℝ) + ΔClockBehind →
      X + ΔNet ≤ ((M.viewFreeze S.C σ : ℕ) : ℝ) - ΔClockAhead →
      (X + ΔNet ≤ b₀ ∨ (b₁ : ℝ) + ΔNet ≤ ((M.viewFreeze S.C σ : ℕ) : ℝ) - ΔClockAhead) →
      T ∈ (x.tickInput u (M.viewFreeze S.C σ)).tree := by
    intro j w X hwj hTj hjX hXc hX hcase
    rcases (held_reaches_voter_or_line M F U) R E hSkew hRedeliver hΔs P.hSync P.hParent σ u hu hRootsU
        hwj hTj (le_trans hjX hXc)
        (fun τ hτ => deadlineOutsideR_le_of (le_trans hτ hjX) hGb hGc hX hcase) hF with hin | hant
    · exact hin
    · exact hD hant
  rcases hgood' with hb | hb
  · -- the previous votes were due before the period
    have hbR : 4 * (Δ S : ℝ) * σ + 2 * Δ S ≤ b₀ := by
      have : ((M.supportCutoff S.C σ : ℕ) : ℝ) ≤ (b₀ : ℝ) := by exact_mod_cast hb
      rw [hscR] at this; exact this
    -- a holder by `4Δσ − 2Δ + ΔClockBehind`, the support cutoff of `σ − 1` plus the clock bound
    have hearly : ∀ (j : ℕ) (w : V), w ∉ A.corrupted j → T ∈ (x.st j w).tree →
        x.time j ≤ 4 * (Δ S : ℝ) * σ - 2 * Δ S + ΔClockBehind →
        T ∈ (x.tickInput u (M.viewFreeze S.C σ)).tree := fun j w hwj hTj hjX =>
      hreach j w _ hwj hTj hjX (by rw [hscR]; linarith) (by rw [hcR]; linarith) (Or.inl (by linarith))
    rcases Nat.lt_or_ge (sₐ + 1) σ with hlt | hge
    · -- the attester's tick is at or before the support cutoff of `σ − 1`
      have h1 := hmul (sₐ + 2) σ (by omega)
      push_cast at h1
      exact hearly ka uₐ hkau hTa (by linarith)
    · have heq : sₐ + 1 = σ := by omega
      rcases Nat.lt_or_ge (s + 1) σ with hσs | hσs
      · -- `σ ≥ s + 2`: an honest active supporter `w` of `Fₐ` at slot `sₐ`, at its tick to the vote time
        have hsc : M.supportCutoff S.C (sₐ + 1) ≤ M.voteTime S.C (σ + 1) := by
          rw [heq]
          have : ((M.supportCutoff S.C σ : ℕ) : ℝ) ≤ ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) := by
            rw [hscR, hvtR]; push_cast; linarith
          exact_mod_cast this
        have hscTb : M.supportCutoff S.C (sₐ + 1) ≤ Tb := by
          have : ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) ≤ (Tb : ℝ) := by linarith
          have : M.voteTime S.C (σ + 1) ≤ Tb := by exact_mod_cast this
          omega
        obtain ⟨w, hw, H_w, hHw, hFH⟩ := (fast_block_has_honest_supporter M F U) S A x R anchor sₐ uₐ
          E hSkew (votesCastByOwner_of_unforgeability M F S A x R E)
          ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
            (by have : ((M.supportCutoff S.C (sₐ + 1) : ℕ) : ℝ) ≤ ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) := by
                  exact_mod_cast hsc
                exact le_trans this (le_max_left _ _)) hRoots)
          (P.hSleepK.mono M hscTb)
          (le_trans P.hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono
            M.toSlotLayout F.sched) S (by omega)))
          huₐ Fₐ hFₐ
        obtain ⟨q, hq⟩ : ∃ q, sₐ = q + 1 := ⟨sₐ - 1, by omega⟩
        obtain ⟨kw, hkw, -, hkw2⟩ := (tick_of_honestActiveAt M F U) R E (t := M.voteTime S.C sₐ)
          (Finset.mem_inter.1 hw).1 (by rw [hvtE]; omega)
          (by rw [hvtR, hq]; have := hdwsR q; push_cast; linarith)
          (by rw [hvtR, hscR]; push_cast; linarith)
        have htiw : x.tickInput w (M.voteTime S.C sₐ) = x.st kw w := by
          unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hkw]
        have hTw : T ∈ (x.st kw w).tree :=
          (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E kw w
            H_w T (htiw ▸ hHw) (ancestorEq_trans hTF hFH)
        rw [hvtR] at hkw2
        have h1 : (sₐ : ℝ) + 1 = σ := by exact_mod_cast heq
        exact hearly kw w (E.not_mem_corrupted_of_tick hkw) hTw (by
          have : 4 * (Δ S : ℝ) * sₐ = 4 * Δ S * σ - 4 * Δ S := by rw [← h1]; ring
          linarith)
      · -- `σ = s + 1`: the hand-over update, whose fast blocks are ancestors of `B`
        have hsₐs : sₐ = s := by omega
        subst hsₐs
        exfalso
        have hFB := (fast_blocks_ancestorEq_saved_of_updater M F U) S A x R sₐ uₐ B E huₐ
          (P.hHand.2.1 uₐ huₐ).1 Fₐ hFₐ
        have hle := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C
          (ancestorEq_trans hTF hFB)
        exact absurd hle (Nat.not_le.mpr hTB)
  · -- the previous votes were due after the period plus its recovery: the attester at its tick
    have hbR : (b₁ : ℝ) + max ((Δ S : ℕ) : ℝ) (Δs : ℝ) ≤ 4 * (Δ S : ℝ) * σ + 3 * Δ S := by
      have : ((b₁ + max (Δ S) Δs : ℕ) : ℝ) ≤ ((M.supportCutoff S.C σ + Δ S : ℕ) : ℝ) := by
        exact_mod_cast hb
      push_cast at this; rw [hscR] at this; linarith
    have h1 := hmul (sₐ + 1) σ hsₐ
    push_cast at h1
    exact hreach ka uₐ (4 * (Δ S : ℝ) * σ + 2 * Δ S + ΔClockBehind) hkau hTa (by linarith)
      (by rw [hscR]) (by rw [hcR]; linarith) (Or.inr (by rw [hcR]; linarith))

end GoldilocksCorrectness.Record.Proofs.Executions

