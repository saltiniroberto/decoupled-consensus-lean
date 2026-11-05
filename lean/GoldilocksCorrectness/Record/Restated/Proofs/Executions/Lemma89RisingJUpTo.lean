module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89RisingJ
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89CountJUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89QuietJUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma89RisingJ
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma89CountJUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma89QuietJUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption

@[expose] public section

/-!
# Lemma89RisingJUpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89RisingJUpTo.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: no honest `head_height_floor` (the
least chain-state height a viable block may have) reaching one more than a quiet honest round
opening slot's proposal before its support cutoff, restated with `SynchronyFromWakeUpTo` and
`CatchUpOnWakeUpTo` at a bound on the deadlines. The page's routine-level theorems are the facts'
fields or have their twins in phase A.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff anchorCW)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slotStart_mono supportCutoff_eq
  supportCutoff_mono voteTime_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq ancestorEq_compatible ancestorEq_antisymm)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **`floor_le_before_quiet_upTo` at an early step** (rule R3: a validator's state is read at a step it is honest at). In the climb's
context, with its end step `k₀` at least the step before the support cutoff of slot `s₀' + 1`, for the opening `i'` (`QuietCtx`
with `s₀'`, `s₃`) whose proposal `B₂` has chain-state height `h` with `h + 1` equal to `H₂` or `H₂ + 1`: the state of a validator
`u` at a step `j` whose real time is greater than `T₁` and less than one delay after the start of slot `s₀' + 1 − k`, with `u`
outside the adversary set at `j`, has `head_height_floor` at most `h`.

Why: take a member `w₀` of slot `s₀' + 1` (outside the adversary set up to the support cutoff of slot `s₀' + 2`; fewer than a
third are ever in it). By clause 1 of the opening, `w₀`'s `head_height_floor` at its tick to the vote time of slot `s₀' + 1` is
at most the chain-state height of `B₂`'s parent, so at most `h`. A `head_height_floor` of at least `h + 1` at `u` at `j` reaches
`w₀` by its tick to `τ + Δ`, `τ` one delay after the end of the range of `j` (`ClimbCtx.spread_level_floor`, or `_succ`: the
block that witnesses it was relayed when it entered `u`'s tree, while `u` was outside the adversary set), and every later step
of `w₀` up to its vote-time tick, which is before `k₀`, keeps it: a contradiction.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `CC`: the climb's context; `C'`: the opening's context; `h`: the height; `B₂`: the proposal; `u`: the validator;
  `j`: the step.

Restated with the delivery premises up to the bounds of the bundles `ClimbCtxUpTo` and `QuietCtxUpTo`, read at
`releaseOf M S.C`.

Read aloud: in the climb's context, no validator outside the adversary set at a step after `T₁` and before one delay after
the start of slot `s₀' + 1 − k` has, there, a `head_height_floor` greater than the chain-state height `h` of the proposal of
the honest round opening slot `s₀' + 1`. -/
theorem floor_le_before_quiet_st_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {GST tGAT tAwakeEnd T₁ r H₂ m i' : ℕ} {rs : ℕ → ℕ} {s₀' s₃ : ℕ} {k₀ : ℕ}
    {Δs : ℕ} {ΔNet : ℕ} (CC : ClimbCtxUpTo M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    (C' : QuietCtxUpTo M S A x GST tGAT tAwakeEnd r m i' rs s₀' s₃ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    (h : ℕ) (hh : h + 1 = H₂ ∨ h = H₂) (B₂ : Block V) (hB₂ : ProposalAt M S x (s₀' + 1) B₂)
    (hB₂h : (M.chainStateOf S.C B₂).h = h) (u : V) (j : ℕ)
    (hj1 : (T₁ : ℝ) < x.time j)
    (hj2 : x.time j < ((M.slotStart S.C (s₀' + 1 - S.C.k) + Δ S : ℕ) : ℝ))
    (hu : u ∉ A.corrupted j)
    -- the climb's end step is at least the step before the support cutoff of slot `s₀' + 1`
    (hk₀ : x.stepBefore (M.supportCutoff S.C (s₀' + 1)) ≤ k₀) :
    M.head_height_floor (x.st j u) ≤ h := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hSkew := C'.hSkew
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hAΔ : ΔClockAhead < Δ S := by linarith
  have hBΔ : ΔClockBehind < Δ S := by linarith
  have hw0 := (C'.win M F U) (le_refl (s₀' + 1))
  have hsR := C'.sR
  have hEnd := C'.cut_end M F
  have hanc := hw0.2
  rw [GoldilocksCorrectness.Proofs.Routines.anchorCW_eq] at hanc
  have hte := fun a => (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S a
  have hse := fun a => (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S a
  obtain ⟨hv1, hc1, -, hs1', -⟩ := hte (s₀' + 1)
  obtain ⟨-, hc2, -, -, -⟩ := hte (s₀' + 1 + 1)
  obtain ⟨-, -, -, hsw0, -⟩ := hte (s₀' + 1 - S.C.k - 1)
  rw [show s₀' + 1 - S.C.k - 1 + 1 = s₀' + 1 - S.C.k by have := hw0.1; omega] at hsw0
  have hs1 := hse (s₀' + 1)
  have hs2 := hse (s₀' + 1 + 1)
  have hsk := hse (s₀' + 1 - S.C.k)
  have hsk1 : M.slotStart S.C (s₀' + 1 - S.C.k) + 4 * Δ S * S.C.k = M.slotStart S.C (s₀' + 1) := by
    rw [hsk, hs1, ← Nat.mul_add, show s₀' + 1 - S.C.k + S.C.k = s₀' + 1 by have := hw0.1; omega]
  have hk4 := Nat.mul_le_mul_left (4 * Δ S) hk
  have hcm := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
    (show s₀' + 1 + 1 ≤ s₃ by have := S.C.R_ge_two; omega)
  -- `τ`: one delay after the end of the range of `j`; `τ + Δ` is at most the vote time of slot `s₀' + 1`
  set τ := M.slotStart S.C (s₀' + 1 - S.C.k) + 2 * Δ S with hτ
  have hτv : τ + Δ S ≤ M.voteTime S.C (s₀' + 1) := by omega
  have hjτ : x.time j ≤ (τ : ℝ) := by
    have : ((M.slotStart S.C (s₀' + 1 - S.C.k) + Δ S : ℕ) : ℝ) ≤ (τ : ℝ) := by exact_mod_cast (show _ ≤ τ by omega)
    linarith
  have hjc : x.clockValue j u ≤ τ := by
    have h1 := (clockValue_le_time_add_ahead M F) x R E j u
    have h2 : max 0 (x.time j + ΔClockAhead) < (τ : ℝ) := by
      refine max_lt (by have : (1 : ℝ) ≤ (τ : ℝ) := by exact_mod_cast (show 1 ≤ τ by omega)
                        linarith) ?_
      have : ((M.slotStart S.C (s₀' + 1 - S.C.k) + Δ S : ℕ) : ℝ) + Δ S = (τ : ℝ) := by
        exact_mod_cast (show _ = τ by omega)
      linarith
    exact_mod_cast (le_of_lt (lt_of_le_of_lt h1 h2))
  -- a member `w₀` of slot `s₀' + 1`: outside the adversary set up to the support cutoff of slot `s₀' + 2`
  have hcE : M.supportCutoff S.C (s₀' + 1 + 1) ≤ tAwakeEnd := le_trans hcm hEnd
  obtain ⟨w₀, hvT⟩ : ∃ v : V, A.HonestThroughTime x (M.supportCutoff S.C (s₀' + 1 + 1)) v := by
    by_contra hall
    have hall' : ∀ w ∈ (Finset.univ : Finset V),
        ∃ i : ℕ, x.time i ≤ (M.supportCutoff S.C (s₀' + 1 + 1) : ℕ) ∧ w ∈ A.corrupted i := by
      intro w _
      by_contra hn
      exact hall ⟨w, fun i hi hadv => hn ⟨i, hi, hadv⟩⟩
    have h3 := ((GoldilocksCorrectness.Record.Proofs.Executions.adversaryFewerThanThirdUntil_of_le M F) hcE C'.hThird)
      Finset.univ hall'
    rw [Finset.card_univ] at h3
    unfold validator_count at h3
    omega
  have hw₀b : w₀ ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀' + 1 + 1)) :=
    Activity.not_mem_corruptedAtTime.2 fun i hi => hvT i hi
  have hw₀H : w₀ ∈ Hon M S A x (s₀' + 1) := by
    unfold Hon roundMembers
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hw₀b⟩
  have hw₀A := C'.awakeHonest M F R E w₀ (t₁ := tGAT) le_rfl hcE hw₀b
  -- clause 1 at `w₀`: its `head_height_floor` at its vote-time tick is at most `h`
  obtain ⟨-, hfl₀⟩ := (C'.clause1 M F R E U Fx) B₂ hB₂ w₀ hw₀H
  obtain ⟨iB, hlB, hsentB⟩ := hB₂
  obtain ⟨-, -, hBpar?, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.proposal_parent_walk_end M F U) S A x R E s₀' iB B₂ _ hlB hsentB
  have hpar := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C
    (GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_parent? hBpar?)
  -- `w₀`'s ticks to `τ + Δ` and to the vote time of slot `s₀' + 1`
  have hGτ : tGAT + Δ S ≤ τ := by omega
  obtain ⟨kT, hkT, hkT1, hkT2⟩ := E.tick_of_mem_activeThroughout (fun _ _ h => R.time_mono h) hw₀A (t := τ + Δ S)
    (by
      have : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((τ : ℕ) : ℝ) := by exact_mod_cast hGτ
      push_cast at this ⊢; linarith)
    (by
      have : ((τ + Δ S : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀' + 1 + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show τ + Δ S + Δ S ≤ M.supportCutoff S.C (s₀' + 1 + 1) by omega)
      linarith)
    (by omega)
  obtain ⟨kv, hkv, hkv1, hkv2⟩ := E.tick_of_mem_activeThroughout (fun _ _ h => R.time_mono h) hw₀A
    (t := M.voteTime S.C (s₀' + 1))
    (by
      have : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((M.voteTime S.C (s₀' + 1) : ℕ) : ℝ) := by exact_mod_cast (show _ ≤ _ by omega)
      push_cast at this; linarith)
    (by
      have : ((M.voteTime S.C (s₀' + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀' + 1 + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show M.voteTime S.C (s₀' + 1) + Δ S ≤ M.supportCutoff S.C (s₀' + 1 + 1) by omega)
      linarith)
    (by omega)
  have hkTv : kT ≤ kv := (tick_step_le_of_le M F) E hkT hkv hτv
  have hw₀kv : w₀ ∉ A.corrupted kv := E.not_mem_corrupted_of_tick hkv
  -- `w₀`'s vote-time tick is before the support cutoff of slot `s₀' + 1`, so before `k₀`, and before `aR M S r`
  have hkvc : x.time kv < ((M.supportCutoff S.C (s₀' + 1) : ℕ) : ℝ) := by
    have : ((M.voteTime S.C (s₀' + 1) : ℕ) : ℝ) + Δ S = ((M.supportCutoff S.C (s₀' + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C (s₀' + 1) + Δ S = M.supportCutoff S.C (s₀' + 1) by omega)
    linarith
  have hkvk₀ : kv ≤ k₀ := le_trans (((time_lt_iff_le_stepBefore M) x R E (by omega)).1 hkvc) hk₀
  -- `w₀`'s tick to `T₁ + Δ`, before its vote-time tick (the UpTo kit reads it)
  have hT₁τ : T₁ + Δ S ≤ τ := by
    have : (T₁ : ℝ) < ((M.slotStart S.C (s₀' + 1 - S.C.k) + Δ S : ℕ) : ℝ) := lt_trans hj1 hj2
    have h' : T₁ < M.slotStart S.C (s₀' + 1 - S.C.k) + Δ S := by exact_mod_cast this
    omega
  have hTG := CC.hT₁
  obtain ⟨kL, hkL, -, -⟩ := E.tick_of_mem_activeThroughout (fun _ _ h => R.time_mono h) hw₀A (t := T₁ + Δ S)
    (by
      have : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((T₁ + Δ S : ℕ) : ℝ) := by exact_mod_cast (show tGAT + Δ S ≤ T₁ + Δ S by omega)
      push_cast at this ⊢; linarith)
    (by
      have : ((T₁ + Δ S : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀' + 1 + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show T₁ + Δ S + Δ S ≤ M.supportCutoff S.C (s₀' + 1 + 1) by omega)
      linarith)
    (by omega)
  have hkLv : kL ≤ kv := (tick_step_le_of_le M F) E hkL hkv (by omega)
  have hT₁a : T₁ + Δ S ≤ aR M S r := by
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show s₀' + 1 ≤ r * S.C.R + 1 by have := C'.hir; omega)
    have : M.supportCutoff S.C (s₀' + 1) ≤ aR M S r := by unfold aR; exact h1
    omega
  have hkvR : x.time kv < aR M S r := by
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show s₀' + 1 ≤ r * S.C.R + 1 by have := C'.hir; omega)
    have : ((M.supportCutoff S.C (s₀' + 1) : ℕ) : ℝ) ≤ ((aR M S r : ℕ) : ℝ) := by
      exact_mod_cast (show M.supportCutoff S.C (s₀' + 1) ≤ aR M S r by unfold aR; exact h1)
    linarith
  -- `w₀` is active from `tGAT` up to its tick to `τ + Δ`
  have hwA : ∀ l : ℕ, (tGAT : ℝ) ≤ x.time l → l ≤ kT → w₀ ∈ A.active l := fun l h1 h2 =>
    Activity.mem_active_of_mem_activeThroughout_of_time (fun _ _ h => R.time_mono h) hw₀A h1
      (by
        have : ((τ + Δ S : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀' + 1 + 1) : ℕ) : ℝ) := by
          exact_mod_cast (show τ + Δ S + Δ S ≤ M.supportCutoff S.C (s₀' + 1 + 1) by omega)
        linarith [R.time_mono h2])
  have hTi : x.tickInput w₀ (M.voteTime S.C (s₀' + 1)) = x.st kv w₀ := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hkv]
  rw [hTi] at hfl₀
  by_contra hgt
  push Not at hgt
  rcases hh with hh | hh
  · have hL : H₂ ≤ M.head_height_floor (x.st j u) := by
      unfold Height at *
      omega
    have hsp := (CC.spread_level_floor M F U R E Fx) hj1 hjτ hjc hu hL hkT hkTv hwA hkvR
      hkvk₀ hw₀kv hT₁a hkL hkLv
    unfold Height at *
    omega
  · have hL : H₂ + 1 ≤ M.head_height_floor (x.st j u) := by
      unfold Height at *
      omega
    have hsp := (CC.spread_level_floor_succ M F U R E Fx) hj1 hjτ hjc hu hL hkT hkTv hwA hkvR
      hkvk₀ hw₀kv
    unfold Height at *
    omega

/-- **`floor_le_before_quiet_upTo` per tick** (rule R3: a validator's own state is read at its own ticks). Under the
hypotheses of `floor_le_before_quiet_upTo`: every tick of a validator `u` outside the adversary set, to a clock value `c` from
the start of slot `s₀' + 1 − k` to the support cutoff of slot `s₀' + 1`, starts from a state whose `head_height_floor`
is at most `h`.

Why: `floor_le_before_quiet_upTo` before the time `c − Δ S`; from `u`'s last step before that time to its tick to `c`, `u`
has no `ForkChoiceChangeStep` (`C'.hNo`, from `u`'s tick to the window's start value, which comes before that time, to
the tick, before the support cutoff of slot `s₃`), and a step that is not one does not raise `head_height_floor`
(`floor_le_of_no_change_st`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `CC`: the climb's context; `C'`: the opening's context; `h`: the height; `B₂`: the proposal.

Read aloud: in the climb's context, no tick of an honest validator to a clock value from the start of slot
`s₀' + 1 − k` to the support cutoff of the honest round opening slot `s₀' + 1` starts from a `head_height_floor`
greater than the chain-state height `h` of that slot's proposal. -/
theorem floor_le_before_quiet_tick_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {GST tGAT tAwakeEnd T₁ r H₂ m i' : ℕ} {rs : ℕ → ℕ} {s₀' s₃ : ℕ} {k₀ : ℕ}
    {Δs : ℕ} {ΔNet : ℕ} (CC : ClimbCtxUpTo M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    (C' : QuietCtxUpTo M S A x GST tGAT tAwakeEnd r m i' rs s₀' s₃ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    (hT₁ : T₁ + Δ S ≤ M.slotStart S.C (s₀' + 1 - S.C.k - 1))
    (h : ℕ) (hh : h + 1 = H₂ ∨ h = H₂) (B₂ : Block V) (hB₂ : ProposalAt M S x (s₀' + 1) B₂)
    (hB₂h : (M.chainStateOf S.C B₂).h = h)
    -- the climb's end step is at least the step before the support cutoff of slot `s₀' + 1`
    (hk₀ : x.stepBefore (M.supportCutoff S.C (s₀' + 1)) ≤ k₀) :
    ∀ (u : V) (c kt : ℕ), M.slotStart S.C (s₀' + 1 - S.C.k) ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl kt = Event.tick u c → u ∉ A.corrupted kt →
      M.head_height_floor (x.tickInput u c) ≤ h := by
  intro u c kt hc1 hc2 hkt hukt
  have hk := S.C.k_ge_two
  have hw0 := (C'.win M F U) (le_refl (s₀' + 1))
  have hsR := C'.sR
  have hEnd := C'.cut_end M F
  have hanc := hw0.2
  rw [GoldilocksCorrectness.Proofs.Routines.anchorCW_eq] at hanc
  obtain ⟨hv0, -, -, hs0, hΔ⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s₀' + 1 - S.C.k - 1)
  have hsw : s₀' + 1 - S.C.k - 1 + 1 = s₀' + 1 - S.C.k := by have := hw0.1; omega
  rw [hsw] at hs0
  have hcm := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
    (show s₀' + 1 + 1 ≤ s₃ by have := S.C.R_ge_two; omega)
  obtain ⟨-, hc1', -, hs1', -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s₀' + 1)
  have hc2' := ((GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s₀' + 1 + 1)).2.1
  have hA0 := E.ahead_nonneg
  have hSkew := C'.hSkew
  have hB0 := E.behind_nonneg
  obtain ⟨-, hkt1, hkt2⟩ := E.tick_active kt u c hkt
  -- `u` is outside the adversary set up to the time `c − Δ`, before its tick to `c`
  have hub : u ∉ A.corruptedAtTime x ((c - Δ S : ℕ) : ℝ) := by
    refine Activity.not_mem_corruptedAtTime.2 fun i hi => ?_
    have hit : x.time i < x.time kt := by
      have : ((c - Δ S + Δ S : ℕ) : ℝ) = (c : ℝ) := by exact_mod_cast (show c - Δ S + Δ S = c by omega)
      push_cast at this; linarith
    exact E.not_mem_corrupted_of_le ((lt_of_time_lt M) x R hit).le hukt
  have huA := C'.awakeHonest M F R E u (t₁ := tGAT) le_rfl (le_trans (show c - Δ S ≤ M.supportCutoff S.C s₃ by omega) hEnd) hub
  -- `u`'s tick to the window's start value, before the time `c − Δ`
  obtain ⟨k0, hk0l, hk0b, hk0t⟩ := E.tick_of_mem_activeThroughout (fun _ _ h => R.time_mono h) huA
    (t := M.voteTime S.C (s₀' + 1 - S.C.k - 1))
    (by
      have : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((M.voteTime S.C (s₀' + 1 - S.C.k - 1) : ℕ) : ℝ) := by
        exact_mod_cast (show _ ≤ _ by omega)
      push_cast at this; linarith)
    (by
      have : ((M.voteTime S.C (s₀' + 1 - S.C.k - 1) + Δ S : ℕ) : ℝ) ≤ ((c - Δ S : ℕ) : ℝ) := by
        exact_mod_cast (show _ ≤ _ by omega)
      push_cast at this ⊢; linarith)
    (by omega)
  have hk0sb : k0 ≤ x.stepBefore (c - Δ S) := by
    refine ((time_lt_iff_le_stepBefore M) x R E (by omega)).1 ?_
    have : ((M.voteTime S.C (s₀' + 1 - S.C.k - 1) + Δ S : ℕ) : ℝ) ≤ ((c - Δ S : ℕ) : ℝ) := by
      exact_mod_cast (show _ ≤ _ by omega)
    push_cast at this ⊢; linarith
  have hsbkt : x.stepBefore (c - Δ S) ≤ kt := by
    refine (stepBefore_le_of_le_time_st M F) R E ?_
    have : ((c - Δ S + Δ S : ℕ) : ℝ) = (c : ℝ) := by exact_mod_cast (show c - Δ S + Δ S = c by omega)
    push_cast at this ⊢; linarith
  have hk0kt : k0 ≤ kt := le_trans hk0sb hsbkt
  have hfl1 := (floor_le_of_no_change_st M F) S A x R E u hk0kt
    (fun j h1 h2 => C'.hNo u j k0 kt c hk0l h1 hkt (by omega) h2
      (E.not_mem_corrupted_of_le h2.le hukt))
  -- the tick to the window's start value is an early step: after `T₁`, before one delay after the start of slot `s₀' + 1 − k`
  have hfl2 := (floor_le_before_quiet_st_upTo M F U Fx) R E CC C' h hh B₂ hB₂ hB₂h u k0
    (by
      have : ((T₁ + Δ S : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C (s₀' + 1 - S.C.k - 1) : ℕ) : ℝ) := by
        exact_mod_cast (show T₁ + Δ S + Δ S ≤ M.voteTime S.C (s₀' + 1 - S.C.k - 1) by omega)
      push_cast at this; linarith)
    (by
      have : ((M.voteTime S.C (s₀' + 1 - S.C.k - 1) : ℕ) : ℝ) + Δ S ≤ ((M.slotStart S.C (s₀' + 1 - S.C.k) + Δ S : ℕ) : ℝ) := by
        exact_mod_cast (show M.voteTime S.C (s₀' + 1 - S.C.k - 1) + Δ S ≤ M.slotStart S.C (s₀' + 1 - S.C.k) + Δ S by omega)
      linarith)
    (E.not_mem_corrupted_of_le hk0kt hukt) hk₀
  have hTu : x.tickInput u c = x.st kt u := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hkt]
  rw [hTu]
  exact le_trans hfl1 hfl2

/-- **`floor_le_before_quiet_upTo` per tick, from `T₁ + 1 + Δ S`** (rule R3; F-P1-25). Under the hypotheses of
`floor_le_before_quiet_upTo`: every tick of a validator `u` outside the adversary set, to a clock value `c` from `T₁ + 1 + Δ S`
to the support cutoff of slot `s₀' + 1`, starts from a state whose `head_height_floor` is at most `h`.

Why: a tick at a real time less than the support cutoff starts from the state at its own step, which is from the step
before `T₁ + 1` (its real time is more than `c − Δ S`) to the step before the support cutoff
(`floor_le_before_quiet_st_upTo`); a tick at a real time at least the support cutoff is to a clock value at least the start of
slot `s₀' + 1 − k` (`floor_le_before_quiet_tick_upTo`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `CC`: the climb's context; `C'`: the opening's context; `h`: the height; `B₂`: the proposal.

Restated with the delivery premises up to the bundles' bounds.

Read aloud: in the climb's context, no tick of an honest validator to a clock value from `T₁ + 1 + Δ S` to the support
cutoff of the honest round opening slot `s₀' + 1` starts from a `head_height_floor` greater than the chain-state height
`h` of that slot's proposal. -/
theorem floor_le_before_quiet_tick_from_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {GST tGAT tAwakeEnd T₁ r H₂ m i' : ℕ} {rs : ℕ → ℕ} {s₀' s₃ : ℕ} {k₀ : ℕ}
    {Δs : ℕ} {ΔNet : ℕ} (CC : ClimbCtxUpTo M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    (C' : QuietCtxUpTo M S A x GST tGAT tAwakeEnd r m i' rs s₀' s₃ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    (hT₁ : T₁ + Δ S ≤ M.slotStart S.C (s₀' + 1 - S.C.k - 1))
    (h : ℕ) (hh : h + 1 = H₂ ∨ h = H₂) (B₂ : Block V) (hB₂ : ProposalAt M S x (s₀' + 1) B₂)
    (hB₂h : (M.chainStateOf S.C B₂).h = h)
    -- the climb's end step is at least the step before the support cutoff of slot `s₀' + 1`
    (hk₀ : x.stepBefore (M.supportCutoff S.C (s₀' + 1)) ≤ k₀) :
    ∀ (u : V) (c kt : ℕ), T₁ + 1 + Δ S ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl kt = Event.tick u c → u ∉ A.corrupted kt →
      M.head_height_floor (x.tickInput u c) ≤ h := by
  intro u c kt hc1 hc2 hkt hukt
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hSkew := C'.hSkew
  have hAΔ : ΔClockAhead < Δ S := by linarith
  have hBΔ : ΔClockBehind < Δ S := by linarith
  obtain ⟨-, hkt1, hkt2⟩ := E.tick_active kt u c hkt
  have hc1R : ((T₁ + 1 + Δ S : ℕ) : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  push_cast at hc1R
  by_cases hlt : c < M.slotStart S.C (s₀' + 1 - S.C.k)
  · have hTu : x.tickInput u c = x.st kt u := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hkt]
    rw [hTu]
    refine (floor_le_before_quiet_st_upTo M F U Fx) R E CC C' h hh B₂ hB₂ hB₂h u kt ?_ ?_ hukt hk₀
    · linarith
    · have : ((c : ℕ) : ℝ) + 1 ≤ ((M.slotStart S.C (s₀' + 1 - S.C.k) : ℕ) : ℝ) := by exact_mod_cast hlt
      push_cast
      have h1 : (1 : ℝ) ≤ ((Δ S : ℕ) : ℝ) := by exact_mod_cast one_le_Δ S
      linarith
  · push Not at hlt
    exact (floor_le_before_quiet_tick_upTo M F U Fx) R E CC C' hT₁ h hh B₂ hB₂ hB₂h hk₀ u c kt
      hlt hc2 hkt hukt

end GoldilocksCorrectness.Record.Proofs.Executions

