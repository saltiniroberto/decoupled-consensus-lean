module
public import GoldilocksCorrectness.Record.Restated.Proofs.View.Bridges
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89QuietJ
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Sleepy
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.View.Bridges
public import GoldilocksCorrectness.Proofs.Executions.Lemma89QuietJ
public import GoldilocksCorrectness.Proofs.Executions.Sleepy
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89RisingJ, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89RisingJ.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: the kit of the rising quiet honest
round opening slots of part B of Lemma 89, namely no honest `head_height_floor` reaching one more
than a quiet honest round opening slot's proposal before its support cutoff, an honest proposer
proposing, the next proposal after a rising quiet honest round opening slot, and every honest round
opening slot's proposer proposing. The page's routine-level theorems are the facts' fields or have
their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff
  proposalWindowStart anchorCW)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_of_anchor
  dutyWindowStart_succ_le_slotStart one_le_Δ proposalWindowStart_eqJ proposal_window_start_eqJ
  slotStart_cast slotStart_eq slotStart_mono slot_eq_of_mem supportCutoff_eq supportCutoff_mono
  voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (DREBEmits DREBEmits.bind DREBEmits.ite DREBEmits.pure)

open GoldilocksCorrectness.Proofs.Routines (ac_on_tick_emits_vote)

open GoldilocksCorrectness.Proofs.Routines (tick_emits_proposalJ)

open GoldilocksCorrectness.Proofs.Routines (wake_eq)

open GoldilocksCorrectness.Proofs.Routines (anchorCW_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Proofs.Executions (r_lt_of_lt_of_mono)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject healFrontSlots)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq ancestorEq_compatible ancestorEq_antisymm)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## No honest validator's `head_height_floor` (the least chain-state height a viable block may have) reaches above a quiet opening's proposal -/

/-- **`floor_le_before_quiet` at an early step** (rule R3: a validator's state is read at a step it is honest at). In the climb's
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

Read aloud: in the climb's context, no validator outside the adversary set at a step after `T₁` and before one delay after
the start of slot `s₀' + 1 − k` has, there, a `head_height_floor` greater than the chain-state height `h` of the proposal of
the honest round opening slot `s₀' + 1`. -/
theorem floor_le_before_quiet_st (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {GST tGAT tAwakeEnd T₁ r H₂ m i' : ℕ} {rs : ℕ → ℕ} {s₀' s₃ : ℕ} {k₀ : ℕ}
    (CC : ClimbCtx M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    (C' : QuietCtx M S A x GST tGAT tAwakeEnd r m i' rs s₀' s₃ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
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
  have hw₀A := C'.awakeHonest M F R w₀ (t₁ := tGAT) le_rfl hcE hw₀b
  -- clause 1 at `w₀`: its `head_height_floor` at its vote-time tick is at most `h`
  obtain ⟨-, hfl₀⟩ := (C'.clause1 M F R E hNet hSkew hRedeliver Sy hΔs U Fx) B₂ hB₂ w₀ hw₀H
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
    have hsp := (CC.spread_level_floor M F U R E hNet hSkew hRedeliver Sy hΔs Fx) hj1 hjτ hjc hu hL hkT hkTv hwA hkvR
      hkvk₀ hw₀kv
    unfold Height at *
    omega
  · have hL : H₂ + 1 ≤ M.head_height_floor (x.st j u) := by
      unfold Height at *
      omega
    have hsp := (CC.spread_level_floor_succ M F U R E hNet hSkew hRedeliver Sy hΔs Fx) hj1 hjτ hjc hu hL hkT hkTv hwA hkvR
      hkvk₀ hw₀kv
    unfold Height at *
    omega

/-- **`floor_le_before_quiet` per tick** (rule R3: a validator's own state is read at its own ticks). Under the
hypotheses of `floor_le_before_quiet`: every tick of a validator `u` outside the adversary set, to a clock value `c` from
the start of slot `s₀' + 1 − k` to the support cutoff of slot `s₀' + 1`, starts from a state whose `head_height_floor`
is at most `h`.

Why: `floor_le_before_quiet` before the time `c − Δ S`; from `u`'s last step before that time to its tick to `c`, `u`
has no `ForkChoiceChangeStep` (`C'.hNo`, from `u`'s tick to the window's start value, which comes before that time, to
the tick, before the support cutoff of slot `s₃`), and a step that is not one does not raise `head_height_floor`
(`floor_le_of_no_change_st`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `CC`: the climb's context; `C'`: the opening's context; `h`: the height; `B₂`: the proposal.

Read aloud: in the climb's context, no tick of an honest validator to a clock value from the start of slot
`s₀' + 1 − k` to the support cutoff of the honest round opening slot `s₀' + 1` starts from a `head_height_floor`
greater than the chain-state height `h` of that slot's proposal. -/
theorem floor_le_before_quiet_tick (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {GST tGAT tAwakeEnd T₁ r H₂ m i' : ℕ} {rs : ℕ → ℕ} {s₀' s₃ : ℕ} {k₀ : ℕ}
    (CC : ClimbCtx M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    (C' : QuietCtx M S A x GST tGAT tAwakeEnd r m i' rs s₀' s₃ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
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
  have hB0 := E.behind_nonneg
  obtain ⟨-, hkt1, hkt2⟩ := E.tick_active kt u c hkt
  -- `u` is outside the adversary set up to the time `c − Δ`, before its tick to `c`
  have hub : u ∉ A.corruptedAtTime x ((c - Δ S : ℕ) : ℝ) := by
    refine Activity.not_mem_corruptedAtTime.2 fun i hi => ?_
    have hit : x.time i < x.time kt := by
      have : ((c - Δ S + Δ S : ℕ) : ℝ) = (c : ℝ) := by exact_mod_cast (show c - Δ S + Δ S = c by omega)
      push_cast at this; linarith
    exact E.not_mem_corrupted_of_le ((lt_of_time_lt M) x R hit).le hukt
  have huA := C'.awakeHonest M F R u (t₁ := tGAT) le_rfl (le_trans (show c - Δ S ≤ M.supportCutoff S.C s₃ by omega) hEnd) hub
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
  have hfl2 := (floor_le_before_quiet_st M F U Fx) R E hNet hSkew hRedeliver Sy hΔs CC C' h hh B₂ hB₂ hB₂h u k0
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

/-- **`floor_le_before_quiet` per tick, from `T₁ + 1 + Δ S`** (rule R3; F-P1-25). Under the hypotheses of
`floor_le_before_quiet`: every tick of a validator `u` outside the adversary set, to a clock value `c` from `T₁ + 1 + Δ S`
to the support cutoff of slot `s₀' + 1`, starts from a state whose `head_height_floor` is at most `h`.

Why: a tick at a real time less than the support cutoff starts from the state at its own step, which is from the step
before `T₁ + 1` (its real time is more than `c − Δ S`) to the step before the support cutoff
(`floor_le_before_quiet_st`); a tick at a real time at least the support cutoff is to a clock value at least the start of
slot `s₀' + 1 − k` (`floor_le_before_quiet_tick`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `CC`: the climb's context; `C'`: the opening's context; `h`: the height; `B₂`: the proposal.

Read aloud: in the climb's context, no tick of an honest validator to a clock value from `T₁ + 1 + Δ S` to the support
cutoff of the honest round opening slot `s₀' + 1` starts from a `head_height_floor` greater than the chain-state height
`h` of that slot's proposal. -/
theorem floor_le_before_quiet_tick_from (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {GST tGAT tAwakeEnd T₁ r H₂ m i' : ℕ} {rs : ℕ → ℕ} {s₀' s₃ : ℕ} {k₀ : ℕ}
    (CC : ClimbCtx M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    (C' : QuietCtx M S A x GST tGAT tAwakeEnd r m i' rs s₀' s₃ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
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
    refine (floor_le_before_quiet_st M F U Fx) R E hNet hSkew hRedeliver Sy hΔs CC C' h hh B₂ hB₂ hB₂h u kt ?_ ?_ hukt hk₀
    · linarith
    · have : ((c : ℕ) : ℝ) + 1 ≤ ((M.slotStart S.C (s₀' + 1 - S.C.k) : ℕ) : ℝ) := by exact_mod_cast hlt
      push_cast
      have h1 : (1 : ℝ) ≤ ((Δ S : ℕ) : ℝ) := by exact_mod_cast one_le_Δ S
      linarith
  · push Not at hlt
    exact (floor_le_before_quiet_tick M F U Fx) R E hNet hSkew hRedeliver Sy hΔs CC C' hT₁ h hh B₂ hB₂ hB₂h hk₀ u c kt
      hlt hc2 hkt hukt

/-! ## An honest proposer proposes (copied from `Lemma90Inclusion.lean`, which cannot be imported
beside `Lemma89Stability.lean`: both declare `get_anchor_cases`) -/

/-- `honest_proposer_proposes` of `Lemma90Inclusion.lean`, copied, in the readers' form: when the
proposer of slot `q + 2` ticks to the start of slot `q + 2`, active since the trace's start or since a tick, after
its last restart, to a clock value at most the protocol's proposal window start of slot `q + 2`, that tick puts a
block on the wire.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `q`: the slot is `q + 2`.

Read aloud: an honest proposer of slot `q + 2`, active up to its tick to the slot's start from its proposal
window, puts a block on the wire at that tick. -/
theorem honest_proposer_proposesJ (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (q : ℕ)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hp : S.P.proposer (q + 2) ∈ A.activeThroughoutToTick x (proposal_window_start S.C (q + 2)) (M.slotStart S.C (q + 2))) :
    ∃ (i : ℕ) (B : Block V), x.lbl i = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) ∧
      (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i := by
  have hΔ := one_le_Δ S
  set p := S.P.proposer (q + 2) with hpdef
  -- the proposer's tick to the slot's start, and the outcome the step took
  obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hp
  obtain ⟨n', sent, hok, -, hsent⟩ := R.tick k' p (M.slotStart S.C (q + 2)) hk'
  have hin : x.tickInput p (M.slotStart S.C (q + 2)) = x.st k' p := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hk']
  -- the slot's start, read as the spec's time, and its slot
  have hcast := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_cast M.toSlotLayout F.sched U) S (q + 2)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (q + 2)
  have hslot : S.C.slot ((M.slotStart S.C (q + 2) : ℕ) : Int) = q + 2 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast, hss]
    have h4 : 0 < 4 * Δ S := by omega
    exact Nat.mul_div_cancel_left (q + 2) h4
  have htime : ((M.slotStart S.C (q + 2) : ℕ) : Int) =
      S.C.t_ (S.C.slot ((M.slotStart S.C (q + 2) : ℕ) : Int)) := by
    rw [hslot]; exact hcast
  -- the wake test: awake since a time at most the proposal window's start
  have hab : proposal_window_start S.C (q + 2) < ((M.slotStart S.C (q + 2) : ℕ) : Int) := by
    have h := GoldilocksCorrectness.Record.proposal_window_start_lt_slotStart S.C _ htime
    rwa [hslot] at h
  obtain ⟨τ, hτ, hτle⟩ := (awakeSince_le_of_mem_activeThroughoutToTick M F) x R E hab hp
  rw [hin] at hτ
  have hτ' : τ ≤ proposal_window_start S.C (q + 2) := by
    rcases hτle with h | h
    · rw [h, GoldilocksCorrectness.Proofs.Routines.proposal_window_start_eqJ S q]
      exact GoldilocksCorrectness.Proofs.Routines.proposal_window_start_zero_le_duty S.C (q + 1)
    · exact h
  obtain ⟨-, -, haw⟩ := F.tk.tick_clock_validator_awakeSince S.C S.P S.X _ _ n' sent hok
  rw [hτ] at haw
  have hawake : M.awake_since n' (proposal_window_start S.C (S.C.slot ((M.slotStart S.C (q + 2) : ℕ) : Int))) =
      true := by
    rw [F.rd.awake_since_eq, haw, hslot]
    exact decide_eq_true hτ'
  -- the node's validator is the proposer
  have hvi : p ∉ A.corrupted k' := E.not_mem_corrupted_of_tick hk'
  have hnv : (x.st k' p).v = S.P.proposer (S.C.slot ((M.slotStart S.C (q + 2) : ℕ) : Int)) := by
    rw [hslot, (lem11_node_invariant M F S A x R E k' p hvi).2.1]
  have hpos : 0 < S.C.slot ((M.slotStart S.C (q + 2) : ℕ) : Int) := by
    rw [hslot]; exact Nat.succ_pos _
  obtain ⟨B, hB⟩ := F.tk.tick_emits_proposal S.C S.P S.X (x.st k' p) _ n' sent hok hpos htime hnv hawake
  refine ⟨k', B, hk', ?_⟩
  rw [hsent, add_tsub_cancel_left]
  exact Multiset.mem_map.2 ⟨_, Multiset.mem_coe.2 hB, rfl⟩

/-! ## Every opening's proposer proposes -/

/-- **Every opening's proposer proposes.** For an opening `j ≤ m` of a sequence of honest round opening slots
whose phase starts at `tGAT + 4Δ · healFrontSlots`: the opening's proposer puts a block on the wire
at the start of slot `rs j * R`.

Why: the slot is at least `2k` slots after the anchor `anchorCW S tGAT` (`window_after_anchor`), so
the proposal window starts after `tGAT` (`dutyWindowStart_of_anchor`); the proposer is honest at the
support cutoff of its slot (`HonestOpeningSeq.honest`), hence before it (monotone corruption), and
awake (the phase's awake hypothesis up to `tAwakeEnd`, which bounds the last opening's support
cutoff); `honest_proposer_proposesJ`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tGAT`, `tAwakeEnd`: the phase; `m`:
  the index of the last honest round opening slot; `j`: the index of an honest round opening slot; `rs`: the rounds of the honest round opening slots.

Read aloud: the proposer of every honest round opening slot `j ≤ m` puts a block on the wire at the
start of slot `rs j * R`. -/
theorem opening_proposal_exists (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (tGAT tAwakeEnd m j : ℕ) (rs : ℕ → ℕ)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hj : j ≤ m) :
    ∃ B : Block V, ProposalAt M S x (rs j * S.C.R) B := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hmono := r_lt_of_lt_of_mono rs m hSeq.mono
  have h0j : rs 0 * S.C.R ≤ rs j * S.C.R := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h]
    · exact Nat.mul_le_mul_right _ (le_of_lt (hmono 0 j h hj))
  have hjm : rs j * S.C.R ≤ rs m * S.C.R := by
    rcases Nat.lt_or_ge j m with h | h
    · exact Nat.mul_le_mul_right _ (le_of_lt (hmono j m h le_rfl))
    · rw [show j = m by omega]
  have hEnd' : M.supportCutoff S.C (rs j * S.C.R) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S hjm) hSeq.last
  obtain ⟨h2k, hA⟩ := (window_after_anchor M F U) S A x rs m tGAT tAwakeEnd (rs j * S.C.R) hSeq h0j
  have hqH := hSeq.honest j hj
  set s'' := rs j * S.C.R with hs''def
  clear_value s''
  have hssA := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show s'' - 2 * S.C.k + 1 ≤ s'' by omega)
  have hcs'' := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s''
  have hvs'' := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s''
  have hqAH : S.P.proposer s'' ∈ A.activeThroughout x tGAT (M.supportCutoff S.C s'') :=
    (mem_activeThroughout_of_hAwake_honest_at M F) R E hAwake le_rfl hEnd' hqH
  have hs''2 : s'' - 2 + 2 = s'' := by omega
  have hpw := (GoldilocksCorrectness.Record.Proofs.Routines.proposalWindowStart_eqJ M.toSlotLayout F.sched U) S (s'' - 2)
  have hA21 : anchorCW S tGAT ≤ M.slotStart S.C (s'' - 2 + 1 + 1) := by
    rw [show s'' - 2 + 1 + 1 = s'' by omega]
    exact le_trans hA hssA
  have hdwA := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT (s'' - 2 + 1) hA21
  obtain ⟨iB', B', hl', hsent'⟩ := (honest_proposer_proposesJ M F U) S A x R (s'' - 2) E
    (by
      -- the producer on the window widened by the two clock bounds: it starts `ΔClockAhead` before the
      -- proposal window, at least one delay after `tGAT`, and ends `ΔClockBehind` after the slot's start, before its
      -- support cutoff
      have hcs := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s''
      have hvs := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s''
      have hA0 := E.ahead_nonneg
      have hB0 := E.behind_nonneg
      have hdsl := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_le_slotStart M.toSlotLayout F.sched) S (s'' - 2)
      have hsm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show s'' - 2 ≤ s'' by omega)
      have hpos : 0 < M.dutyWindowStart S.C (s'' - 2 + 1) := by omega
      have hdr := (duty_window_start_real_of_pos M F U) S (s'' - 2 + 1) hpos
      have hpwI := GoldilocksCorrectness.Proofs.Routines.proposal_window_start_eq S (s'' - 2)
      have hc1 : 1 ≤ M.slotStart S.C (s'' - 2 + 2) := by rw [hs''2]; omega
      refine (mem_activeThroughoutToTick_of_mem_activeThroughout M F) x R E hc1 ?_ ?_
      · rw [hpwI]
        have h1 := (duty_window_start_le_real M F U) S (s'' - 2 + 1)
        have h2 : ((M.dutyWindowStart S.C (s'' - 2 + 1) : ℕ) : ℝ) ≤ ((M.slotStart S.C (s'' - 2 + 2) : ℕ) : ℝ) := by
          rw [hs''2]; exact_mod_cast (show M.dutyWindowStart S.C (s'' - 2 + 1) ≤ M.slotStart S.C s'' by omega)
        exact_mod_cast (show ((duty_window_start S.C (s'' - 2 + 1) : ℤ) : ℝ) ≤ ((M.slotStart S.C (s'' - 2 + 2) : ℕ) : ℝ) by
          linarith)
      · rw [hpwI, hdr, hs''2]
        refine Activity.mem_activeThroughout_of_le ?_ ?_ hqAH
        · have : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.dutyWindowStart S.C (s'' - 2 + 1) : ℕ) : ℝ) := by
            exact_mod_cast (show tGAT + Δ S ≤ M.dutyWindowStart S.C (s'' - 2 + 1) by omega)
          linarith
        · have : ((M.slotStart S.C s'' : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C s'' : ℕ) : ℝ) := by
            exact_mod_cast (show M.slotStart S.C s'' + Δ S ≤ M.supportCutoff S.C s'' by omega)
          linarith)
  rw [hs''2] at hl' hsent'
  exact ⟨B', iB', hl', hsent'⟩

/-! ## The next proposal after a rising quiet opening -/

/-- **The next proposal after a rising quiet opening, and the opening's height.** In the climb's
context, for an opening `i < m` with `rs (i + 1) * R ≤ r * R`, no fork-choice change from
the vote time of slot `rs i * R − k − 1` to before the support cutoff of slot `rs (i + 1) * R`, no
root collision at an opening, and rising: the next opening's proposer proposes a block `B'` at slot
`rs (i + 1) * R`, higher than the opening's proposal `B`, which that proposer holds one time unit
after the start of the slot; and `B`'s chain-state height is `H₂ − 1` or `H₂`
(`H₂ ≤ h(B) + 1` and `h(B) ≤ H₂`).

Why: the next opening's proposer is honest and awake through its proposal window (the opening
sequence and the window from `anchorCW`), so it proposes (`honest_proposer_proposesJ`); it holds its
own proposal (`lem22a_proposer_holds_own_proposal`, the root collision excluded), at most `H₂ + 1`
high (A2, `held_height_le_before_action`), so `h(B) ≤ H₂` by rising. A committee member honest at
the action time has `head_height_floor` at most `B`'s height (the opening's second clause) and
the greatest chain-state height at least `H₂` (B2), so `H₂ ≤ h(B) + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `H₂`: the threshold; `m`: the index of the last honest round opening slot; `i`: the index of an honest round opening slot; `rs`: the rounds of the honest round opening slots;
  `B`: its proposal.

Roots name blocks until `aR M S r`: the climb's context `ClimbCtx` carries the premise at the action
time of round `r`; the opening's context `QuietCtx` reads up to the support cutoff of slot
`rs (i + 1) * R`, no later.

Read aloud: after a rising quiet honest round opening slot `i` with proposal `B`, the next honest
round opening slot's proposer proposes a block `B'` of greater chain-state height, holds it one time
unit after its slot's start, and `B`'s chain-state height is `H₂ − 1` or `H₂`. -/
theorem quiet_rising_next_proposal (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ r H₂ m i : ℕ) (rs : ℕ → ℕ)
    (B : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (aR M S r))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT) (hT₁s : tGAT + Δs ≤ T₁)
    (hTick : ∀ (c : ℕ) (w : V) (k : ℕ), T₁ ≤ c → x.lbl k = Event.tick w (c + Δ S) → x.time k ≤ tAwakeEnd → w ∉ A.corrupted k → ∃ k' : ℕ, x.lbl k' = Event.tick w c)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hH₂ : OldHeightAttained M S A x T₁ H₂)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hT₁0 : T₁ ≤ M.slotStart S.C (rs 0 * S.C.R - 2 * S.C.k))
    (hi : i < m) (hir : rs (i + 1) * S.C.R ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening M S A x rs m)
    (hNo : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C (rs (i + 1) * S.C.R) → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    (hRise : RisingAt M S A x rs i)
    (hB : ProposalAt M S x (rs i * S.C.R) B) :
    ∃ B' : Block V, ProposalAt M S x (rs (i + 1) * S.C.R) B' ∧
      (M.chainStateOf S.C B).h < (M.chainStateOf S.C B').h ∧
      B' ∈ (x.tickOutput (S.P.proposer (rs (i + 1) * S.C.R)) (M.slotStart S.C (rs (i + 1) * S.C.R))).tree ∧
      H₂ ≤ (M.chainStateOf S.C B).h + 1 ∧ (M.chainStateOf S.C B).h ≤ H₂ := by
  have hT₁0 : T₁ + Δ S ≤ M.slotStart S.C (rs 0 * S.C.R - S.C.k - 1) := by
    have hk := S.C.k_ge_two
    have hΔ := one_le_Δ S
    have hw := (GoldilocksCorrectness.Record.Proofs.Executions.window_after_anchor M F U) S A x rs m tGAT tAwakeEnd
      (rs 0 * S.C.R) hSeq le_rfl
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (show rs 0 * S.C.R - 2 * S.C.k + 1 ≤ rs 0 * S.C.R - S.C.k - 1 by have := hw.1; omega)
    have h2 : M.slotStart S.C (rs 0 * S.C.R - 2 * S.C.k + 1) =
        M.slotStart S.C (rs 0 * S.C.R - 2 * S.C.k) + 4 * Δ S := by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
        (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
    omega
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  obtain ⟨hs1, C⟩ := (quietCtx_of M F U) S A x R GST tGAT tAwakeEnd r m i rs E hNet hSkew hRedeliver Sy hΔs
    ((roots_cutoff_behind_of_aR M F U) S (by omega) E.ahead_nonneg hSkew hRoots) hParent hGST hThird hAwake
    hActive hCommittees hEnd hSeq hi
    ((opening_round_step M F) hSeq hi) hir hNoCol hNo
  have hB0 : ProposalAt M S x (rs i * S.C.R - 1 + 1) B := by rw [← hs1]; exact hB
  have hRise' := hRise
  set s₀ := rs i * S.C.R - 1 with hs₀def
  set s'' := rs (i + 1) * S.C.R with hs''def
  clear_value s₀ s''
  have hsR := C.sR
  have hEnd' := (C.cut_end M F)
  -- the times
  have hw0 := (C.win M F U) (le_refl (s₀ + 1))
  have h0s : rs 0 * S.C.R ≤ s₀ + 1 := (C.rs0 M F)
  have hT₁s₀ : T₁ + Δ S ≤ M.slotStart S.C (s₀ + 1 - S.C.k - 1) := by
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show rs 0 * S.C.R - S.C.k - 1 ≤ s₀ + 1 - S.C.k - 1 by
      omega)
    have h2 : M.slotStart S.C (rs 0 * S.C.R - 2 * S.C.k + 1) =
        M.slotStart S.C (rs 0 * S.C.R - 2 * S.C.k) + 4 * Δ S := by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
    omega
  have hssμ := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show s₀ + 1 - S.C.k - 1 ≤ s'' by omega)
  have hcs'' := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s''
  have hcrR := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S hir
  have haRr : aR M S r = M.supportCutoff S.C (r * S.C.R) + 4 * Δ S := by
    unfold aR
    exact (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S _
  have hvs'' := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s''
  have hAn := E.ahead_nonneg
  have hBn := E.behind_nonneg
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  -- the climb's bundle at the first step whose real time reaches the support cutoff of slot `r R` (F-P1-13)
  have CC := (ClimbCtx.of_clock M F U R E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hT₁s hThird hAwake hH₂
    hOld hEnd hTick (by omega))
  -- the next proposal `B'`
  obtain ⟨B', hB'⟩ := (opening_proposal_exists M F U) S A x R tGAT tAwakeEnd m (i + 1) rs E hAwake hSkew hSeq
    (by omega)
  rw [← hs''def] at hB'
  have hBB' := hRise B B' hB (by rw [← hs''def]; exact hB')
  -- the proposer of `B'` holds it after its tick to the slot's start
  have hB'0 : ProposalAt M S x (s'' - 1 + 1) B' := by
    rw [show s'' - 1 + 1 = s'' by omega]
    exact hB'
  have hPV' := (proposal_parent_viable_head M F U) S A x R E (s'' - 1) B' _ hB'0
  obtain ⟨iB'', hlB'', hsentB''⟩ := hB'0
  have hPV'' := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _
    ((nodeInv_tickInput_of_tick M F) S A x R E hlB'') _).1 hPV'
  obtain ⟨-, -, hB'par?, -⟩ := (proposal_parent_walk_end M F U) S A x R E (s'' - 1) iB'' B' _
    hlB'' hsentB''
  have hPB' := GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_parent? hB'par?
  have hRootNew' : ∀ B₁ ∈ (x.tickInput (S.P.proposer (s'' - 1 + 1)) (M.slotStart S.C (s'' - 1 + 1))).tree,
      B₁.root ≠ B'.root := by
    intro B₁ hB₁ heq
    apply hNoCol
    rw [(GoldilocksCorrectness.Record.Proofs.View.rootCollisionAtOpening_unfold M x)]
    refine ⟨i + 1, by omega, B', ?_, ?_⟩
    · rw [← hs''def]
      exact hB'
    · rw [← hs''def]
      rw [(GoldilocksCorrectness.Record.Proofs.View.rootCollisionAtProposal_unfold M x)]
      rw [show s'' - 1 + 1 = s'' by omega] at hB₁
      exact ⟨B₁, hB₁, heq⟩
  have hBq := (lem22a_proposer_holds_own_proposal M F U) S A x R (s'' - 1) iB'' B' _ E hlB''
    hsentB'' hRootNew' hPV''.1
    ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans hPV''.2.1 hPB')))
  have hl2 : x.lbl iB'' = Event.tick (S.P.proposer s'') (M.slotStart S.C s'') := by
    rw [show s'' - 1 + 1 = s'' by omega] at hlB''
    exact hlB''
  have hBq' : B' ∈ (x.tickOutput (S.P.proposer s'') (M.slotStart S.C s'')).tree := by
    have h' := hBq
    rw [show s'' - 1 + 1 = s'' by omega] at h'
    unfold Trace.tickOutput
    rw [(tickStep_eq_of_lbl M) x E hl2]
    exact h'
  -- the heights: `B'` is held at a step before the climb's end step
  have hiB : iB'' + 1 ≤ x.firstAt (M.supportCutoff S.C (r * S.C.R)) := by
    have hti := ((time_of_lbl_tick M) x R E hlB'').2.2
    rw [show s'' - 1 + 1 = s'' by omega] at hti
    by_contra hc
    push Not at hc
    have h1 := R.time_mono (show x.firstAt (M.supportCutoff S.C (r * S.C.R)) ≤ iB'' + 1 by omega)
    have h2 := E.le_time_firstAt (M.supportCutoff S.C (r * S.C.R))
    have : ((M.slotStart S.C s'' : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (r * S.C.R) : ℕ) : ℝ) := by
      exact_mod_cast (show M.slotStart S.C s'' + Δ S ≤ M.supportCutoff S.C (r * S.C.R) by omega)
    linarith [hSkew]
  have hB'top := (held_height_le_before_action M F Fx) S A x R E tAwakeEnd H₂ _ (iB'' + 1) _ B'
    hThird CC.hOldStep CC.hEndStep hiB hBq
  have hcl2 := (C.clause2_tick M F R E hNet hSkew hRedeliver Sy hΔs U Fx) B hB0
  have hA2 : anchorCW S tGAT ≤ M.slotStart S.C (s₀ + 1 + 1) :=
    le_trans hw0.2 ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
  have hMaj1 := (committee_majority_of_committeeSleepiness M F) S A x _ (s₀ + 1) hCommittees hA2
    (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (by have := C.sR; have := S.C.R_ge_two; omega)) (C.cut_end M F))
  obtain ⟨v₀, hv₀⟩ : (S.P.committee (s₀ + 1) ∩ roundMembers M S A x (s₀ + 1 + 1)).Nonempty :=
    Finset.card_pos.1 (by omega)
  have hv₀H : v₀ ∈ Hon M S A x (s₀ + 1) := (Finset.mem_inter.1 hv₀).2
  have hv₀b : v₀ ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1 + 1)) := (Finset.mem_sdiff.1 hv₀H).2
  have hsc₀2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s₀ + 1 + 1)
  have hv₀2 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₀ + 1 + 1)
  have hss₀1 : M.slotStart S.C (s₀ + 1 + 1) = M.slotStart S.C (s₀ + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s₀ + 1), Nat.mul_add, Nat.mul_one]
  have hss₀μ := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show s₀ + 1 - S.C.k - 1 ≤ s₀ + 1 by omega)
  have hcs₀ := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
    (show s₀ + 1 + 1 ≤ s'' by omega)
  -- B2 at `v₀`'s tick to the support cutoff of slot `s₀ + 2`, whose input the round's second clause reads
  -- (`clause2_tick`; `v₀` an updater of slot `s₀ + 1`, F-P1-29)
  have hdw₀ := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT (s₀ + 1) hA2
  obtain ⟨j, hjl, -⟩ := Activity.mem_activeThroughoutToTick.1 (C.hActive (s₀ + 1) (by omega)
    (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (by have := C.sR; have := S.C.R_ge_two; omega)) (C.cut_end M F)) v₀ hv₀b).2
  have hjt := ((time_of_lbl_tick M) x R E hjl).1
  have hv₀j : v₀ ∉ A.corrupted j := E.not_mem_corrupted_of_tick hjl
  have hc3R := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
    (show s₀ + 1 + 1 + 1 ≤ r * S.C.R by have := C.sR; have := S.C.R_ge_two; omega)
  have hc23 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S (s₀ + 1 + 1)
  have hBn₀ := E.behind_nonneg
  have hAn₀ := E.ahead_nonneg
  have hv₀A := (mem_activeThroughout_of_hAwake_honest_at M F) R E hAwake le_rfl
    (le_trans hcs₀ (C.cut_end M F)) hv₀b
  have hk₀v := (tickStep_spec M) x R E (t := M.slotStart S.C (s₀ + 1 - S.C.k - 1)) (v := v₀) (by omega)
    (Activity.mem_activeThroughout_of_le
      (by
        have : (tGAT : ℝ) + Δ S ≤ ((M.slotStart S.C (s₀ + 1 - S.C.k - 1) : ℕ) : ℝ) := by
          exact_mod_cast (show tGAT + Δ S ≤ M.slotStart S.C (s₀ + 1 - S.C.k - 1) by omega)
        linarith [hSkew])
      (by
        have : ((M.slotStart S.C (s₀ + 1 - S.C.k - 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) := by
          exact_mod_cast (show M.slotStart S.C (s₀ + 1 - S.C.k - 1) + Δ S ≤ M.supportCutoff S.C (s₀ + 1 + 1) by omega)
        linarith [hSkew]) hv₀A)
  have hkj : x.tickStep v₀ (M.slotStart S.C (s₀ + 1 - S.C.k - 1)) ≤ j := by
    by_contra hc
    push Not at hc
    have := E.clock_mono j _ v₀ _ _ hc (E.not_mem_corrupted_of_tick hk₀v.1) (Or.inl hjl) (Or.inl hk₀v.1)
    omega
  have hjk₀ : j ≤ x.firstAt (M.supportCutoff S.C (r * S.C.R)) := by
    by_contra hc
    push Not at hc
    have h1 := R.time_mono hc.le
    have h2 := E.le_time_firstAt (M.supportCutoff S.C (r * S.C.R))
    have : ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (r * S.C.R) : ℕ) : ℝ) := by
      exact_mod_cast (show M.supportCutoff S.C (s₀ + 1 + 1) + Δ S ≤ M.supportCutoff S.C (r * S.C.R) by omega)
    linarith [hjt.2, hSkew]
  have hbnd := CC.bounds_st M F U R Fx (j := j) (w := v₀) (c := M.slotStart S.C (s₀ + 1 - S.C.k - 1))
    hT₁s₀ hk₀v.1 hkj hv₀j hjk₀
    (by
      have : ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) + Δ S ≤ ((aR M S r : ℕ) : ℝ) := by
        exact_mod_cast (show M.supportCutoff S.C (s₀ + 1 + 1) + Δ S ≤ aR M S r by
          unfold aR
          have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show r * S.C.R ≤ r * S.C.R + 1 by omega)
          omega)
      linarith [hjt.2, hSkew])
  have hflv := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_sub_one_le_floor M F) S.C S.P S.X
    (x.tickInput v₀ (M.supportCutoff S.C (s₀ + 1 + 1)))
    ((nodeInv_tickInput_of_tick M F) S A x R E hjl)
  have hfl2 := (hcl2 v₀ hv₀H).2
  have hbnd1 := hbnd.1
  have e1 : x.tickInput v₀ (M.supportCutoff S.C (s₀ + 1 + 1)) = x.st j v₀ := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hjl]
  rw [e1] at hflv hfl2
  refine ⟨B', hB', hBB', hBq', ?_, ?_⟩
  · have h1 : hMax M S.C (x.st j v₀) ≤ (M.chainStateOf S.C B).h + 1 := by
      have h2 := le_trans hflv hfl2
      unfold Height at *
      omega
    exact le_trans hbnd1 h1
  · unfold Height at *
    omega

end GoldilocksCorrectness.Record.Proofs.Executions

