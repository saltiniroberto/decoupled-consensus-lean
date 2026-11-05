module
public import GoldilocksCorrectness.Record.Restated.Proofs.View.Bridges
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.FinalizedSlot
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89ClimbLate
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89CountJUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89QuietJUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89RisingJUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma80UpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ProposalWalkUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89WaitJUpTo
public import GoldilocksCorrectness.Proofs.View.Bridges
public import GoldilocksCorrectness.Proofs.Executions.Lemma89ClimbLate
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma89CountJUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma89QuietJUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma89RisingJUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma80UpTo
public import GoldilocksCorrectness.Proofs.Executions.ProposalWalkUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma89WaitJUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89ClimbLateUpTo, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89ClimbLateUpTo.lean`, over a model
`M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: part B of Lemma 89, the climb's
rising and waiting steps with a later threshold time `T₁`, namely the next proposal after a rising
quiet honest round opening slot and its height, the heights of the quiet honest round opening slot
whose round holds `r * R`, two rising quiet honest round opening slots at different heights, at most
two rising quiet honest round opening slots before the fast round, the next proposal after a waiting
quiet honest round opening slot, and two waiting quiet honest round opening slots at the same height
with the same justified height, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a
bound on the deadlines. The page's routine-level theorems are the facts' fields or have their twins
in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart anchorCW)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_voteTime dutyWindowStart_mono
  dutyWindowStart_of_anchor one_le_Δ proposalWindowStart_eqJ slotStart_eq slotStart_mono
  supportCutoff_eq supportCutoff_lt_of_lt supportCutoff_mono viewFreeze_eq voteTime_eq
  voteTime_mono voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (anchorCW_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Proofs.Executions (r_lt_of_lt_of_mono)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject fgObject
  healFrontSlots)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq ancestorEq_compatible ancestorEq_antisymm ancestorEq_genesis_iff)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

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

The copy with the threshold time `T₁` up to one delay before the start of slot
`rs 0 * R − k − 1`: the landed form asks `T₁` at most the start of
slot `rs 0 * R − 2k`, and the climb takes `T₁` three delays later so that the first honest
attestation above the threshold comes at a round whose slot `r * R + 1` starts at or after the
committee premise's anchor. The proof is unchanged: it reads `hT₁0` only to bound `T₁ + Δ` by
the start of a later slot.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `H₂`: the threshold; `m`: the index of the last honest round opening slot; `i`: the index of an honest round opening slot; `rs`: the rounds of the honest round opening slots;
  `B`: its proposal.

Roots name blocks until `aR M S r`: the climb's context `ClimbCtx` carries the premise at the action
time of round `r`; the honest round opening slots' contexts `QuietCtx` read up to support cutoffs of
slots at most `r * R`, before it.

Restated with the delivery premises up to `aR M S r`: the bound of its roots `hRoots`, the bundle
`ClimbCtxUpTo`'s; the honest round opening slots' bundles `QuietCtxUpTo` read up to support cutoffs
of slots at most `r * R`, before it.

Read aloud: after a rising quiet honest round opening slot `i` with proposal `B`, the next honest
round opening slot's proposer proposes a block `B'` of greater chain-state height, holds it one time
unit after its slot's start, and `B`'s chain-state height is `H₂ − 1` or `H₂`, with the threshold
time `T₁` up to one delay before the start of slot `rs 0 * R − k − 1`, with the delivery premises up
to the action time of round `r`. -/
theorem quiet_rising_next_proposal_late_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ r H₂ m i : ℕ) (rs : ℕ → ℕ)
    (B : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (aR M S r)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (aR M S r))
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
    (hT₁0 : T₁ + Δ S ≤ M.slotStart S.C (rs 0 * S.C.R - S.C.k - 1))
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
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  obtain ⟨hs1, C⟩ := (quietCtx_of_upTo M F U) S A x R GST tGAT tAwakeEnd r m i rs (E.mono ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) hNet hSkew hRedeliver (Sy.mono ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) hΔs
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
  have CC := (ClimbCtxUpTo.of_clock M F U R E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hT₁s hThird hAwake hH₂
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
  have hcl2 := (C.clause2_tick M F R E U Fx) B hB0
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
  have hbnd := CC.bounds_st M F U R E Fx (j := j) (w := v₀) (c := M.slotStart S.C (s₀ + 1 - S.C.k - 1))
    hT₁s₀ hk₀v.1 hkj hv₀j hjk₀
    (by
      have : ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) + Δ S ≤ ((aR M S r : ℕ) : ℝ) := by
        exact_mod_cast (show M.supportCutoff S.C (s₀ + 1 + 1) + Δ S ≤ aR M S r by
          unfold aR
          have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show r * S.C.R ≤ r * S.C.R + 1 by omega)
          omega)
      linarith [hjt.2, hSkew])
    (by
      have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (show s₀ + 1 - S.C.k - 1 ≤ r * S.C.R + 1 by omega)
      have := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (s₀ + 1 - S.C.k - 1)
      unfold aR
      omega)
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

/-- **The quiet honest round opening slot whose round holds `r * R` proposes at height `H₂ − 1` or
`H₂`.** The proof; the audited statement is in `Statements/Executions/Lemma89Statements.lean`.

The route: the context `QuietCtx` with the end `s'' := r * R` (`quietCtx_of`). The
upper bound: were the proposal `B` above `H₂`, `quiet_top_gives_attestation_cutoff` at
`s'' := r * R` gives an honest attestation above `H₂` at a time at most `aR M S (rs i) < aR M S r`,
against `hOld`. The lower bound, as in `quiet_rising_next_proposal_late`: a committee member `v₀` of
slot `rs i * R` honest at the support cutoff of the next slot has `head_height_floor` at most `h(B)`
(the round's second clause) and the greatest chain-state height at least `H₂`
(`ClimbCtx.bounds`), and the greatest chain-state height minus one is at
most its `head_height_floor` (`h_max_sub_one_le_floor`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `H₂`: the threshold; `m`: the last honest round opening slot's index; `i`: the honest round
  opening slot; `rs`: the rounds of the honest round opening slots; `B`: its proposal.

Roots name blocks until `aR M S r`: the climb's context `ClimbCtx` carries the premise at the action
time of round `r`; the honest round opening slots' contexts `QuietCtx` read up to support cutoffs of
slots at most `r * R`, before it.

Restated with the delivery premises up to `aR M S r`: the bound of its roots `hRoots`, the bundle
`ClimbCtxUpTo`'s; the honest round opening slots' bundles `QuietCtxUpTo` read up to support cutoffs
of slots at most `r * R`, before it.

Read aloud: a quiet honest round opening slot before the fast block proposes at one of the two
heights the climb has not left, with the delivery premises up to the action time of round `r`. -/
theorem quiet_straddler_heights_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ r H₂ m i : ℕ) (rs : ℕ → ℕ)
    (B : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (aR M S r)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (aR M S r))
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
    (hT₁0 : T₁ + Δ S ≤ M.slotStart S.C (rs 0 * S.C.R - S.C.k - 1))
    (hi : i < m) (hir : rs i * S.C.R + S.C.R ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening M S A x rs m)
    (hNo : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C (r * S.C.R) → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    (hB : ProposalAt M S x (rs i * S.C.R) B) :
    H₂ ≤ (M.chainStateOf S.C B).h + 1 ∧ (M.chainStateOf S.C B).h ≤ H₂ := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  -- the upper bound
  have hTop : (M.chainStateOf S.C B).h ≤ H₂ := by
    by_contra hgt
    obtain ⟨t₀, v, a, ht₀, hA, ha, hvR⟩ := (quiet_top_gives_attestation_cutoff_upTo_at M F U Fx) S A x R GST tGAT
      tAwakeEnd r m i H₂ (r * S.C.R) rs B (E.mono ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) hNet hSkew hRedeliver (Sy.mono ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) hΔs
      ((roots_cutoff_behind_of_aR M F U) S (by omega) E.ahead_nonneg hSkew hRoots) hParent
      hGST hThird hAwake hActive hCommittees hEnd hSeq hi hir le_rfl hNoCol hNo hB
      (by unfold Height at *; omega) (aR M S r)
        (by unfold aR; exact (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
                (by omega)) hEnd
    obtain ⟨j, hl, hm⟩ := hA
    have hlt : t₀ < aR M S r := by
      have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_lt_of_lt M.toSlotLayout F.sched) S (show rs i * S.C.R + 1 < r * S.C.R + 1 by omega)
      unfold aR at ht₀ ⊢
      omega
    have := hOld j t₀ v a hl (by exact_mod_cast hlt) hvR hm
    exact absurd this (not_le.2 ha)
  -- the lower bound
  obtain ⟨hs1, C⟩ := (quietCtx_of_upTo M F U) S A x R GST tGAT tAwakeEnd r m i rs (E.mono ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) hNet hSkew hRedeliver (Sy.mono ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) hΔs
    ((roots_cutoff_behind_of_aR M F U) S (by omega) E.ahead_nonneg hSkew hRoots) hParent hGST hThird hAwake
    hActive hCommittees hEnd hSeq hi hir le_rfl hNoCol
    hNo
  have hB0 : ProposalAt M S x (rs i * S.C.R - 1 + 1) B := by rw [← hs1]; exact hB
  set s₀ := rs i * S.C.R - 1 with hs₀def
  clear_value s₀
  have hw0 := (C.win M F U) (le_refl (s₀ + 1))
  have h0s : rs 0 * S.C.R ≤ s₀ + 1 := (C.rs0 M F)
  have hT₁s₀ : T₁ + Δ S ≤ M.slotStart S.C (s₀ + 1 - S.C.k - 1) := by
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show rs 0 * S.C.R - S.C.k - 1 ≤ s₀ + 1 - S.C.k - 1 by
      omega)
    have h2 : M.slotStart S.C (rs 0 * S.C.R - 2 * S.C.k + 1) =
        M.slotStart S.C (rs 0 * S.C.R - 2 * S.C.k) + 4 * Δ S := by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
    omega
  have hcl2 := (C.clause2_tick M F R E U Fx) B hB0
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
  have hA0' := E.ahead_nonneg
  have hB0' := E.behind_nonneg
  have hcsR := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
    (show s₀ + 1 + 1 ≤ r * S.C.R by have := C.sR; omega)
  have hssR := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
    (show s₀ + 1 - S.C.k - 1 ≤ r * S.C.R by have := C.sR; omega)
  have htR := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (r * S.C.R)
  -- the climb's bundle at the first step whose real time reaches the support cutoff of slot `r R` (F-P1-13)
  have CC := (ClimbCtxUpTo.of_clock M F U R E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hT₁s hThird hAwake hH₂
    hOld hEnd hTick (by omega))
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
    (le_trans hcsR (C.cut_end M F)) hv₀b
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
  have hbnd := CC.bounds_st M F U R E Fx (j := j) (w := v₀) (c := M.slotStart S.C (s₀ + 1 - S.C.k - 1))
    hT₁s₀ hk₀v.1 hkj hv₀j hjk₀
    (by
      have : ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) + Δ S ≤ ((aR M S r : ℕ) : ℝ) := by
        exact_mod_cast (show M.supportCutoff S.C (s₀ + 1 + 1) + Δ S ≤ aR M S r by
          unfold aR
          have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show r * S.C.R ≤ r * S.C.R + 1 by omega)
          omega)
      linarith [hjt.2, hSkew])
    (by
      have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (show s₀ + 1 - S.C.k - 1 ≤ r * S.C.R + 1 by omega)
      have := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (s₀ + 1 - S.C.k - 1)
      unfold aR
      omega)
  have hflv := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_sub_one_le_floor M F) S.C S.P S.X
    (x.tickInput v₀ (M.supportCutoff S.C (s₀ + 1 + 1)))
    ((nodeInv_tickInput_of_tick M F) S A x R E hjl)
  have hfl2 := (hcl2 v₀ hv₀H).2
  have hbnd1 := hbnd.1
  have e1 : x.tickInput v₀ (M.supportCutoff S.C (s₀ + 1 + 1)) = x.st j v₀ := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hjl]
  rw [e1] at hflv hfl2
  refine ⟨?_, hTop⟩
  have h1 : hMax M S.C (x.st j v₀) ≤ (M.chainStateOf S.C B).h + 1 := by
    have h2 := le_trans hflv hfl2
    unfold Height at *
    omega
  exact le_trans hbnd1 h1

/-- **The chain invariant relative to `B'`, one slot further, with the delivery premises up to `aR M S r`.** The
step of `next_proposal_chain_extends_upTo`, as `next_proposal_chain_step`; each kit call reads the delivery premises
up to its own bound.

The variables:
- as in `next_proposal_chain_extends_upTo`; `σ`: the slot of the step.

Read aloud: in the climb's setting, with the delivery premises up to the bound, when the honest chain extends `B'` at
a slot `σ` from `s''` with `σ + 1 ≤ s₀'`, it extends `B'` at slot `σ + 1`. -/
theorem next_proposal_chain_step_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ r m i i' s'' s₀' s₃ : ℕ)
    (rs : ℕ → ℕ)
    (B' : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (aR M S r)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (aR M S r))
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
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hT₁0 : T₁ + Δ S ≤ M.slotStart S.C (rs 0 * S.C.R - S.C.k - 1))
    (hs''def : s'' = rs (i + 1) * S.C.R) (hs₀'def : s₀' = rs i' * S.C.R - 1)
    (hii' : i < i') (hi' : i' < m) (hri : rs (i + 1) < rs i')
    (hsR' : rs i' * S.C.R + S.C.R ≤ s₃) (hir' : s₃ ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening M S A x rs m)
    -- no change at a step from a validator's own tick to the vote time of slot `s'' − k − 1` to before one of its own
    -- ticks to a clock value at most the support cutoff of slot `s''` (the window before `s''`, read per tick)
    (hNo : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (s'' - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C s'' → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    (hB' : ProposalAt M S x s'' B')
    -- read at every tick of a validator outside the adversary set to a clock value `c` from the vote time of slot
    -- `s''` to the support cutoff of slot `s₀' + 1`, on the state that tick starts from (rule R3)
    (hFl : ∀ (u : V) (c k : ℕ), M.voteTime S.C s'' ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl k = Event.tick u c → u ∉ A.corrupted k → u ∉ A.corruptedAtTime x (x.time k + Δ S) →
      M.head_height_floor (x.tickInput u c) ≤ (M.chainStateOf S.C B').h)
    (hRootB' : ∀ (u : V) (c k : ℕ), M.voteTime S.C s'' ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl k = Event.tick u c → u ∉ A.corrupted k → u ∉ A.corruptedAtTime x (x.time k + Δ S) → B' ∈ (x.tickInput u c).tree →
      (M.get_fc_root (x.tickInput u c)).AncestorEq B')
    (hDel : ∀ (u : V) (c k : ℕ), M.voteTime S.C s'' ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl k = Event.tick u c → u ∉ A.corrupted k → u ∉ A.corruptedAtTime x (x.time k + Δ S) → B' ∈ (x.tickInput u c).tree)
    -- the finalized block at every tick of a validator outside the adversary set at that tick alone
    (hFin : ∀ (u : V) (c k : ℕ), M.voteTime S.C s'' ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl k = Event.tick u c → u ∉ A.corrupted k → (x.tickInput u c).finalized.compatible B' = true) :
    ∀ σ, s'' ≤ σ → σ + 1 ≤ s₀' → HonestChainExtends M S A x (Hon M S A x σ) B' σ →
      HonestChainExtends M S A x (Hon M S A x (σ + 1)) B' (σ + 1) := by
  subst hs₀'def
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hmono := r_lt_of_lt_of_mono rs m hSeq.mono
  have hgap : rs (i + 1) * S.C.R + S.C.R ≤ rs i' * S.C.R := by
    have h' : (rs (i + 1) + 1) * S.C.R ≤ rs i' * S.C.R := Nat.mul_le_mul_right _ hri
    rw [Nat.add_mul, Nat.one_mul] at h'
    exact h'
  have h0s : rs 0 * S.C.R ≤ rs (i + 1) * S.C.R :=
    Nat.mul_le_mul_right _ (le_of_lt (hmono 0 (i + 1) (by omega) (by omega)))
  obtain ⟨h2k, hAnc⟩ := (window_after_anchor M F U) S A x rs m tGAT tAwakeEnd (rs (i + 1) * S.C.R) hSeq h0s
  rw [← hs''def] at hAnc h2k hgap
  have hBΔ : ΔClockBehind < Δ S := by linarith
  have hAΔ : ΔClockAhead < Δ S := by linarith
  have hanc := anchorCW_eq S tGAT
  have hAnc' := hAnc
  rw [hanc, Nat.mul_add] at hAnc'
  have hk4 := Nat.mul_le_mul_left (4 * Δ S) S.C.k_ge_two
  have hΔs' : Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have hm : ((Δs : ℕ) : ℝ) ≤ max ((Δ S : ℕ) : ℝ) ((Δs : ℕ) : ℝ) := le_max_right _ _
    exact_mod_cast (show ((Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) by push_cast; linarith)
  have hmx1 : max (Δ S) Δs ≤ 4 * Δ S * S.C.k := by
    rcases max_choice (Δ S) Δs with h | h <;> rw [h] <;> omega
  have hss := fun a b (h : a ≤ b) => (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S h
  have hscm := fun a b (h : a ≤ b) => (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h
  have hte := fun a => (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S a
  -- the slots `σ` from `s''` to `rs i' * R - 1`, and their times
  have hAσ : ∀ σ, s'' ≤ σ → anchorCW S tGAT ≤ M.slotStart S.C (σ + 1) := fun σ hσ =>
    le_trans hAnc (hss _ _ (by omega))
  have hdwσ : ∀ σ, s'' ≤ σ → tGAT + Δ S ≤ M.dutyWindowStart S.C σ := fun σ hσ =>
    (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT σ (hAσ σ hσ)
  have hcEσ : ∀ σ, σ ≤ rs i' * S.C.R → M.supportCutoff S.C σ ≤ tAwakeEnd := fun σ hσ =>
    le_trans (hscm σ (r * S.C.R + 1) (by omega)) hEnd
  have hcRσ : ∀ σ, σ ≤ rs i' * S.C.R → M.supportCutoff S.C σ ≤ aR M S r := fun σ hσ => hscm σ (r * S.C.R + 1) (by omega)
  -- the members of a slot: active from `tGAT` to its update, honest active and updaters
  have hMemA : ∀ σ, s'' ≤ σ → σ + 1 ≤ rs i' * S.C.R → ∀ v ∈ Hon M S A x σ,
      v ∈ A.activeThroughout x tGAT (M.supportCutoff S.C (σ + 1)) := fun σ h1 h2 v hv =>
    (mem_activeThroughout_of_hAwake_honest_at M F) R E hAwake le_rfl (hcEσ _ h2) (Finset.mem_sdiff.1 hv).2
  have hMemH : ∀ σ, s'' ≤ σ → σ + 1 ≤ rs i' * S.C.R → ∀ v ∈ Hon M S A x σ,
      v ∈ honestActiveAt M S A x σ ∧ v ∈ updaterAt M S A x σ := fun σ h1 h2 v hv =>
    hActive σ (by have := hdwσ σ h1; omega) (hcEσ _ h2) v (Finset.mem_sdiff.1 hv).2
  -- a member ticks to every clock value `c` with `c + ΔClockBehind` at most its update's real time
  have hTickOf : ∀ σ, s'' ≤ σ → σ + 1 ≤ rs i' * S.C.R → ∀ v ∈ Hon M S A x σ, ∀ c : ℕ, 1 ≤ c →
      tGAT + Δ S ≤ c → c + Δ S ≤ M.supportCutoff S.C (σ + 1) →
      ∃ k : ℕ, x.lbl k = Event.tick v c ∧ x.clockValue k v < c := by
    intro σ h1 h2 v hv c hc1 hc2 hc3
    have hvA := hMemA σ h1 h2 v hv
    have hc2R : ((tGAT : ℕ) : ℝ) + Δ S ≤ (c : ℝ) := by exact_mod_cast hc2
    have hc3R : (c : ℝ) + Δ S ≤ ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) := by exact_mod_cast hc3
    have hact : ∀ j : ℕ, (c : ℝ) - ΔClockAhead ≤ x.time j → x.time j ≤ (c : ℝ) + ΔClockBehind → v ∈ A.active j :=
      fun j h1' h2' => Activity.mem_activeThroughout.1 hvA j (by linarith)
        (by linarith [htime (Nat.le_succ j)])
    obtain ⟨k, hk, -, hk2⟩ := E.tick_of_active c hc1 v hact
    refine ⟨k, hk, (clockValue_lt_of_tick_of_active M F) E hk (by omega) (fun j h1' h2' => ?_)⟩
    exact Activity.mem_activeThroughout.1 hvA j (by linarith [htime h2'])
      (by linarith [htime (Nat.le_succ j)])
  -- the members' votes of slot `σ`
  have hVotes : ∀ σ, s'' ≤ σ → σ + 1 ≤ rs i' * S.C.R → ∀ u ∈ S.P.committee σ ∩ Hon M S A x σ,
      u ∈ Hon M S A x σ ∧ u ∈ S.P.committee σ ∧
        ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = σ ∧
          ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C σ) ∧
            (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i := by
    intro σ h1 h2 u hu
    obtain ⟨hK, huH⟩ := Finset.mem_inter.1 hu
    obtain ⟨k', hl, hAw⟩ := (tick_and_wake_of_tick_window M F U) S A x R σ u E
      ((voteTime_tick_window_of_honestActiveAt M F U) S A x R σ u E hSkew (hMemH σ h1 h2 u huH).1)
    obtain ⟨vote, hvi, hvs, hsent⟩ := (honest_votes_of_window M F U) S A x R σ u E hl hAw hK
    exact ⟨huH, hK, vote, hvi, hvs, k', hl, hsent⟩
  intro σ h1 hσ2
  have h2 : σ + 1 + 1 ≤ rs i' * S.C.R := by clear * - hσ2; omega
  obtain ⟨hvS, hcS, -, hsS, -⟩ := hte s''
  obtain ⟨-, hcS1, -, -, -⟩ := hte (s'' + 1)
  obtain ⟨hv0, hc0, hf0, hs0, -⟩ := hte σ
  obtain ⟨hv1, hc1, hf1, hs1, -⟩ := hte (σ + 1)
  obtain ⟨-, hc2, -, -, -⟩ := hte (σ + 1 + 1)
  have hssσ := hss s'' σ h1
  have hTop : M.supportCutoff S.C (σ + 1 + 1) ≤ M.supportCutoff S.C (rs i' * S.C.R - 1 + 1) := hscm _ _ (by clear * - h2; omega)
  -- `StepFrameAt` relative to `B'` at the members of slot `σ + 1`; the clock values it reads
  have hdw := hdwσ s'' le_rfl
  have hdv := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_le_voteTime M.toSlotLayout F.sched) S s''
  have hdw1 := hdwσ (σ + 1) (by clear * - h1; omega)
  have hdv1 := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_le_voteTime M.toSlotLayout F.sched) S (σ + 1)
  have ha1 : 1 ≤ M.voteTime S.C s'' := by clear * - hvS hΔ; omega
  have ha2 : tGAT + Δ S ≤ M.voteTime S.C s'' := by clear * - hdw hdv; omega
  have ha3 : M.voteTime S.C s'' + Δ S ≤ M.supportCutoff S.C (s'' + 1) := by clear * - hvS hcS1 hsS; omega
  have ha4 : s'' + 1 ≤ rs i' * S.C.R := by clear * - hgap hR; omega
  have hb1 : 1 ≤ M.voteTime S.C (σ + 1) := by clear * - hv1 hΔ; omega
  have hb2 : tGAT + Δ S ≤ M.voteTime S.C (σ + 1) := by clear * - hdw1 hdv1; omega
  have hb3 : M.voteTime S.C (σ + 1) + Δ S ≤ M.supportCutoff S.C (σ + 1 + 1) := by clear * - hv1 hc2 hs1; omega
  have hb4 : s'' ≤ σ + 1 := by clear * - h1; omega
  have hb5 : s'' + 1 ≤ σ + 1 + 1 := by clear * - h1; omega
  have hcv0 : M.voteTime S.C s'' ≤ M.voteTime S.C (σ + 1) := by clear * - hvS hv1 hssσ hs0; omega
  have hcv1 : M.voteTime S.C (σ + 1) ≤ M.supportCutoff S.C (rs i' * S.C.R - 1 + 1) := by clear * - hv1 hc2 hs1 hTop; omega
  have hcs0 : M.voteTime S.C s'' ≤ M.supportCutoff S.C (σ + 1 + 1) := by clear * - hvS hssσ hs0 hc2 hs1; omega
  have hcs1 : M.supportCutoff S.C (σ + 1 + 1) ≤ M.supportCutoff S.C (rs i' * S.C.R - 1 + 1) := hTop
  have hcf : M.voteTime S.C s'' ≤ M.viewFreeze S.C σ := by clear * - hvS hssσ hf0; omega
  have hmS := (roundMembers_mono M F S A (s'' + 1) (σ + 1 + 1) tAwakeEnd R E hb5 (hcEσ _ h2)).1
  have hSF : ∀ w ∈ Hon M S A x (σ + 1), StepFrameAt M S A x B' σ w := by
    intro w hw
    have hwσ'' : w ∈ Hon M S A x s'' := hmS hw
    obtain ⟨k, hk, hlt⟩ := hTickOf s'' le_rfl ha4 w hwσ'' (M.voteTime S.C s'') ha1 ha2 ha3
    obtain ⟨kv, hkv, -⟩ := hTickOf (σ + 1) hb4 h2 w hw (M.voteTime S.C (σ + 1)) hb1 hb2 hb3
    obtain ⟨k2, hk2, -⟩ := Activity.mem_activeThroughoutToTick.1 (hMemH (σ + 1) hb4 h2 w hw).2
    have hkkv : k ≤ kv := (tick_step_le_of_le M F) E hk hkv hcv0
    have hwk := E.not_mem_corrupted_of_tick hk
    have hwkv := E.not_mem_corrupted_of_tick hkv
    have hwk2 := E.not_mem_corrupted_of_tick hk2
    have hk2' : x.lbl k2 = Event.tick w (M.supportCutoff S.C (σ + 1 + 1)) := hk2
    -- `w` is outside the adversary set one delay after its two vote-time ticks: its membership
    have hwH : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 1 + 1)) := (Finset.mem_sdiff.1 hw).2
    have hwkΔ : w ∉ A.corruptedAtTime x (x.time k + Δ S) :=
      Activity.not_mem_corruptedAtTime.2 fun i hi =>
        (Activity.not_mem_corruptedAtTime.1 hwH) i (le_trans hi (by
          have h1 := (E.tick_active k w _ hk).2.2
          have h2 : ((M.voteTime S.C s'' : ℕ) : ℝ) + Δ S + Δ S ≤ ((M.supportCutoff S.C (σ + 1 + 1) : ℕ) : ℝ) := by
            exact_mod_cast (show M.voteTime S.C s'' + Δ S + Δ S ≤ M.supportCutoff S.C (σ + 1 + 1) by
              clear * - hvS hssσ hs0 hc2 hs1 hΔ hcs0 hcv0 hv1 hb3; omega)
          have h3 := E.ahead_nonneg
          linarith [hSkew]))
    have hwkvΔ : w ∉ A.corruptedAtTime x (x.time kv + Δ S) :=
      Activity.not_mem_corruptedAtTime.2 fun i hi =>
        (Activity.not_mem_corruptedAtTime.1 hwH) i (le_trans hi (by
          have h1 := (E.tick_active kv w _ hkv).2.2
          have h2 : ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) + Δ S + Δ S ≤ ((M.supportCutoff S.C (σ + 1 + 1) : ℕ) : ℝ) := by
            exact_mod_cast (show M.voteTime S.C (σ + 1) + Δ S + Δ S ≤ M.supportCutoff S.C (σ + 1 + 1) by
              clear * - hv1 hc2 hs1 hb3 hΔ; omega)
          have h3 := E.ahead_nonneg
          linarith [hSkew]))
    exact (stepFrame_of_compat_fin M F U) S A x R E B' B' σ w (ancestorEq_refl B') hk hlt hcf
      (hDel w _ k le_rfl (le_trans hcs0 hcs1) hk hwk hwkΔ) hkv hkkv
      ((compatible_iff _ _).2 (Or.inl (hRootB' w _ kv hcv0 hcv1 hkv hwkv hwkvΔ (hDel w _ kv hcv0 hcv1 hkv hwkv hwkvΔ))))
      (hFl w _ kv hcv0 hcv1 hkv hwkv hwkvΔ)
      (hFin w _ k2 hcs0 hcs1 hk2' hwk2)
  have hGsn : GST + max (Δ S) Δs ≤ M.supportCutoff S.C σ := by
    have := hss (s'' - 2 * S.C.k + 1) σ (by clear * - h1 hk h2k; omega)
    clear * - this hc0 hAnc' hGST hmx1
    omega
  have hRT : ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) + ΔClockBehind ≤ ((aR M S r : ℕ) : ℝ) := by
    have : ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) + Δ S ≤ ((aR M S r : ℕ) : ℝ) := by
      exact_mod_cast (show M.supportCutoff S.C (σ + 1) + Δ S ≤ aR M S r by
        have := hcRσ (σ + 1 + 1) h2
        clear * - this hc1 hs1 hc2
        omega)
    linarith
  have hMaj0 := (committee_majority_of_committeeSleepiness M F) S A x _ σ hCommittees (hAσ σ h1)
    (hcEσ _ (by clear * - h2; omega))
  have hMaj1 := (committee_majority_of_committeeSleepiness M F) S A x _ (σ + 1) hCommittees (hAσ (σ + 1) (by clear * - h1; omega))
    (hcEσ _ h2)
  intro ihn
  have hcR1 : M.supportCutoff S.C (σ + 1) ≤ aR M S r := hcRσ _ (by clear * - h2; omega)
  exact (lem79_step_sets_upTo M F U) S A x R GST σ (Hon M S A x σ) (Hon M S A x (σ + 1))
    (fun s => S.P.committee s ∩ Hon M S A x s) B' (E.mono hcR1) hNet hSkew hRedeliver (Sy.mono hcR1) hΔs
    ((per_tick_roots_of_roots_until M F) x E hRoots hRT) hParent
    (votesCastByOwner_of_unforgeability M F S A x R E) hGsn ihn
    (roundMembers_mono M F S A (σ + 1) (σ + 1 + 1) tAwakeEnd R E (Nat.le_succ _) (hcEσ _ h2)).1
    (fun v hv => (hMemH σ h1 (by clear * - h2; omega) v hv).2)
    (fun v hv => by
      --: the member's reader to its tick to the vote time of slot `σ + 1`, from its window from `tGAT`
      have hd := hdwσ (σ + 1) (by clear * - h1; omega)
      have hΔ1 := one_le_Δ S
      have hdr := (duty_window_start_real_of_pos M F U) S (σ + 1) (by clear * - hd hΔ1; omega)
      have hA0 := E.ahead_nonneg
      have hB0 := E.behind_nonneg
      have hdR : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((M.dutyWindowStart S.C (σ + 1) : ℕ) : ℝ) := by exact_mod_cast hd
      push_cast at hdR
      have hle : duty_window_start S.C (σ + 1) ≤ ((M.voteTime S.C (σ + 1) : ℕ) : ℤ) :=
        le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_le_dutyWindowStart M.toSlotLayout F.sched U) S (σ + 1))
          (by exact_mod_cast (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_le_voteTime M.toSlotLayout F.sched) S (σ + 1))
      have hve : ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (σ + 1 + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show M.voteTime S.C (σ + 1) + Δ S ≤ M.supportCutoff S.C (σ + 1 + 1) by clear * - hv1 hc2 hs1; omega)
      refine (mem_activeThroughoutToTick_of_mem_activeThroughout M F) x R E (by clear * - hv1 hΔ1; omega) hle ?_
      refine Activity.mem_activeThroughout_of_le ?_ ?_ (hMemA (σ + 1) hb4 h2 v hv)
      · rw [hdr]; linarith
      · linarith)
    (fun v hv => (hMemH (σ + 1) hb4 h2 v hv).2)
    (fun u hu hX => (Finset.mem_sdiff.1 (hMemH (σ + 1) hb4 h2 u hu).1).2 (Finset.mem_union_right _ hX))
    (hVotes σ h1 (by clear * - h2; omega)) (hVotes (σ + 1) hb4 h2)
    (fun w _ => ((counting_of_committee_majority_st M F) S A x R E σ (x.tickStep w (M.voteTime S.C (σ + 1)))
      (Hon M S A x σ) w hMaj0).2.2)
    (fun v _ => ((counting_of_committee_majority_st M F) S A x R E (σ + 1)
      (x.tickStep v (M.supportCutoff S.C (σ + 1 + 1))) (Hon M S A x (σ + 1)) v hMaj1).2.1)
    (fun w hw => (hSF w hw).1) (fun w hw => (hSF w hw).2.1) (fun w hw => (hSF w hw).2.2)


/-- **The chain invariant relative to the proposal at an honest round opening slot, up to the slot before a
later one, with the delivery premises up to the action time of round `r`.** The first part shared by `quiet_rising_heights_differ_cutoff_upTo` and
`quiet_waiting_same_entry_cutoff_upTo`: the round's base at the slot `s''` of `B'` (`WinCtxUpTo.base`) makes
the honest votes of that slot extend `B'`, and `lem79_step_sets_upTo` carries the chain invariant
relative to `B'` slot by slot. Each caller proves the three facts on `B'` (`hFl`, `hRootB'`, `hDel`) its
own way.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `m`: the index of the last honest round opening slot; `i < i'`: the indices of two honest round
  opening slots; `rs`: the rounds of the honest round opening slots;
- `s''`: the honest round opening slot `rs (i + 1) * R`; `s₀'`: the slot before the later honest
  round opening slot `rs i' * R`; `s₃`: the slot up to whose support cutoff no honest validator's
  fork choice changes after the later one;
- `B'`: the proposal at `s''`.

Read aloud: in the climb's setting, let `B'` be the proposal at the honest round opening slot
`s'' = rs (i + 1) * R`, and `rs i' * R` a later honest round opening slot. Suppose that every tick of a validator outside the adversary set, to a clock value from the vote time
of slot `s''` up to the support cutoff of slot `rs i' * R`, starts from a state that holds `B'`, has
`head_height_floor` (the least chain-state height a viable block may have) at most `B'`'s chain-state
height, and has an fgroot that is `B'` or an ancestor of `B'`. Then at every slot
from `s''` to the slot `s₀'` before `rs i' * R`, the votes of the validators honest at that slot's
update extend `B'`, their live locks do not conflict with `B'`, and their saved confirmations extend
`B'`. -/
theorem next_proposal_chain_extends_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ r m i i' s'' s₀' s₃ : ℕ)
    (rs : ℕ → ℕ)
    (B' : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (aR M S r)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (aR M S r))
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
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hT₁0 : T₁ + Δ S ≤ M.slotStart S.C (rs 0 * S.C.R - S.C.k - 1))
    (hs''def : s'' = rs (i + 1) * S.C.R) (hs₀'def : s₀' = rs i' * S.C.R - 1)
    (hii' : i < i') (hi' : i' < m) (hri : rs (i + 1) < rs i')
    (hsR' : rs i' * S.C.R + S.C.R ≤ s₃) (hir' : s₃ ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening M S A x rs m)
    -- no change at a step from a validator's own tick to the vote time of slot `s'' − k − 1` to before one of its own
    -- ticks to a clock value at most the support cutoff of slot `s''` (the window before `s''`, read per tick)
    (hNo : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (s'' - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C s'' → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    (hB' : ProposalAt M S x s'' B')
    -- read at every tick of a validator outside the adversary set to a clock value `c` from the vote time of slot
    -- `s''` to the support cutoff of slot `s₀' + 1`, on the state that tick starts from (rule R3)
    (hFl : ∀ (u : V) (c k : ℕ), M.voteTime S.C s'' ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl k = Event.tick u c → u ∉ A.corrupted k → u ∉ A.corruptedAtTime x (x.time k + Δ S) →
      M.head_height_floor (x.tickInput u c) ≤ (M.chainStateOf S.C B').h)
    (hRootB' : ∀ (u : V) (c k : ℕ), M.voteTime S.C s'' ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl k = Event.tick u c → u ∉ A.corrupted k → u ∉ A.corruptedAtTime x (x.time k + Δ S) → B' ∈ (x.tickInput u c).tree →
      (M.get_fc_root (x.tickInput u c)).AncestorEq B')
    (hDel : ∀ (u : V) (c k : ℕ), M.voteTime S.C s'' ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl k = Event.tick u c → u ∉ A.corrupted k → u ∉ A.corruptedAtTime x (x.time k + Δ S) → B' ∈ (x.tickInput u c).tree)
    -- the finalized block at every tick of a validator outside the adversary set at that tick alone
    (hFin : ∀ (u : V) (c k : ℕ), M.voteTime S.C s'' ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl k = Event.tick u c → u ∉ A.corrupted k → (x.tickInput u c).finalized.compatible B' = true) :
    ∀ n, s'' + n ≤ s₀' →
      HonestChainExtends M S A x (Hon M S A x (s'' + n)) B' (s'' + n) := by
  subst hs₀'def
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hmono := r_lt_of_lt_of_mono rs m hSeq.mono
  have hgap : rs (i + 1) * S.C.R + S.C.R ≤ rs i' * S.C.R := by
    have h' : (rs (i + 1) + 1) * S.C.R ≤ rs i' * S.C.R := Nat.mul_le_mul_right _ hri
    rw [Nat.add_mul, Nat.one_mul] at h'
    exact h'
  have h0s : rs 0 * S.C.R ≤ rs (i + 1) * S.C.R :=
    Nat.mul_le_mul_right _ (le_of_lt (hmono 0 (i + 1) (by omega) (by omega)))
  obtain ⟨h2k, hAnc⟩ := (window_after_anchor M F U) S A x rs m tGAT tAwakeEnd (rs (i + 1) * S.C.R) hSeq h0s
  rw [← hs''def] at hAnc h2k hgap
  have hBΔ : ΔClockBehind < Δ S := by linarith
  have hAΔ : ΔClockAhead < Δ S := by linarith
  have hanc := anchorCW_eq S tGAT
  have hAnc' := hAnc
  rw [hanc, Nat.mul_add] at hAnc'
  have hk4 := Nat.mul_le_mul_left (4 * Δ S) S.C.k_ge_two
  have hΔs' : Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have hm : ((Δs : ℕ) : ℝ) ≤ max ((Δ S : ℕ) : ℝ) ((Δs : ℕ) : ℝ) := le_max_right _ _
    exact_mod_cast (show ((Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) by push_cast; linarith)
  have hmx1 : max (Δ S) Δs ≤ 4 * Δ S * S.C.k := by
    rcases max_choice (Δ S) Δs with h | h <;> rw [h] <;> omega
  have hss := fun a b (h : a ≤ b) => (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S h
  have hscm := fun a b (h : a ≤ b) => (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h
  have hte := fun a => (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S a
  -- the slots `σ` from `s''` to `rs i' * R - 1`, and their times
  have hAσ : ∀ σ, s'' ≤ σ → anchorCW S tGAT ≤ M.slotStart S.C (σ + 1) := fun σ hσ =>
    le_trans hAnc (hss _ _ (by omega))
  have hdwσ : ∀ σ, s'' ≤ σ → tGAT + Δ S ≤ M.dutyWindowStart S.C σ := fun σ hσ =>
    (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT σ (hAσ σ hσ)
  have hcEσ : ∀ σ, σ ≤ rs i' * S.C.R → M.supportCutoff S.C σ ≤ tAwakeEnd := fun σ hσ =>
    le_trans (hscm σ (r * S.C.R + 1) (by omega)) hEnd
  have hcRσ : ∀ σ, σ ≤ rs i' * S.C.R → M.supportCutoff S.C σ ≤ aR M S r := fun σ hσ => hscm σ (r * S.C.R + 1) (by omega)
  -- the members of a slot: active from `tGAT` to its update, honest active and updaters
  have hMemA : ∀ σ, s'' ≤ σ → σ + 1 ≤ rs i' * S.C.R → ∀ v ∈ Hon M S A x σ,
      v ∈ A.activeThroughout x tGAT (M.supportCutoff S.C (σ + 1)) := fun σ h1 h2 v hv =>
    (mem_activeThroughout_of_hAwake_honest_at M F) R E hAwake le_rfl (hcEσ _ h2) (Finset.mem_sdiff.1 hv).2
  have hMemH : ∀ σ, s'' ≤ σ → σ + 1 ≤ rs i' * S.C.R → ∀ v ∈ Hon M S A x σ,
      v ∈ honestActiveAt M S A x σ ∧ v ∈ updaterAt M S A x σ := fun σ h1 h2 v hv =>
    hActive σ (by have := hdwσ σ h1; omega) (hcEσ _ h2) v (Finset.mem_sdiff.1 hv).2
  -- a member ticks to every clock value `c` with `c + ΔClockBehind` at most its update's real time
  have hTickOf : ∀ σ, s'' ≤ σ → σ + 1 ≤ rs i' * S.C.R → ∀ v ∈ Hon M S A x σ, ∀ c : ℕ, 1 ≤ c →
      tGAT + Δ S ≤ c → c + Δ S ≤ M.supportCutoff S.C (σ + 1) →
      ∃ k : ℕ, x.lbl k = Event.tick v c ∧ x.clockValue k v < c := by
    intro σ h1 h2 v hv c hc1 hc2 hc3
    have hvA := hMemA σ h1 h2 v hv
    have hc2R : ((tGAT : ℕ) : ℝ) + Δ S ≤ (c : ℝ) := by exact_mod_cast hc2
    have hc3R : (c : ℝ) + Δ S ≤ ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) := by exact_mod_cast hc3
    have hact : ∀ j : ℕ, (c : ℝ) - ΔClockAhead ≤ x.time j → x.time j ≤ (c : ℝ) + ΔClockBehind → v ∈ A.active j :=
      fun j h1' h2' => Activity.mem_activeThroughout.1 hvA j (by linarith)
        (by linarith [htime (Nat.le_succ j)])
    obtain ⟨k, hk, -, hk2⟩ := E.tick_of_active c hc1 v hact
    refine ⟨k, hk, (clockValue_lt_of_tick_of_active M F) E hk (by omega) (fun j h1' h2' => ?_)⟩
    exact Activity.mem_activeThroughout.1 hvA j (by linarith [htime h2'])
      (by linarith [htime (Nat.le_succ j)])
  -- the members' votes of slot `σ`
  have hVotes : ∀ σ, s'' ≤ σ → σ + 1 ≤ rs i' * S.C.R → ∀ u ∈ S.P.committee σ ∩ Hon M S A x σ,
      u ∈ Hon M S A x σ ∧ u ∈ S.P.committee σ ∧
        ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = σ ∧
          ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C σ) ∧
            (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i := by
    intro σ h1 h2 u hu
    obtain ⟨hK, huH⟩ := Finset.mem_inter.1 hu
    obtain ⟨k', hl, hAw⟩ := (tick_and_wake_of_tick_window M F U) S A x R σ u E
      ((voteTime_tick_window_of_honestActiveAt M F U) S A x R σ u E hSkew (hMemH σ h1 h2 u huH).1)
    obtain ⟨vote, hvi, hvs, hsent⟩ := (honest_votes_of_window M F U) S A x R σ u E hl hAw hK
    exact ⟨huH, hK, vote, hvi, hvs, k', hl, hsent⟩
  -- the round's base at `B'`'s slot
  have hW1 : M.supportCutoff S.C (s'' - 1 + 1 + 1) ≤ aR M S r :=
    le_trans (hscm _ _ (show s'' - 1 + 1 + 1 ≤ rs i' * S.C.R by omega)) (hcRσ _ le_rfl)
  have W1 : WinCtxUpTo M S A x GST tGAT tAwakeEnd r m (i + 1) rs (s'' - 1) Δs (releaseOf M S.C) ΔRedeliver
      ΔClockAhead ΔClockBehind ΔNet := by
    refine ⟨E.mono hW1, hNet, hSkew, hRedeliver, Sy.mono hW1, hΔs,
      (roots_cutoff_behind_of_aR M F U) S (show s'' - 1 + 1 + 1 ≤ r * S.C.R by omega) E.ahead_nonneg hSkew hRoots,
      hParent, hGST, hThird, hAwake, hActive, hCommittees, hEnd, hSeq, by omega, by omega, by omega, ?_⟩
    rw [show s'' - 1 + 1 = s'' by omega]
    exact hNo
  have hB'P : ProposalAt M S x (s'' - 1 + 1) B' := by
    rw [show s'' - 1 + 1 = s'' by omega]
    exact hB'
  obtain ⟨hvS, hcS, -, hsS, -⟩ := hte s''
  obtain ⟨-, hcS1, -, -, -⟩ := hte (s'' + 1)
  obtain ⟨-, hBase', -⟩ := (W1.base M F R E U Fx) hNoCol B' hB'P (by
    intro v hv
    rw [show s'' - 1 + 1 = s'' by omega] at hv ⊢
    obtain ⟨k2, hk2, -⟩ := Activity.mem_activeThroughoutToTick.1 (hMemH s'' le_rfl (by omega) v hv).2
    have hv2 := E.not_mem_corrupted_of_tick hk2
    have hc1 : M.voteTime S.C s'' ≤ M.supportCutoff S.C (s'' + 1) := by omega
    have hc2 : M.supportCutoff S.C (s'' + 1) ≤ M.supportCutoff S.C (rs i' * S.C.R - 1 + 1) :=
      hscm _ _ (by omega)
    -- (B): the member's finalized block at its update tick is compatible with `B'` (`hFin`) and its clock value
    -- there is less than the support cutoff of slot `s'' + 1`, the slot after `B'`'s, so it is `B'` or an ancestor of `B'`
    have hT2 : x.tickInput v (M.supportCutoff S.C (s'' + 1)) = x.st k2 v := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hk2]
    obtain ⟨τ, hτ, -⟩ := (tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E
      (hMemH s'' le_rfl (by omega) v hv).2
      ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_lt_supportCutoff M.toSlotLayout F.sched U) S
        (s'' + 1))
    rw [hT2] at hτ
    have hclk0 := (clockValue_lt_of_tick_awakeSince_some M F) R E hk2
      ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot M.toSlotLayout F.sched) S s'').2 hτ
    obtain ⟨iP', hlP', hsentP'⟩ := id hB'P
    have hB'sl := ((proposal_parent_walk_end M F U) S A x R E (s'' - 1) iP' B' _ hlP' hsentP').1
    have hTk2 : x.time k2 ≤ ((aR M S r : ℕ) : ℝ) := by
      have h1 := (E.tick_active k2 v _ hk2).2.2
      have h2 : ((M.supportCutoff S.C (s'' + 1) : ℕ) : ℝ) + Δ S ≤ ((aR M S r : ℕ) : ℝ) := by
        exact_mod_cast (show M.supportCutoff S.C (s'' + 1) + Δ S ≤ aR M S r by
          unfold aR
          have := hscm _ _ (show s'' + 1 + 1 ≤ r * S.C.R + 1 by omega)
          have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S (s'' + 1)
          omega)
      linarith [hSkew, E.ahead_nonneg]
    have hTE : x.time k2 ≤ ((tAwakeEnd : ℕ) : ℝ) := le_trans hTk2 (by exact_mod_cast hEnd)
    rw [hT2]
    exact (finalized_ancestorEq_of_compatible_of_clock_le M F U Fx) S A x R E k2 v B'
      (((fewerThanQuorum_of_fewerThanThird M F) A x tAwakeEnd hThird).mono hTE)
      ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hTk2 hRoots) hv2
      (by rw [hB'sl, show s'' - 1 + 1 = s'' by omega]; exact hclk0.le)
      (by rw [← hT2]; exact hFin v _ k2 hc1 hc2 hk2 hv2))
  rw [show s'' - 1 + 1 = s'' by omega] at hBase'
  -- the chain invariant relative to `B'`, carried slot by slot
  intro n
  induction n with
  | zero => intro _; simpa using hBase'
  | succ n ih =>
    intro hn
    rw [show s'' + (n + 1) = s'' + n + 1 by omega]
    exact (next_proposal_chain_step_upTo M F U Fx) S A x R GST tGAT tAwakeEnd T₁ r m i i' s'' (rs i' * S.C.R - 1) s₃ rs B'
      E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hT₁s hTick hThird hAwake hActive hCommittees hEnd hSeq hT₁0
      hs''def rfl hii' hi' hri hsR' hir' hNoCol hNo hB' hFl hRootB' hDel hFin (s'' + n) (by omega) (by omega) (ih (by omega))

/-- **The proposal at an honest round opening slot is an ancestor of a later one's parent, with the delivery premises up to the action time of round `r`.**
The second part shared by `quiet_rising_heights_differ_cutoff_upTo` and
`quiet_waiting_same_entry_cutoff_upTo`: with the chain invariant relative to `B'` carried to the slot `s₀'`
(`next_proposal_chain_extends_upTo`), the later proposer's anchor is on `B'`'s chain or comparable with it, so `B'`
is an ancestor of `B₂`'s parent (`proposal_parent_extends_majority_block_upTo`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `m`: the index of the last honest round opening slot; `i < i'`: the indices of two honest round
  opening slots; `rs`: the rounds of the honest round opening slots;
- `s''`: the honest round opening slot `rs (i + 1) * R`; `s₀'`: the slot before the later honest
  round opening slot `rs i' * R`; `s₃`: the slot up to whose support cutoff no honest validator's
  fork choice changes after the later one;
- `B'`: the proposal at `s''`; `B₂`: the proposal at the later honest round opening slot.

Read aloud: in the climb's setting, let `B'` be the proposal at the honest round opening slot
`s'' = rs (i + 1) * R` and `B₂` the proposal at a later honest round opening slot `rs i' * R`. Suppose that every tick of a validator outside the adversary set, to a clock value from the vote time
of slot `s''` up to the support cutoff of slot `rs i' * R`, starts from a state that holds `B'`, has
`head_height_floor` (the least chain-state height a viable block may have) at most `B'`'s chain-state
height, and has an fgroot that is `B'` or an ancestor of `B'`.
Then `B'` is `B₂`'s parent or an ancestor of it. -/
theorem next_proposal_ancestorEq_later_parent_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ r m i i' s'' s₀' s₃ : ℕ)
    (rs : ℕ → ℕ)
    (B' B₂ : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (aR M S r)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (aR M S r))
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
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hT₁0 : T₁ + Δ S ≤ M.slotStart S.C (rs 0 * S.C.R - S.C.k - 1))
    (hs''def : s'' = rs (i + 1) * S.C.R) (hs₀'def : s₀' = rs i' * S.C.R - 1)
    (hii' : i < i') (hi' : i' < m) (hri : rs (i + 1) < rs i')
    (hsR' : rs i' * S.C.R + S.C.R ≤ s₃) (hir' : s₃ ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening M S A x rs m)
    -- no change at a step from a validator's own tick to the vote time of slot `s'' − k − 1` to before one of its own
    -- ticks to a clock value at most the support cutoff of slot `s''` (the window before `s''`, read per tick)
    (hNo : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (s'' - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C s'' → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    (hB' : ProposalAt M S x s'' B')
    (hB₂ : ProposalAt M S x (rs i' * S.C.R) B₂)
    -- read at every tick of a validator outside the adversary set to a clock value `c` from the vote time of slot
    -- `s''` to the support cutoff of slot `s₀' + 1`, on the state that tick starts from (rule R3)
    (hFl : ∀ (u : V) (c k : ℕ), M.voteTime S.C s'' ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl k = Event.tick u c → u ∉ A.corrupted k → u ∉ A.corruptedAtTime x (x.time k + Δ S) →
      M.head_height_floor (x.tickInput u c) ≤ (M.chainStateOf S.C B').h)
    (hRootB' : ∀ (u : V) (c k : ℕ), M.voteTime S.C s'' ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl k = Event.tick u c → u ∉ A.corrupted k → u ∉ A.corruptedAtTime x (x.time k + Δ S) → B' ∈ (x.tickInput u c).tree →
      (M.get_fc_root (x.tickInput u c)).AncestorEq B')
    (hDel : ∀ (u : V) (c k : ℕ), M.voteTime S.C s'' ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl k = Event.tick u c → u ∉ A.corrupted k → u ∉ A.corruptedAtTime x (x.time k + Δ S) → B' ∈ (x.tickInput u c).tree)
    -- the finalized block at every tick of a validator outside the adversary set at that tick alone
    (hFin : ∀ (u : V) (c k : ℕ), M.voteTime S.C s'' ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl k = Event.tick u c → u ∉ A.corrupted k → (x.tickInput u c).finalized.compatible B' = true) :
    B'.AncestorEq B₂.parent := by
  have hCarry := (next_proposal_chain_extends_upTo M F U Fx) S A x R GST tGAT tAwakeEnd T₁ r m i i' s'' s₀' s₃ rs B'
    E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hT₁s hTick hThird hAwake hActive hCommittees hEnd hSeq hT₁0
    hs''def hs₀'def hii' hi' hri hsR' hir' hNoCol hNo hB' hFl hRootB' hDel hFin
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hmono := r_lt_of_lt_of_mono rs m hSeq.mono
  -- the later honest round opening slot is `σ + 1 + 1`
  have hgap : rs (i + 1) * S.C.R + S.C.R ≤ rs i' * S.C.R := by
    have h' : (rs (i + 1) + 1) * S.C.R ≤ rs i' * S.C.R := Nat.mul_le_mul_right _ hri
    rw [Nat.add_mul, Nat.one_mul] at h'
    exact h'
  have h0q : rs 0 * S.C.R ≤ rs i' * S.C.R :=
    Nat.mul_le_mul_right _ (le_of_lt (hmono 0 i' (by omega) hi'.le))
  have hpH0 := hSeq.honest i' hi'.le
  obtain ⟨h2k, hAnc⟩ := (window_after_anchor M F U) S A x rs m tGAT tAwakeEnd (rs i' * S.C.R) hSeq h0q
  obtain ⟨σ, hσ⟩ : ∃ σ, rs i' * S.C.R = σ + 1 + 1 := ⟨rs i' * S.C.R - 2, by omega⟩
  rw [hσ] at hpH0 hAnc hB₂ hgap hsR' h2k
  subst hs''def hs₀'def
  rw [hσ, show σ + 1 + 1 - 1 = σ + 1 by omega] at hCarry
  rw [hσ, show σ + 1 + 1 - 1 + 1 = σ + 1 + 1 by omega] at hFl hRootB' hDel
  set s'' := rs (i + 1) * S.C.R with hs''def
  clear_value s''
  set p := S.P.proposer (σ + 1 + 1) with hpdef
  -- the times
  obtain ⟨hv1, hc1, -, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  obtain ⟨hv2, hc2, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1 + 1)
  have hvs'' := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s''
  have hss''σ := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
    (show s'' ≤ σ + 1 by omega)
  have hssA := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
    (show σ + 1 + 1 - 2 * S.C.k + 1 ≤ σ + 1 by omega)
  have hAσ1 : anchorCW S tGAT ≤ M.slotStart S.C (σ + 1 + 1) := le_trans (le_trans hAnc hssA) (by omega)
  have hAσ2 : anchorCW S tGAT ≤ M.slotStart S.C (σ + 1 + 1 + 1) := by
    have := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (show σ + 1 + 1 ≤ σ + 1 + 1 + 1 by omega)
    omega
  have hdw1 := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT (σ + 1) hAσ1
  have hdw2 := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT (σ + 1 + 1) hAσ2
  have hdwsl := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_le_slotStart M.toSlotLayout F.sched) S (σ + 1 + 1)
  have hanc := anchorCW_eq S tGAT
  have hcR : M.supportCutoff S.C (σ + 1 + 1) ≤ aR M S r := by
    unfold aR
    exact (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  have hcE : M.supportCutoff S.C (σ + 1 + 1) ≤ tAwakeEnd := le_trans hcR hEnd
  have hBΔ : ΔClockBehind < Δ S := by linarith
  have hAΔ : ΔClockAhead < Δ S := by linarith
  -- `max (Δ S) Δs` and `max (2 * Δ S) Δs` are at most four delays times `k`
  have hΔs' : Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have hm : ((Δs : ℕ) : ℝ) ≤ max ((Δ S : ℕ) : ℝ) ((Δs : ℕ) : ℝ) := le_max_right _ _
    exact_mod_cast (show ((Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) by push_cast; linarith)
  have hAnc' := hAnc
  rw [hanc, Nat.mul_add] at hAnc'
  have hssA' := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
    (show σ + 1 + 1 - 2 * S.C.k + 1 ≤ σ + 1 by omega)
  have hk4 := Nat.mul_le_mul_left (4 * Δ S) S.C.k_ge_two
  have hmx1 : max (Δ S) Δs ≤ 4 * Δ S * S.C.k := by
    rcases max_choice (Δ S) Δs with h | h <;> rw [h] <;> omega
  have hmx2 : max (2 * Δ S) Δs ≤ 4 * Δ S * S.C.k := by
    rcases max_choice (2 * Δ S) Δs with h | h <;> rw [h] <;> omega
  have hmx2' := le_max_right (2 * Δ S) Δs
  have hGSTσ : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (σ + 1) := by omega
  have hHold0 : tGAT ≤ M.supportCutoff S.C (σ + 1) - max (2 * Δ S) Δs := by omega
  -- the later proposer: honest up to the support cutoff of its slot, so active from `tGAT` to it
  have hpA : p ∈ A.activeThroughout x tGAT (M.supportCutoff S.C (σ + 1 + 1)) :=
    (mem_activeThroughout_of_hAwake_honest_at M F) R E hAwake le_rfl hcE hpH0
  obtain ⟨iB₂, hlB₂, hsentB₂⟩ := hB₂
  have hpi : p ∉ A.corrupted iB₂ := E.not_mem_corrupted_of_tick hlB₂
  have hiT := (E.tick_active iB₂ p _ hlB₂).2.2
  have hti : x.tickInput p (M.slotStart S.C (σ + 1 + 1)) = x.st iB₂ p := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hlB₂]
  have hc0 : M.voteTime S.C s'' ≤ M.slotStart S.C (σ + 1 + 1) := by omega
  have hc0' : M.slotStart S.C (σ + 1 + 1) ≤ M.supportCutoff S.C (σ + 1 + 1) := by omega
  -- the proposer is outside the adversary set one delay after its tick: honest to its slot's support cutoff
  have hpΔ : p ∉ A.corruptedAtTime x (x.time iB₂ + Δ S) :=
    Activity.not_mem_corruptedAtTime.2 fun i hi =>
        (Activity.not_mem_corruptedAtTime.1 hpH0) i (le_trans hi (by
          have h1 := (E.tick_active iB₂ p _ hlB₂).2.2
          have h2 : ((M.slotStart S.C (σ + 1 + 1) : ℕ) : ℝ) + Δ S + Δ S ≤ ((M.supportCutoff S.C (σ + 1 + 1) : ℕ) : ℝ) := by
            exact_mod_cast (show M.slotStart S.C (σ + 1 + 1) + Δ S + Δ S ≤ M.supportCutoff S.C (σ + 1 + 1) by
              omega)
          have h3 := E.ahead_nonneg
          linarith [hSkew]))
  have hB'q := hDel p _ iB₂ hc0 hc0' hlB₂ hpi hpΔ
  have hRq := hRootB' p _ iB₂ hc0 hc0' hlB₂ hpi hpΔ hB'q
  have hFq := hFl p _ iB₂ hc0 hc0' hlB₂ hpi hpΔ
  have hnI := (nodeInv_tickInput_of_tick M F) S A x R E hlB₂
  have hFB'q : (x.tickInput p (M.slotStart S.C (σ + 1 + 1))).finalized.AncestorEq B' := by
    have h := (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E iB₂ p
    rw [← hti] at h
    exact ancestorEq_trans h hRq
  have hF3p : ∃ W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (σ + 1 + 1)))).tree,
      W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (σ + 1 + 1)))).viable_heads ∧ B'.AncestorEq W := by
    refine ⟨B', ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hB'q, hFB'q⟩, ?_,
      ancestorEq_refl B'⟩
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _ hnI,
      (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
    exact ⟨hB'q, hFB'q, hRq, hFq⟩
  -- the chain invariant relative to `B'` at the slots `σ` and `σ + 1`
  have hCE := hCarry (σ + 1 - s'') (by omega)
  rw [show s'' + (σ + 1 - s'') = σ + 1 by omega] at hCE
  have hCE1 := hCarry (σ - s'') (by omega)
  rw [show s'' + (σ - s'') = σ by omega] at hCE1
  -- the anchor is comparable with `B'`
  have hpHσ : p ∈ Hon M S A x σ :=
    Finset.mem_sdiff.2 ⟨Finset.mem_univ _, (not_mem_corruptedAtTime_of_le M) x R E
      ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (show σ + 1 ≤ σ + 1 + 1 by omega)) hpH0⟩
  have hpTT : p ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (σ + 2) : ℕ) : ℤ) (M.slotStart S.C (σ + 1 + 1)) := by
    refine (mem_activeThroughoutToTick_of_mem_activeThroughout M F) x R E (by omega) (by exact_mod_cast (show
      M.dutyWindowStart S.C (σ + 2) ≤ M.slotStart S.C (σ + 1 + 1) by
        have := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_mono M.toSlotLayout F.sched) S
          (show σ + 2 ≤ σ + 1 + 1 + 1 by omega)
        omega)) ?_
    refine Activity.mem_activeThroughout_of_le ?_ ?_ hpA
    · have h : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.dutyWindowStart S.C (σ + 2) : ℕ) : ℝ) := by
        exact_mod_cast (show tGAT + Δ S ≤ M.dutyWindowStart S.C (σ + 2) by
          have := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_mono M.toSlotLayout F.sched) S
            (show σ + 1 + 1 ≤ σ + 2 by omega)
          omega)
      push_cast
      linarith
    · have h : ((M.slotStart S.C (σ + 1 + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (σ + 1 + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show M.slotStart S.C (σ + 1 + 1) + Δ S ≤ M.supportCutoff S.C (σ + 1 + 1) by omega)
      linarith
  have hAcmp : (M.get_anchor (x.tickInput p (M.slotStart S.C (σ + 1 + 1)))
      ((M.slotStart S.C (σ + 1 + 1) : ℕ) : Int)).AncestorEq B' ∨
      B'.AncestorEq (M.get_anchor (x.tickInput p (M.slotStart S.C (σ + 1 + 1)))
      ((M.slotStart S.C (σ + 1 + 1) : ℕ) : Int)) := by
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.get_anchor_cases_locked M F)
        (x.tickInput p (M.slotStart S.C (σ + 1 + 1))) ((M.slotStart S.C (σ + 1 + 1) : ℕ) : Int) with
      ha | ⟨-, e, he, hl, hAe⟩
    · left
      rw [ha, (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
      exact hRq
    · have hl' := ((GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F) _ _ _).1 hl
      rcases (live_lock_entry_source M F U) S A x R σ (M.slotStart S.C (σ + 1 + 1)) p E hSkew hpTT
          (by omega) (by rw [show σ + 2 = σ + 1 + 1 from rfl]; omega) e he hl'.1 with
        ⟨C₁, hC₁, heC₁⟩ | ⟨n₃, sent₃, hrun₃, hA₃, e', he', hl₃, hee'⟩
      · exact ancestorEq_compatible (ancestorEq_trans hAe heC₁) (hCE1.2.2 p hpHσ C₁ hC₁)
      · rcases (compatible_iff _ _).1 (hCE1.2.1 p hpHσ n₃ sent₃ hrun₃ hA₃ e' he' hl₃) with he'B | hBe'
        · exact Or.inl (ancestorEq_trans hAe (ancestorEq_trans hee' he'B))
        · exact ancestorEq_compatible (ancestorEq_trans hAe hee') hBe'
  rcases hAcmp with hAB | hBA
  swap
  · exact ancestorEq_trans hBA ((get_anchor_ancestorEq_proposal_parent M F) S A x R E (σ + 1 + 1) iB₂ B₂ _
      hlB₂ hsentB₂)
  -- the honest votes of slot `σ + 1` extend `B'`
  set Hs : Finset V := S.P.committee (σ + 1) ∩ Hon M S A x (σ + 1) with hHsdef
  have hex : ∀ u ∈ Hs, ∃ H_u : Block V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (σ + 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (σ + 1) H_u.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H_u ∈ (x.tickInput u (M.voteTime S.C (σ + 1))).tree ∧ B'.AncestorEq H_u := by
    intro u hu
    obtain ⟨hK, huH⟩ := Finset.mem_inter.1 hu
    have hub : u ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 1 + 1)) := (Finset.mem_sdiff.1 huH).2
    have hua := (hActive (σ + 1) (by omega) hcE u hub).1
    obtain ⟨k', hl, hAw⟩ := (tick_and_wake_of_tick_window M F U) S A x R (σ + 1) u E
      ((voteTime_tick_window_of_honestActiveAt M F U) S A x R (σ + 1) u E hSkew hua)
    obtain ⟨vote, -, -, hsent⟩ := (honest_votes_of_window M F U) S A x R (σ + 1) u E hl hAw hK
    obtain ⟨H_u, hT, hvt, hBH⟩ := hCE.1 u huH vote ⟨k', hl, hsent⟩
    subst hvt
    exact ⟨H_u, ⟨k', hl, hsent⟩, hT, hBH⟩
  choose Hc hHc using hex
  let Hf : V → Block V := fun u => if h' : u ∈ Hs then Hc u h' else B'
  have hHf : ∀ u (hu : u ∈ Hs), Hf u = Hc u hu := fun u hu => dif_pos hu
  have hMaj := (committee_majority_of_committeeSleepiness M F) S A x _ (σ + 1) hCommittees hAσ1 hcE
  -- the proposer's tick to the support cutoff of slot `σ + 1`
  have hc1R : ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) + ΔClockBehind ≤ ((M.supportCutoff S.C (σ + 1 + 1) : ℕ) : ℝ) := by
    have : ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (σ + 1 + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.supportCutoff S.C (σ + 1) + Δ S ≤ M.supportCutoff S.C (σ + 1 + 1) by omega)
    linarith
  have hG1 : ((tGAT : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) - ΔClockAhead := by
    have : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show tGAT + Δ S ≤ M.supportCutoff S.C (σ + 1) by omega)
    linarith
  obtain ⟨kR, hkR, hkR1, hkR2⟩ := E.tick_of_active (M.supportCutoff S.C (σ + 1)) (by omega) p
    (fun j h1 h2 => Activity.mem_activeThroughout.1 hpA j (le_trans h2 hc1R)
      (le_trans (le_trans hG1 h1) (htime (Nat.le_succ j))))
  have hRootsP : RootsNameBlocksUntil M A x (x.time (x.tickStep p (M.supportCutoff S.C (σ + 1)))) := by
    rw [(tickStep_eq_of_lbl M) x E hkR]
    refine (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) ?_ hRoots
    have : ((M.supportCutoff S.C (σ + 1 + 1) : ℕ) : ℝ) ≤ ((aR M S r : ℕ) : ℝ) := by exact_mod_cast hcR
    linarith
  have hTI : x.time iB₂ ≤ ((M.supportCutoff S.C (σ + 1 + 1) : ℕ) : ℝ) := by
    have : ((M.slotStart S.C (σ + 1 + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (σ + 1 + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.slotStart S.C (σ + 1 + 1) + Δ S ≤ M.supportCutoff S.C (σ + 1 + 1) by omega)
    linarith
  have hcR1 : M.supportCutoff S.C (σ + 1) ≤ aR M S r :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show σ + 1 ≤ σ + 1 + 1 by omega)) hcR
  refine ((proposal_parent_extends_majority_block_upTo M F U) S A x R GST (σ + 1) iB₂ Hs Hf B' B₂ p (E.mono hcR1) hNet hSkew
    hRedeliver (Sy.mono hcR1) hΔs hRootsP hParent (votesCastByOwner_of_unforgeability M F S A x R E) hGSTσ ?_ ?_ ?_ ?_
    hlB₂ hsentB₂ hF3p hAB).1
  · intro u hu
    rw [hHf u hu]
    obtain ⟨hK, huH⟩ := Finset.mem_inter.1 hu
    have hub : u ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 1 + 1)) := (Finset.mem_sdiff.1 huH).2
    refine ⟨hK, ?_, (hHc u hu).1, (hHc u hu).2.1, (hHc u hu).2.2⟩
    rw [(tickStep_eq_of_lbl M) x E hlB₂]
    exact (not_mem_corrupted_of_le_time M) x R E hub hTI
  · intro votes_p support_p hP
    rw [hP.1]
    exact ((counting_of_committee_majority_st M F) S A x R E (σ + 1) (x.tickStep p (M.slotStart S.C (σ + 1 + 1)))
      (Hon M S A x (σ + 1)) p hMaj).2.1
  · intro u hu
    obtain ⟨-, huH⟩ := Finset.mem_inter.1 hu
    have hub : u ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 1 + 1)) := (Finset.mem_sdiff.1 huH).2
    refine Activity.mem_activeThroughout_of_le ?_ ?_
      ((mem_activeThroughout_of_hAwake_honest_at M F) R E hAwake le_rfl hcE hub)
    · exact_mod_cast hHold0
    · have : ((M.supportCutoff S.C (σ + 1) - max (2 * Δ S) Δs + Δs : ℕ) : ℝ) ≤
          ((M.supportCutoff S.C (σ + 1 + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show M.supportCutoff S.C (σ + 1) - max (2 * Δ S) Δs + Δs ≤ M.supportCutoff S.C (σ + 1 + 1) by
          omega)
      push_cast at this
      exact this
  · refine ⟨kR, hkR, fun j h1 h2 => Activity.mem_activeThroughout.1 hpA j
      (le_trans (htime h2) (le_trans hkR2 hc1R)) ?_⟩
    have : ((tGAT : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (σ + 1) - max (2 * Δ S) Δs : ℕ) : ℝ) := by
      exact_mod_cast hHold0
    exact le_trans (le_trans this h1) (htime (Nat.le_succ j))

/-- **B12 restated, part 1, on a copy: two rising quiet openings are at different heights.** The
proof; the audited statement is in `Statements/Executions/Lemma89Statements.lean`.

The route, by contradiction with both proposals `B`, `B₂` at the height `h`: the next proposal
`B'` after `B` has height at least `h + 1` (rising) and at most `H₂ + 1` (A2), so `h` is `H₂ − 1` or
`H₂` (at `B`'s action time, `head_height_floor`, the least chain-state height a viable block may
have, is at most `h`, B2). No honest validator's `head_height_floor` reaches `h + 1` before the
later opening's support cutoff (`floor_le_before_quiet`); so `B'` reaches every honest validator one
delay after its proposal (`held_spread`), and there it has the greatest chain-state height `h + 1`,
no contest and its root on `B'`'s chain. The round's base at `B'`'s slot (`WinCtx.base`) makes the
honest votes of that slot extend `B'`; `lem79_step_sets` carries the chain invariant relative to
`B'` to the slot before the later opening, whose proposer's anchor is then on `B'`'s chain or
comparable with it, so `B'` is an ancestor of `B₂`'s parent
(`proposal_parent_extends_majority_block`): `B₂` is higher than `h`.

The threshold time `T₁` may be as late as one delay before the start of slot
`rs 0 * R − k − 1`, in place of at most the start of slot
`rs 0 * R − 2k`: the climb takes `T₁` three delays later so that the first honest
attestation above the threshold comes at a round whose slot `r * R + 1` starts at or after the
committee premise's anchor. The proof reads `hT₁0` only to bound `T₁ + Δ` by
the start of a later slot.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `H₂`: the threshold; `m`: the index of the last honest round opening slot; `i < i'`: the indices of the two honest round opening slots; `rs`: the
  openings' rounds; `B`, `B₂`: their proposals.

Roots name blocks until `aR M S r`: the climb's context `ClimbCtx` carries the premise at the action
time of round `r`; the honest round opening slots' contexts `QuietCtx` read up to support cutoffs of
slots at most `r * R`, before it.

Restated with the delivery premises up to `aR M S r`: the bound of its roots `hRoots`, the bundle
`ClimbCtxUpTo`'s; the honest round opening slots' bundles `QuietCtxUpTo` read up to support cutoffs
of slots at most `r * R`, before it.

Read aloud: two honest round opening slots with no fork-choice change in their windows and rounds, the first
rising, propose at different heights, with the delivery premises up to the action time of round `r`.
-/
theorem quiet_rising_heights_differ_cutoff_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ r H₂ m i i' s''₂ : ℕ)
    (rs : ℕ → ℕ)
    (B B₂ : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (aR M S r)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (aR M S r))
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
    (hT₁0 : T₁ + Δ S ≤ M.slotStart S.C (rs 0 * S.C.R - S.C.k - 1))
    (hii' : i < i') (hi' : i' < m) (hsR' : rs i' * S.C.R + S.C.R ≤ s''₂)
    (hir' : s''₂ ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening M S A x rs m)
    (hNo : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C (rs (i + 1) * S.C.R) → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    (hNo' : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i' * S.C.R - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C s''₂ → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    (hRise : RisingAt M S A x rs i)
    (hB : ProposalAt M S x (rs i * S.C.R) B)
      (hB₂ : ProposalAt M S x (rs i' * S.C.R) B₂) :
    (M.chainStateOf S.C B).h ≠ (M.chainStateOf S.C B₂).h := by
  intro hEq
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hAΔ : ΔClockAhead < Δ S := by linarith
  have hBΔ : ΔClockBehind < Δ S := by linarith
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hmono := r_lt_of_lt_of_mono rs m hSeq.mono
  have hri1 : rs (i + 1) ≤ rs i' := by
    rcases Nat.lt_or_ge (i + 1) i' with h | h
    · exact le_of_lt (hmono _ _ h (by omega))
    · have : i + 1 = i' := by omega
      rw [this]
  have hir : rs (i + 1) * S.C.R ≤ r * S.C.R := by
    have := Nat.mul_le_mul_right S.C.R hri1
    omega
  -- the case of the next opening
  by_cases hi1 : i' = i + 1
  · subst hi1
    exact (Nat.ne_of_lt (hRise B B₂ hB hB₂)) hEq
  have hri : rs (i + 1) < rs i' := hmono _ _ (by omega) (by omega)
  have hsRi : rs i * S.C.R + S.C.R ≤ rs (i + 1) * S.C.R := by
    have h' : (rs i + 1) * S.C.R ≤ rs (i + 1) * S.C.R :=
      Nat.mul_le_mul_right _ (hmono i (i + 1) (by omega) (by omega))
    rw [Nat.add_mul, Nat.one_mul] at h'
    exact h'
  -- the next proposal `B'`, and the heights
  obtain ⟨B', hB', hBB', hBq', hhlo, hhhi⟩ := (quiet_rising_next_proposal_late_upTo M F U Fx) S A x R GST tGAT
    tAwakeEnd T₁ r H₂ m i rs B E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hT₁s hTick
    hThird hAwake hActive hCommittees hH₂ hOld hEnd hSeq hT₁0 (by omega) hir hNoCol hNo hRise hB
  -- the two contexts
  obtain ⟨hs1, C⟩ := (quietCtx_of_upTo M F U) S A x R GST tGAT tAwakeEnd r m i rs (E.mono ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) hNet hSkew hRedeliver (Sy.mono ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) hΔs
    ((roots_cutoff_behind_of_aR M F U) S (by omega) E.ahead_nonneg hSkew hRoots) hParent hGST hThird hAwake
    hActive hCommittees hEnd hSeq (by omega) hsRi hir hNoCol hNo
  obtain ⟨hs1', C'⟩ := (quietCtx_of_upTo M F U) S A x R GST tGAT tAwakeEnd r m i' rs (E.mono ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) hNet hSkew hRedeliver (Sy.mono ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) hΔs
    ((roots_cutoff_behind_of_aR M F U) S (by omega) E.ahead_nonneg hSkew hRoots) hParent hGST hThird hAwake
    hActive hCommittees hEnd hSeq hi' hsR' hir' hNoCol hNo'
  have hB₂0 : ProposalAt M S x (rs i' * S.C.R - 1 + 1) B₂ := by rw [← hs1']; exact hB₂
  set s₀ := rs i * S.C.R - 1 with hs₀def
  set s'' := rs (i + 1) * S.C.R with hs''def
  set s₀' := rs i' * S.C.R - 1 with hs₀'def
  set s₃ := s''₂ with hs₃def
  clear_value s₀ s'' s₀' s₃
  have hsR'2 := C'.sR
  have hs''s₀' : s'' + S.C.R ≤ s₀' + 1 := by
    have h' : (rs (i + 1) + 1) * S.C.R ≤ rs i' * S.C.R := Nat.mul_le_mul_right _ hri
    rw [Nat.add_mul, Nat.one_mul] at h'
    omega
  have hEnd' := (C'.cut_end M F)
  -- the times
  have hw0 := (C.win M F U) (le_refl (s₀ + 1))
  have hw0' := (C'.win M F U) (le_refl (s₀' + 1))
  have h0s : rs 0 * S.C.R ≤ s₀ + 1 := (C.rs0 M F)
  have hanc0 := hw0.2
  rw [anchorCW_eq] at hanc0
  have hte := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S
  have hssm : ∀ {a b : ℕ}, a ≤ b → M.slotStart S.C a ≤ M.slotStart S.C b := fun h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S h
  have hscm : ∀ {a b : ℕ}, a ≤ b → M.supportCutoff S.C a ≤ M.supportCutoff S.C b := fun h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h
  obtain ⟨hvA, hcA, -, hsA, -⟩ := hte (s₀ + 1 - S.C.k - 1)
  obtain ⟨hvB, hcB, -, hsB, -⟩ := hte (s'' - S.C.k - 1)
  obtain ⟨hv'', hc'', -, hs''1, -⟩ := hte s''
  obtain ⟨-, hcQ, -, hsQ, -⟩ := hte (s₀' + 1)
  obtain ⟨-, hcQ1, -, -, -⟩ := hte (s₀' + 1 + 1)
  obtain ⟨-, -, -, hs00, -⟩ := hte (rs 0 * S.C.R - S.C.k - 1)
  obtain ⟨-, hcS0, -, -, -⟩ := hte (s₀ + 1)
  have hmE := hssm (show s₀ + 1 - S.C.k - 1 ≤ s₀ + 1 by omega)
  have hmA := hssm (show s₀ + 1 - S.C.k - 1 + 1 ≤ s'' - S.C.k - 1 by omega)
  have hmB := hssm (show rs 0 * S.C.R - S.C.k - 1 + 1 ≤ s'' by omega)
  have hmC := hssm (show s₀ + 1 - S.C.k - 1 ≤ s'' by omega)
  have hmD := hssm (show s'' ≤ s₀' + 1 by omega)
  have hcR : M.supportCutoff S.C (s₀' + 1 + 1) ≤ aR M S r := by
    unfold aR
    exact hscm (by omega)
  have hT₁sl : T₁ + Δ S ≤ M.slotStart S.C (s₀' + 1 - S.C.k - 1) := by
    have h1 := hssm (show rs 0 * S.C.R - S.C.k - 1 ≤ s₀' + 1 - S.C.k - 1 by
      have := (C'.rs0 M F)
      omega)
    omega
  -- the climb's context
  have CC := (ClimbCtxUpTo.of_clock M F U R E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hT₁s hThird hAwake hH₂
    hOld hEnd hTick (by have := hscm (show s₀ + 1 ≤ r * S.C.R by omega); omega))
  set h := (M.chainStateOf S.C B).h with hhdef
  clear_value h
  have hh : h + 1 = H₂ ∨ h = H₂ := by
    unfold Height at *
    omega
  have hB₂h : (M.chainStateOf S.C B₂).h = h := hEq.symm
  -- no tick of an honest validator from the vote time of slot `s''` to the later opening's support cutoff starts from
  -- a `head_height_floor` greater than `h`
  have hF := (floor_le_before_quiet_tick_from_upTo M F U Fx) R E CC C' hT₁sl h hh B₂ hB₂0 hB₂h
    (le_trans ((stepBefore_mono M) x R E ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show s₀' + 1 ≤ r * S.C.R by omega))) (Nat.sub_le _ _))
  -- what a tick from the vote time of slot `s''` to the later opening's support cutoff reads
  have hRd : ∀ (u : V) (c kt : ℕ), M.voteTime S.C s'' ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl kt = Event.tick u c → u ∉ A.corrupted kt →
      x.tickInput u c = x.st kt u ∧ M.head_height_floor (x.st kt u) ≤ h ∧
        hMax M S.C (x.st kt u) ≤ h + 1 ∧ (x.st kt u).justifiedHeight ≤ h ∧
        x.time kt ≤ ((aR M S r : ℕ) : ℝ) ∧ M.nodeInv S.C S.P S.X (x.st kt u) := by
    intro u c kt hc1 hc2 hkt hukt
    have hTu : x.tickInput u c = x.st kt u := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hkt]
    have hfu := hF u c kt (by omega) hc2 hkt hukt
    rw [hTu] at hfu
    have hinv := (lem11_node_invariant M F S A x R E kt u hukt).1
    have hmx := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_le_floor_add_one M F) S.C S.P S.X _ hinv
    have hjl := (h_j_lt_h_max_st M F) S A x R E kt u
    have hkt2 := (E.tick_active kt u c hkt).2.2
    have hTa : ((M.supportCutoff S.C (s₀' + 1) : ℕ) : ℝ) + Δ S ≤ ((aR M S r : ℕ) : ℝ) := by
      exact_mod_cast (show M.supportCutoff S.C (s₀' + 1) + Δ S ≤ aR M S r by omega)
    have hc2R : (c : ℝ) ≤ ((M.supportCutoff S.C (s₀' + 1) : ℕ) : ℝ) := by exact_mod_cast hc2
    refine ⟨hTu, hfu, by unfold Height at *; omega, by unfold Height at *; omega, by linarith, hinv⟩
  -- `head_height_floor` at those ticks is at most `B'`'s chain-state height
  have hFl : ∀ (u : V) (c k : ℕ), M.voteTime S.C s'' ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl k = Event.tick u c → u ∉ A.corrupted k →
      M.head_height_floor (x.tickInput u c) ≤ (M.chainStateOf S.C B').h := by
    intro u c k hc1 hc2 hk' hu
    obtain ⟨hTu, hfu, -⟩ := hRd u c k hc1 hc2 hk' hu
    rw [hTu]
    unfold Height at *
    omega
  -- an honest holder of `B'` at those ticks has its root on `B'`'s chain
  have hRootB' : ∀ (u : V) (c k : ℕ), M.voteTime S.C s'' ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl k = Event.tick u c → u ∉ A.corrupted k → B' ∈ (x.tickInput u c).tree →
      (M.get_fc_root (x.tickInput u c)).AncestorEq B' := by
    intro u c k hc1 hc2 hk' hu hB'u
    obtain ⟨hTu, -, hmx, hjl, hTk, hinv⟩ := hRd u c k hc1 hc2 hk' hu
    rw [hTu] at hB'u ⊢
    have hBh := le_hMax M (C := S.C) hB'u
    have hTE : x.time k ≤ tAwakeEnd := by
      have : ((aR M S r : ℕ) : ℝ) ≤ (tAwakeEnd : ℝ) := by exact_mod_cast hEnd
      linarith
    have hFB' : (x.st k u).finalized.AncestorEq B' :=
      (F_ancestorEq_of_high_st M F Fx) S A x R E hRoots tAwakeEnd k k u u B' hThird hTE hTE hu hu hB'u
        (by unfold Height at *; omega) (max_le hTk hTk)
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X (x.st k u) hinv with ⟨hJ, hm1, hc⟩ | ⟨hFr, -⟩
    · rw [hJ]
      by_contra hJB
      have hct := (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_true_of M F) S.C S.P S.X
        (x.st k u) hinv B' hm1 hB'u hFB' (by unfold Height at *; omega) hJB
      rw [hc] at hct
      cases hct
    · rw [hFr]
      exact hFB'
  -- `B'` is in the tree at those ticks
  have hqH := hSeq.honest (i + 1) (by omega)
  obtain ⟨iP, hlP, hsentP⟩ := hB'
  have hBP : B' ∈ (x.st (iP + 1) (S.P.proposer s'')).tree := by
    have : x.tickOutput (S.P.proposer s'') (M.slotStart S.C s'') = x.st (iP + 1) (S.P.proposer s'') := by
      unfold Trace.tickOutput
      rw [(tickStep_eq_of_lbl M) x E hlP]
    rw [← this]
    exact hBq'
  have hs1'' : s'' - 1 + 1 = s'' := by omega
  have hDel : ∀ (u : V) (c k : ℕ), M.voteTime S.C s'' ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl k = Event.tick u c → u ∉ A.corrupted k → B' ∈ (x.tickInput u c).tree := by
    intro u c k hc1 hc2 hk' hu
    obtain ⟨hTu, -, -, hjl, hTk, -⟩ := hRd u c k hc1 hc2 hk' hu
    rw [hTu]
    have hp1 := E.not_mem_corrupted_succ_of_tick hlP
    have hTP : x.time (iP + 1) ≤ x.time k := by
      have h1 := ((time_of_lbl_tick M) x R E hlP).2.2
      have h2 := (E.tick_active k u c hk').2.1
      have h3 : ((M.slotStart S.C s'' : ℕ) : ℝ) + Δ S ≤ (c : ℝ) := by exact_mod_cast (show _ ≤ c by omega)
      linarith
    have hTE : x.time k ≤ tAwakeEnd := by
      have : ((aR M S r : ℕ) : ℝ) ≤ (tAwakeEnd : ℝ) := by exact_mod_cast hEnd
      linarith
    have hFB' : (x.st k u).finalized.AncestorEq B' :=
      (F_ancestorEq_of_high_st M F Fx) S A x R E hRoots tAwakeEnd k (iP + 1) u (S.P.proposer s'') B' hThird hTE
        (le_trans hTP hTE) hu hp1 hBP (by unfold Height at *; omega) (max_le hTk (le_trans hTP hTk))
    -- the deadline of the proposer's send: at most the action time of round `r`, and `ΔClockAhead` before `c`
    have hTP1 := ((time_of_lbl_tick M) x R E hlP).2.2
    have hGs : ((GST : ℕ) : ℝ) ≤ ((M.slotStart S.C s'' : ℕ) : ℝ) := by
      exact_mod_cast (show GST ≤ M.slotStart S.C s'' by omega)
    have hmaxP : max (x.time (iP + 1)) ((GST : ℕ) : ℝ) ≤ ((M.slotStart S.C s'' : ℕ) : ℝ) + ΔClockBehind :=
      max_le hTP1 (by linarith)
    have hsA : ((M.slotStart S.C s'' : ℕ) : ℝ) + Δ S ≤ ((aR M S r : ℕ) : ℝ) := by
      exact_mod_cast (show M.slotStart S.C s'' + Δ S ≤ aR M S r by omega)
    have hcs : ((M.slotStart S.C s'' : ℕ) : ℝ) + Δ S ≤ (c : ℝ) := by exact_mod_cast (show _ ≤ c by omega)
    refine (proposal_held_at_later_tick_of_deadline M F U) S A x R (s'' - 1) iP k c B' (S.P.proposer s'') u E hSkew
      hRedeliver ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hTk hRoots) hParent
      (by rw [hs1'']; exact hc1) hk' ?_ (by rw [hs1'']; exact hlP) hsentP hBP
      (GoldilocksCorrectness.Statements.AbstractTrace.deadlineUpTo_eq_some.2 ⟨by linarith, rfl⟩) (by linarith)
      ((compatible_iff _ _).2 (Or.inl hFB'))
    intro j h1 h2
    have hwj : u ∉ A.corrupted j := E.not_mem_corrupted_of_le h2 hu
    rw [hs1''] at h1
    have hgs : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((M.slotStart S.C s'' : ℕ) : ℝ) := by
      exact_mod_cast (show tGAT + Δ S ≤ M.slotStart S.C s'' by omega)
    push_cast at hgs
    refine Finset.mem_sdiff.2 ⟨hAwake j u (le_trans (htime h2) hTE) (by linarith [htime (Nat.le_succ j)]) hwj, hwj⟩
  -- the finalized block at those ticks, of a validator outside the adversary set at the tick alone: `B'` or an
  -- ancestor of `B'` (`F_ancestorEq_of_high_st`, as in `hRootB'`;)
  have hFin : ∀ (u : V) (c k : ℕ), M.voteTime S.C s'' ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl k = Event.tick u c → u ∉ A.corrupted k → (x.tickInput u c).finalized.compatible B' = true := by
    intro u c k hc1 hc2 hk' hu
    have hB'u := hDel u c k hc1 hc2 hk' hu
    obtain ⟨hTu, -, hmx, hjl, hTk, -⟩ := hRd u c k hc1 hc2 hk' hu
    rw [hTu] at hB'u ⊢
    have hBh := le_hMax M (C := S.C) hB'u
    have hTE : x.time k ≤ tAwakeEnd := by
      have : ((aR M S r : ℕ) : ℝ) ≤ (tAwakeEnd : ℝ) := by exact_mod_cast hEnd
      linarith
    exact (compatible_iff _ _).2 (Or.inl ((F_ancestorEq_of_high_st M F Fx) S A x R E hRoots tAwakeEnd k k u u B'
      hThird hTE hTE hu hu hB'u (by unfold Height at *; omega) (max_le hTk hTk)))
  -- no change from a validator's own tick to the vote time of slot `s'' − k − 1` to before its ticks to clock values
  -- at most the support cutoff of slot `s''`: the window of opening `i` read from a later start
  have hNo'' := (noChange_tick_start_later M F) R E hSkew hAwake (tGAT := tGAT) (tAwakeEnd := tAwakeEnd)
    (c₀ := M.voteTime S.C (s₀ + 1 - S.C.k - 1)) (c₁ := M.voteTime S.C (s'' - S.C.k - 1))
    (by omega) (by omega) (by have := hscm (show s₀ + 1 ≤ r * S.C.R + 1 by omega); unfold aR at hEnd; omega)
    (by rw [show s₀ + 1 = rs i * S.C.R by omega]; exact hNo)
  -- the shared part: `B'` is an ancestor of `B₂`'s parent
  have hB'P₂ := (next_proposal_ancestorEq_later_parent_upTo M F U Fx) S A x R GST tGAT tAwakeEnd T₁ r m i i' s'' s₀' s₃ rs B' B₂
    E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hT₁s hTick hThird hAwake hActive hCommittees hEnd hSeq hT₁0
    hs''def hs₀'def (by omega) hi' hri (by omega) hir' hNoCol hNo'' ⟨iP, hlP, hsentP⟩ hB₂ (fun u c k h1 h2 h3 h4 _ => hFl u c k h1 h2 h3 h4)
    (fun u c k h1 h2 h3 h4 _ h5 => hRootB' u c k h1 h2 h3 h4 h5) (fun u c k h1 h2 h3 h4 _ => hDel u c k h1 h2 h3 h4) hFin
  obtain ⟨iB₂, hlB₂, hsentB₂⟩ := hB₂0
  obtain ⟨-, -, hB₂par?, -⟩ := (proposal_parent_walk_end M F U) S A x R E s₀' iB₂ B₂ _ hlB₂ hsentB₂
  have hPB₂ := GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_parent? hB₂par?
  have hh1 := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C (ancestorEq_trans hB'P₂ hPB₂)
  unfold Height at *
  omega

open Classical in
/-- **B12 restated, part 2, on a copy: at most two rising quiet openings before the climb's end.**
In the climb's context, the honest round opening slots `i < m` with `rs i * R < r * R`, no
fork-choice change from its own tick to the vote time of slot `rs i * R − k − 1` to before the support
cutoff of slot `min (rs (i + 1) * R) (r * R)`, and rising when `rs (i + 1) * R ≤ r * R`, are at most
two, when no opening's proposal collides with a block its proposer held.

Why: every such opening's proposal has chain-state height `H₂ − 1` or `H₂`
(`quiet_rising_next_proposal_late`, or `quiet_straddler_heights` for the one whose round holds
`r * R`), and two of them have different heights (`quiet_rising_heights_differ_cutoff`, with the
later one's range ending at `min (rs (i' + 1) * R) (r * R)`; the earlier one's next slot is at or
before the later one's first, so it is rising): the map from such an opening to its proposal's
height is one to one into a set of two heights.

The threshold time `T₁` may be as late as one delay before the start of slot
`rs 0 * R − k − 1`, in place of at most the start of slot
`rs 0 * R − 2k`: the climb takes `T₁` three delays later so that the first honest
attestation above the threshold comes at a round whose slot `r * R + 1` starts at or after the
committee premise's anchor. The proof reads `hT₁0` only to bound `T₁ + Δ` by
the start of a later slot.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `H₂`: the threshold; `m`: the index of the last honest round opening slot; `rs`: the rounds of the honest round opening slots.

Roots name blocks until `aR M S r`: `quiet_rising_next_proposal_late`, `quiet_straddler_heights` and
`quiet_rising_heights_differ_cutoff`, at the action time of round `r`.

Restated with the delivery premises up to `aR M S r`: the bound of its roots `hRoots`, the bundle
`ClimbCtxUpTo`'s; the honest round opening slots' bundles `QuietCtxUpTo` read up to support cutoffs
of slots at most `r * R`, before it.

Read aloud: before the climb's end, at most two honest round opening slots with no fork-choice change in their
windows and rounds climb, the one whose round holds the fast round's first slot included, with the
delivery premises up to the action time of round `r`. -/
theorem quiet_rising_before_fast_round_le_two_cutoff_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ r H₂ m : ℕ) (rs : ℕ → ℕ)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (aR M S r)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (aR M S r))
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
    (hT₁0 : T₁ + Δ S ≤ M.slotStart S.C (rs 0 * S.C.R - S.C.k - 1))
    (hNoCol : ¬ RootCollisionAtOpening M S A x rs m) :
    ((Finset.range m).filter (fun i => rs i * S.C.R < r * S.C.R ∧
      (∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) → k ≤ j →
        x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C (min (rs (i + 1) * S.C.R) (r * S.C.R)) → j < k' →
        w ∉ A.corrupted j → ¬ ForkChoiceChangeStep M S A x w j) ∧
      (rs (i + 1) * S.C.R ≤ r * S.C.R → RisingAt M S A x rs i))).card ≤ 2 := by
  set Fo := (Finset.range m).filter (fun i => rs i * S.C.R < r * S.C.R ∧
      (∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) → k ≤ j →
        x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C (min (rs (i + 1) * S.C.R) (r * S.C.R)) → j < k' →
        w ∉ A.corrupted j → ¬ ForkChoiceChangeStep M S A x w j) ∧
      (rs (i + 1) * S.C.R ≤ r * S.C.R → RisingAt M S A x rs i)) with hFdef
  have hP : ∀ i, i ≤ m → ∃ B : Block V, ProposalAt M S x (rs i * S.C.R) B :=
    fun i hi => (opening_proposal_exists M F U) S A x R tGAT tAwakeEnd m i rs E hAwake hSkew
      hSeq hi
  let Bf : ℕ → Block V := fun i =>
    if hi : i ≤ m then Classical.choose (hP i hi) else Block.genesis
  have hBf : ∀ i (hi : i ≤ m), ProposalAt M S x (rs i * S.C.R) (Bf i) := by
    intro i hi
    simp only [Bf, dif_pos hi]
    exact Classical.choose_spec (hP i hi)
  have hmem : ∀ i ∈ Fo, i < m ∧ rs i * S.C.R < r * S.C.R ∧
      (∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) → k ≤ j →
        x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C (min (rs (i + 1) * S.C.R) (r * S.C.R)) → j < k' →
        w ∉ A.corrupted j → ¬ ForkChoiceChangeStep M S A x w j) ∧
      (rs (i + 1) * S.C.R ≤ r * S.C.R → RisingAt M S A x rs i) := by
    intro i hi
    rw [hFdef, Finset.mem_filter, Finset.mem_range] at hi
    exact ⟨hi.1, hi.2⟩
  -- a round's first slot before `r * R` is at least one round before it
  have hmul : ∀ a : ℕ, a * S.C.R < r * S.C.R → a * S.C.R + S.C.R ≤ r * S.C.R := by
    intro a h
    have h1 : a < r := Nat.lt_of_mul_lt_mul_right h
    have h2 := Nat.mul_le_mul_right S.C.R (show a + 1 ≤ r by omega)
    rw [Nat.add_mul, Nat.one_mul] at h2
    exact h2
  -- the no-change hypothesis of the climb's steps, when the next slot is at or before `r * R`
  have hNoNext : ∀ i, rs (i + 1) * S.C.R ≤ r * S.C.R →
      (∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) → k ≤ j →
        x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C (min (rs (i + 1) * S.C.R) (r * S.C.R)) → j < k' →
        w ∉ A.corrupted j → ¬ ForkChoiceChangeStep M S A x w j) →
      ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) → k ≤ j →
        x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C (rs (i + 1) * S.C.R) → j < k' → w ∉ A.corrupted j →
        ¬ ForkChoiceChangeStep M S A x w j := by
    intro i hir hNo
    rw [min_eq_left hir] at hNo
    exact hNo
  let f : ℕ → ℕ := fun i => (M.chainStateOf S.C (Bf i)).h
  have hmaps : ∀ i ∈ Fo, f i ∈ (insert (H₂ - 1) {H₂} : Finset ℕ) := by
    intro i hi
    obtain ⟨him, hlt, hNo, hRise⟩ := hmem i hi
    have hh : H₂ ≤ (M.chainStateOf S.C (Bf i)).h + 1 ∧ (M.chainStateOf S.C (Bf i)).h ≤ H₂ := by
      by_cases hir : rs (i + 1) * S.C.R ≤ r * S.C.R
      · obtain ⟨-, -, -, -, h1, h2⟩ := (quiet_rising_next_proposal_late_upTo M F U Fx) S A x R GST tGAT
          tAwakeEnd T₁ r H₂ m i rs (Bf i) E hNet hSkew hRedeliver Sy hΔs hRoots hParent
          hGST hT₁s hTick hThird hAwake hActive hCommittees hH₂ hOld hEnd hSeq hT₁0 him hir hNoCol
          (hNoNext i hir hNo) (hRise hir) (hBf i (le_of_lt him))
        exact ⟨h1, h2⟩
      · rw [min_eq_right (le_of_lt (Nat.lt_of_not_le hir))] at hNo
        exact (quiet_straddler_heights_upTo M F U Fx) S A x R GST tGAT tAwakeEnd T₁ r H₂ m i rs (Bf i) E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hT₁s hTick hThird hAwake hActive hCommittees
          hH₂ hOld hEnd hSeq hT₁0 him (hmul _ hlt) hNoCol hNo (hBf i (le_of_lt him))
    rw [Finset.mem_insert, Finset.mem_singleton]
    show (M.chainStateOf S.C (Bf i)).h = H₂ - 1 ∨ (M.chainStateOf S.C (Bf i)).h = H₂
    unfold Height at *
    omega
  -- two of them: the earlier one's next slot is at or before the later one's, so it rises
  have hpair : ∀ i ∈ Fo, ∀ i' ∈ Fo, i < i' → f i ≠ f i' := by
    intro i hi i' hi' hlt hff
    obtain ⟨him, -, hNo, hRise⟩ := hmem i hi
    obtain ⟨him', hlt', hNo', -⟩ := hmem i' hi'
    have hle1 : rs (i + 1) * S.C.R ≤ rs i' * S.C.R := by
      rcases Nat.lt_or_ge (i + 1) i' with h | h
      · exact Nat.mul_le_mul_right _
          (le_of_lt (r_lt_of_lt_of_mono rs m hSeq.mono _ _ h (le_of_lt him')))
      · rw [show i' = i + 1 by omega]
    have hir : rs (i + 1) * S.C.R ≤ r * S.C.R := by omega
    have hsR' : rs i' * S.C.R + S.C.R ≤ min (rs (i' + 1) * S.C.R) (r * S.C.R) :=
      le_min ((opening_round_step M F) hSeq him') (hmul _ hlt')
    exact (quiet_rising_heights_differ_cutoff_upTo M F U Fx) S A x R GST tGAT tAwakeEnd T₁ r H₂ m i i'
      (min (rs (i' + 1) * S.C.R) (r * S.C.R)) rs (Bf i) (Bf i') E hNet hSkew hRedeliver Sy hΔs
      hRoots hParent hGST hT₁s hTick hThird hAwake hActive hCommittees hH₂ hOld hEnd hSeq hT₁0 hlt him'
      hsR' (min_le_right _ _) hNoCol (hNoNext i hir hNo) hNo' (hRise hir)
      (hBf i (le_of_lt him)) (hBf i' (le_of_lt him')) hff
  have hinj : Set.InjOn f Fo := by
    intro i hi i' hi' hff
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact hpair i hi i' hi' hlt hff
    · exact hpair i' hi' i hi hlt hff.symm
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  have hIcc : (insert (H₂ - 1) {H₂} : Finset ℕ).card ≤ 2 :=
    le_trans (Finset.card_insert_le _ _) (by rw [Finset.card_singleton])
  omega

/-- **The next proposal after a waiting quiet opening** (probe copy of `quiet_rising_next_proposal`,
with the rising hypothesis replaced by waiting and `h(B) ≤ H₂` taken as a hypothesis): `B'` is on
`B`'s chain at `B`'s chain-state height (Lemma 89r at the opening,
`QuietCtx.round89r`).

The threshold time `T₁` may be as late as one delay before the start of slot
`rs 0 * R − k − 1`, in place of at most the start of slot
`rs 0 * R − 2k`: the climb takes `T₁` three delays later so that the first honest
attestation above the threshold comes at a round whose slot `r * R + 1` starts at or after the
committee premise's anchor. The proof reads `hT₁0` only to bound `T₁ + Δ` by
the start of a later slot.

Roots name blocks until `aR M S r`: the climb's context `ClimbCtx` carries the premise at the action
time of round `r`; the honest round opening slots' contexts `QuietCtx` read up to support cutoffs of
slots at most `r * R`, before it.

Restated with the delivery premises up to `aR M S r`: the bound of its roots `hRoots`, the bundle
`ClimbCtxUpTo`'s; the honest round opening slots' bundles `QuietCtxUpTo` read up to support cutoffs
of slots at most `r * R`, before it; the attestations (`hSyncF`, `hCatchF`) up to
`M.slotStart S.C (rs (i + 1) * S.C.R)`, the bound
`QuietCtxUpTo.round89r` reads them at for
the next opening.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: a waiting quiet opening's next proposal extends it at the same height, `H₂ − 1` or `H₂`,
with the delivery premises up to the action time of round `r` (those of the FG messages up to the
start of slot `rs (i + 1) * R`). -/
theorem quiet_waiting_next_proposal_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ r H₂ m i : ℕ) (rs : ℕ → ℕ)
    (B : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (aR M S r)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (aR M S r))
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
    (hT₁0 : T₁ + Δ S ≤ M.slotStart S.C (rs 0 * S.C.R - S.C.k - 1))
    (hi : i < m) (hir : rs (i + 1) * S.C.R ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening M S A x rs m)
    (hNo : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C (rs (i + 1) * S.C.R) → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    {ΔNet_F : ℕ} (E_F : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.slotStart S.C (rs (i + 1) * S.C.R))) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S) {Δs_F : ℕ}
    (Sy_F : SyncedWithinUpTo A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST (M.slotStart S.C (rs (i + 1) * S.C.R)))
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- every validator outside the adversary set at the support cutoff of the slot after the opening's first slot is
    -- active through the attestations' sync delay after the later of that first slot's duty window's start and `GST`
    --
    (hHoldF : ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (rs i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hWait : ∀ B' : Block V, ProposalAt M S x (rs (i + 1) * S.C.R) B' →
      (M.chainStateOf S.C B').h ≤ (M.chainStateOf S.C B).h)
    (hTop : (M.chainStateOf S.C B).h ≤ H₂)
    (hB : ProposalAt M S x (rs i * S.C.R) B) :
    ∃ B' : Block V, ProposalAt M S x (rs (i + 1) * S.C.R) B' ∧
      B.AncestorEq B' ∧ (M.chainStateOf S.C B').h = (M.chainStateOf S.C B).h ∧
      B' ∈ (x.tickOutput (S.P.proposer (rs (i + 1) * S.C.R)) (M.slotStart S.C (rs (i + 1) * S.C.R))).tree ∧
      H₂ ≤ (M.chainStateOf S.C B).h + 1 ∧ (M.chainStateOf S.C B).h ≤ H₂ := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  obtain ⟨hs1, C⟩ := (quietCtx_of_upTo M F U) S A x R GST tGAT tAwakeEnd r m i rs (E.mono ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) hNet hSkew hRedeliver (Sy.mono ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) hΔs
    ((roots_cutoff_behind_of_aR M F U) S (by omega) E.ahead_nonneg hSkew hRoots) hParent hGST hThird hAwake
    hActive hCommittees hEnd hSeq hi
    ((opening_round_step M F) hSeq hi) hir hNoCol hNo
  have hB0 : ProposalAt M S x (rs i * S.C.R - 1 + 1) B := by rw [← hs1]; exact hB
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
  have CC := (ClimbCtxUpTo.of_clock M F U R E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hT₁s hThird hAwake hH₂
    hOld hEnd hTick (by omega))
  -- the next proposal `B'`
  obtain ⟨B', hB'⟩ := (opening_proposal_exists M F U) S A x R tGAT tAwakeEnd m (i + 1) rs E hAwake hSkew hSeq
    (by omega)
  rw [← hs''def] at hB'
  have hW := hWait B' hB'
  have h89 := (C.round89r M F R E U Fx) hs''def.symm B B' hB0 hB' E_F hNet_F hSkew_F Sy_F hΔs_F
    --: the holder row of the opening's first slot
    (fun v hv => by
      have hv' := (Finset.mem_sdiff.1 hv).2
      rw [← hs1] at hv' ⊢
      exact hHoldF v hv')
  have hBB' : B.AncestorEq B' ∧ (M.chainStateOf S.C B').h = (M.chainStateOf S.C B).h := by
    refine ⟨h89.1, ?_⟩
    rcases h89.2.1 with h' | ⟨h', -⟩
    · unfold Height at *
      omega
    · exact h'
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
  have hcl2 := (C.clause2_tick M F R E U Fx) B hB0
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
  have hbnd := CC.bounds_st M F U R E Fx (j := j) (w := v₀) (c := M.slotStart S.C (s₀ + 1 - S.C.k - 1))
    hT₁s₀ hk₀v.1 hkj hv₀j hjk₀
    (by
      have : ((M.supportCutoff S.C (s₀ + 1 + 1) : ℕ) : ℝ) + Δ S ≤ ((aR M S r : ℕ) : ℝ) := by
        exact_mod_cast (show M.supportCutoff S.C (s₀ + 1 + 1) + Δ S ≤ aR M S r by
          unfold aR
          have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show r * S.C.R ≤ r * S.C.R + 1 by omega)
          omega)
      linarith [hjt.2, hSkew])
    (by
      have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (show s₀ + 1 - S.C.k - 1 ≤ r * S.C.R + 1 by omega)
      have := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (s₀ + 1 - S.C.k - 1)
      unfold aR
      omega)
  have hflv := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_sub_one_le_floor M F) S.C S.P S.X
    (x.tickInput v₀ (M.supportCutoff S.C (s₀ + 1 + 1)))
    ((nodeInv_tickInput_of_tick M F) S A x R E hjl)
  have hfl2 := (hcl2 v₀ hv₀H).2
  have hbnd1 := hbnd.1
  have e1 : x.tickInput v₀ (M.supportCutoff S.C (s₀ + 1 + 1)) = x.st j v₀ := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hjl]
  rw [e1] at hflv hfl2
  refine ⟨B', hB', hBB'.1, hBB'.2, hBq', ?_, hTop⟩
  have h1 : hMax M S.C (x.st j v₀) ≤ (M.chainStateOf S.C B).h + 1 := by
    have h2 := le_trans hflv hfl2
    unfold Height at *
    omega
  exact le_trans hbnd1 h1

/-- **In the waiting phase, no honest validator reaches the waited height's justification before the later opening's
support cutoff, read at its tick** (the part of `quiet_waiting_same_entry_cutoff` that reads
`h_j_lt_of_later_proposal_st_upTo` and `h_j_lt_or_genesis_before_cutoff_st_upTo`, a theorem of its own so that each proof stays
within the default heartbeat budget). The later opening's proposer `q`, outside the adversary set at the support cutoff
of slot `s₀' + 1`, proposes `B₂` at the height `h ≥ 2` at its tick to the start of slot `s₀' + 1`; every tick of a
validator outside the adversary set at the tick, to a clock value from `T₁ + 1 + Δ S` to that support cutoff, starts
from a `head_height_floor` at most `h`; no validator's step after its own tick to `c₁` and before a later tick of its
own to a clock value at most `cs` is a fork-choice change. Then every tick `k` of a validator `u` to a clock value `c`
from `cR` to the support cutoff of slot `s₀' + 1`, with `u` outside the adversary set at `k`, starts from `h_j < h`.

Why: when the real time of `k` is at least one delay before the start of slot `s₀' + 1`, `h_j_lt_of_later_proposal_st`
(the windows from `tGAT`). Otherwise `u` ticked to `c₁`, at least two delays before that start, at a step `k₁ ≤ k`:
`h_j_lt_or_genesis_before_cutoff_st` from `k₁` (the floor at `k₁` and `k` from `hF`, the no-change premise from `hNo'`
with the tick `k`), and a justified genesis block has `h_j ≤ 1 < h`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`, `tGAT`, `tAwakeEnd`, `T₁`: the
  times; `s₀' + 1`: the later opening's slot; `tL + Δ S = c₁`: the clock value the no-change premise starts from;
  `cR`, `cs`: the clock values bounding the readers and the no-change premise; `h`: the height; `q`, `B₂`: the later
  proposer and its proposal.

Restated with the delivery premises up to the start of slot `s₀' + 1`, the bound the
`_st_upTo` forms read them at.

Read aloud: in the waiting phase, an honest validator's tick before the later opening's support cutoff starts from a
justification lower than the waited height. -/
theorem waiting_h_j_lt_at_tick_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ s₀' tL c₁ cR cs h : ℕ)
    (q : V) (B₂ : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.slotStart S.C (s₀' + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.slotStart S.C (s₀' + 1)))
    (hRoots : RootsNameBlocksUntil M A x ((M.slotStart S.C (s₀' + 1) + Δ S : ℕ) : ℝ))
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hGST : GST ≤ tGAT) (hT₁s : tGAT + Δs ≤ T₁)
    -- the clock values: `c₁ = tL + Δ S`, after `T₁` and at least two delays before the later opening's slot; the
    -- readers from `cR`, after `T₁`; the slot's times inside the awake window
    (htL : tL + Δ S = c₁) (hT₁c₁ : T₁ + 1 + Δ S ≤ c₁) (hT₁L : T₁ + Δ S ≤ tL)
    (hc₁s : c₁ + Δ S + Δ S ≤ M.slotStart S.C (s₀' + 1)) (hT₁cR : T₁ + 1 + Δ S ≤ cR)
    (hcs : M.supportCutoff S.C (s₀' + 1) ≤ cs)
    (hEndN : M.supportCutoff S.C (s₀' + 1) + Δ S ≤ tAwakeEnd)
    (hvfN : M.viewFreeze S.C s₀' + Δ S ≤ M.supportCutoff S.C (s₀' + 1))
    (hgsv : tGAT + Δ S ≤ M.viewFreeze S.C s₀')
    (hss : M.slotStart S.C (s₀' + 1) + Δ S ≤ M.supportCutoff S.C (s₀' + 1))
    (hqH : q ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀' + 1)))
    (hB₂0 : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C (s₀' + 1)) ∧
      (⟨q, NamedObject.block B₂⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hB₂h : (M.chainStateOf S.C B₂).h = h) (hh2 : 2 ≤ h)
    (hF : ∀ (u : V) (c kt : ℕ), T₁ + 1 + Δ S ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl kt = Event.tick u c → u ∉ A.corrupted kt → M.head_height_floor (x.tickInput u c) ≤ h)
    (hNo' : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w c₁ → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ cs → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j) :
    ∀ (u : V) (c k : ℕ), cR ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl k = Event.tick u c → u ∉ A.corrupted k →
      (x.st k u).justifiedHeight < h := by
  intro u c k hc1 hc2 hk' hu
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hAΔ : ΔClockAhead < Δ S := by linarith
  have hBΔ : ΔClockBehind < Δ S := by linarith
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hEndR : ((M.supportCutoff S.C (s₀' + 1) : ℕ) : ℝ) + Δ S ≤ (tAwakeEnd : ℝ) := by exact_mod_cast hEndN
  have hvfR : ((M.viewFreeze S.C s₀' : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀' + 1) : ℕ) : ℝ) := by
    exact_mod_cast hvfN
  have hc₁sR : ((c₁ : ℕ) : ℝ) + Δ S + Δ S ≤ ((M.slotStart S.C (s₀' + 1) : ℕ) : ℝ) := by exact_mod_cast hc₁s
  have hssR : ((M.slotStart S.C (s₀' + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s₀' + 1) : ℕ) : ℝ) := by
    exact_mod_cast hss
  have hgc₁ : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((c₁ : ℕ) : ℝ) := by
    exact_mod_cast (show tGAT + Δ S ≤ c₁ by omega)
  have hT₁R : ((tGAT + Δs : ℕ) : ℝ) ≤ ((T₁ : ℕ) : ℝ) := by exact_mod_cast hT₁s
  push_cast at hT₁R
  have hT₁c : ((T₁ + 1 + Δ S : ℕ) : ℝ) ≤ ((c₁ : ℕ) : ℝ) := by exact_mod_cast hT₁c₁
  push_cast at hT₁c
  obtain ⟨iB₂, hlB₂, hsentB₂⟩ := hB₂0
  have hkq : x.tickStep q (M.slotStart S.C (s₀' + 1)) = iB₂ := (tickStep_eq_of_lbl M) x E hlB₂
  have hiB₂t := (E.tick_active iB₂ q _ hlB₂).2.2
  have hq' : ∀ j : ℕ, (tGAT : ℝ) ≤ x.time j → j ≤ x.tickStep q (M.slotStart S.C (s₀' + 1)) → q ∈ A.active j := by
    intro j h1 h2
    rw [hkq] at h2
    have hqj : q ∉ A.corrupted j := (Activity.not_mem_corruptedAtTime.1 hqH) j (by
      have := htime h2
      linarith)
    exact Finset.mem_sdiff.2 ⟨hAwake j q (by have := htime h2; linarith)
      (le_trans h1 (htime (Nat.le_succ j))) hqj, hqj⟩
  have hqv : ∃ kq : ℕ, x.lbl kq = Event.tick q (M.viewFreeze S.C s₀') := by
    have hgsvR : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.viewFreeze S.C s₀' : ℕ) : ℝ) := by exact_mod_cast hgsv
    obtain ⟨kq, hkq', -, -⟩ := E.tick_of_active (M.viewFreeze S.C s₀') (by omega) q fun j h1 h2 => by
      have hqj : q ∉ A.corrupted j := (Activity.not_mem_corruptedAtTime.1 hqH) j (by linarith)
      exact Finset.mem_sdiff.2 ⟨hAwake j q (by linarith) (by linarith [htime (Nat.le_succ j)]) hqj, hqj⟩
    exact ⟨kq, hkq'⟩
  have hsT : x.time (x.tickStep q (M.slotStart S.C (s₀' + 1))) ≤ tAwakeEnd := by
    rw [hkq]
    linarith
  have hRq : RootsNameBlocksUntil M A x (x.time (x.tickStep q (M.slotStart S.C (s₀' + 1)))) := by
    refine (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) ?_ hRoots
    rw [hkq]
    push_cast
    linarith
  have hmaxN : tGAT + max (Δ S) Δs ≤ tL + Δ S := by
    rcases max_choice (Δ S) Δs with hm | hm <;> rw [hm] <;> omega
  obtain ⟨-, hkt, hkt2⟩ := E.tick_active k u c hk'
  have hcRR : ((T₁ : ℕ) : ℝ) + 1 + Δ S ≤ (c : ℝ) := by exact_mod_cast (show T₁ + 1 + Δ S ≤ c by omega)
  have hc2R : (c : ℝ) ≤ ((M.supportCutoff S.C (s₀' + 1) : ℕ) : ℝ) := by exact_mod_cast hc2
  -- `u` is outside the adversary set at every step at a real time less than that of `k`
  have huT : ∀ j : ℕ, x.time j < x.time k → u ∉ A.corrupted j := fun j hj =>
    E.not_mem_corrupted_of_le (lt_of_not_ge fun hkj => (not_le.2 hj) (htime hkj)).le hu
  -- `u` is active from `tGAT` through the sync delay after it, a window that ends before `k`
  have hu₀ : u ∈ A.activeThroughout x tGAT (tGAT + Δs) := by
    refine Activity.mem_activeThroughout.2 (fun j h1 h2 => ?_)
    push_cast at h1
    have huj : u ∉ A.corrupted j := huT j (by linarith)
    exact Finset.mem_sdiff.2 ⟨hAwake j u (by linarith) h2 huj, huj⟩
  by_cases hcase : x.time k + Δ S ≤ ((M.slotStart S.C (s₀' + 1) : ℕ) : ℝ)
  · -- one delay before the later opening's slot
    have := (h_j_lt_of_later_proposal_st_upTo M F U Fx) S A x R GST tAwakeEnd tGAT s₀' k u q B₂ E hNet hSkew
      hRedeliver Sy hRq hParent hThird hsT hGST (by push_cast; linarith)
      (by rcases max_choice (Δ S) Δs with hm | hm <;> rw [hm] <;> omega) hcase hu₀ hu hq' hqv
      ⟨iB₂, hlB₂, hsentB₂⟩
    rw [hB₂h] at this
    exact this
  push_neg at hcase
  -- the reader's tick to `c₁`, before `k`
  obtain ⟨k₁, hk₁, hk₁a, hk₁b⟩ := E.tick_of_active c₁ (by omega) u fun j h1 h2 => by
    have huj : u ∉ A.corrupted j := huT j (by linarith)
    exact Finset.mem_sdiff.2 ⟨hAwake j u (by linarith) (by linarith [htime (Nat.le_succ j)]) huj, huj⟩
  have hc₁c : c₁ ≤ c := by
    have : ((c₁ : ℕ) : ℝ) ≤ (c : ℝ) := by linarith
    exact_mod_cast this
  have hk₁k : k₁ ≤ k := (tick_step_le_of_le M F) E hk₁ hk' hc₁c
  have huk₁ : u ∉ A.corrupted k₁ := E.not_mem_corrupted_of_le hk₁k hu
  have hF₁ : M.head_height_floor (x.st k₁ u) ≤ h := by
    have h1 := hF u c₁ k₁ hT₁c₁ (by omega) hk₁ huk₁
    have hT : x.tickInput u c₁ = x.st k₁ u := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hk₁]
    rw [hT] at h1
    exact h1
  have hFk : M.head_height_floor (x.st k u) ≤ h := by
    have h1 := hF u c k (by omega) hc2 hk' hu
    have hT : x.tickInput u c = x.st k u := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hk']
    rw [hT] at h1
    exact h1
  have hk₁s : x.time k₁ + Δ S ≤ ((M.slotStart S.C (s₀' + 1) : ℕ) : ℝ) := by linarith
  have hGt : ((tL : ℕ) : ℝ) ≤ x.time k₁ := by
    have : ((tL : ℕ) : ℝ) + Δ S = ((c₁ : ℕ) : ℝ) := by exact_mod_cast htL
    linarith
  rcases (h_j_lt_or_genesis_before_cutoff_st_upTo M F U Fx) S A x R GST tAwakeEnd tL s₀' h q B₂ E hNet hSkew hRedeliver
      Sy hRq hParent hThird (by omega) hsT tGAT hGST hmaxN (by omega) hAwake hqv ⟨iB₂, hlB₂, hsentB₂⟩ hB₂h u k₁ k
      hk₁k hGt hk₁s hu hu₀ hF₁ hFk
      (fun j hj1 hj2 => hNo' u j k₁ k c hk₁ hj1 hk' (le_trans hc2 hcs) hj2
        (E.not_mem_corrupted_of_le hj2.le hu)) with hlt | hg
  · exact hlt
  · obtain ⟨⟨D, -, hJD, hjD⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E k u
    by_contra hge
    have h1' : 1 ≤ (M.chainStateOf S.C D).h_j := by
      rw [← hjD]
      unfold Height at *
      omega
    have hJh := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).2.2 h1'
    rw [← hJD, hg] at hJh
    have hg1 : (M.chainStateOf S.C (Block.genesis : Block V)).h = 1 :=
      (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_genesis_h M F) S.C
    rw [hg1, ← hjD] at hJh
    unfold Height at *
    omega

/-- `quiet_waiting_same_entry_cutoff_upTo` when the later opening is the next one (`i' = i + 1`): its proposal `B₂`
extends `B` (`round89r`), so at the same height the two have one entry (Lemma 47 (e)). A theorem of its own so that
each proof stays within the default heartbeat budget.

The variables: as in `quiet_waiting_same_entry_cutoff_upTo`.

Restated with the delivery premises of `quiet_waiting_same_entry_cutoff_upTo` (the UpTo twin of `quiet_waiting_same_entry_next`).

Read aloud: a waiting quiet opening and the next one, at one height, have one entry. -/
theorem quiet_waiting_same_entry_next_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ r H₂ m i i' : ℕ) (rs : ℕ → ℕ)
    (B B₂ : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (aR M S r)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (aR M S r))
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
    (hT₁0 : T₁ + Δ S ≤ M.slotStart S.C (rs 0 * S.C.R - S.C.k - 1))
    (hii' : i < i') (hi' : i' < m) (hir' : rs (i' + 1) * S.C.R ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening M S A x rs m)
    (hNo : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C (rs (i + 1) * S.C.R) → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    (hNo' : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i' * S.C.R - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C (rs (i' + 1) * S.C.R) → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    {ΔNet_F : ℕ} (E_F : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.slotStart S.C (rs (i + 1) * S.C.R))) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S) {Δs_F : ℕ}
    (Sy_F : SyncedWithinUpTo A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST (M.slotStart S.C (rs (i + 1) * S.C.R)))
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- every validator outside the adversary set at the support cutoff of the slot after opening `i`'s first slot is
    -- active through the attestations' sync delay after the later of that first slot's duty window's start and `GST`
    -- (; the row `quiet_waiting_next_proposal_upTo` reads)
    (hHoldF : ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (rs i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hWait : ∀ B' : Block V, ProposalAt M S x (rs (i + 1) * S.C.R) B' →
      (M.chainStateOf S.C B').h ≤ (M.chainStateOf S.C B).h)
    (hTop : (M.chainStateOf S.C B).h ≤ H₂)
    (hB : ProposalAt M S x (rs i * S.C.R) B)
      (hB₂ : ProposalAt M S x (rs i' * S.C.R) B₂)
    (hi1 : i' = i + 1) :
    (M.chainStateOf S.C B).h = (M.chainStateOf S.C B₂).h →
      (M.chainStateOf S.C B).T_h = (M.chainStateOf S.C B₂).T_h := by
  intro hEq
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hAΔ : ΔClockAhead < Δ S := by linarith
  have hBΔ : ΔClockBehind < Δ S := by linarith
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hmono := r_lt_of_lt_of_mono rs m hSeq.mono
  have hri1 : rs (i + 1) ≤ rs i' := by
    rcases Nat.lt_or_ge (i + 1) i' with h | h
    · exact le_of_lt (hmono _ _ h (by omega))
    · have : i + 1 = i' := by omega
      rw [this]
  have hsR' : rs i' * S.C.R + S.C.R ≤ rs (i' + 1) * S.C.R := (opening_round_step M F) hSeq hi'
  have hir : rs (i + 1) * S.C.R ≤ r * S.C.R := by
    have := Nat.mul_le_mul_right S.C.R hri1
    omega
  -- the case of the next opening: `B₂` is the next proposal, and extends `B` (`round89r`)
  subst hi1
  obtain ⟨hs1, C⟩ := (quietCtx_of_upTo M F U) S A x R GST tGAT tAwakeEnd r m i rs (E.mono ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) hNet hSkew hRedeliver (Sy.mono ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) hΔs
    ((roots_cutoff_behind_of_aR M F U) S (by omega) E.ahead_nonneg hSkew hRoots) hParent hGST hThird hAwake
    hActive hCommittees hEnd hSeq (by omega) ((opening_round_step M F) hSeq (by omega)) hir hNoCol hNo
  have hB0 : ProposalAt M S x (rs i * S.C.R - 1 + 1) B := by rw [← hs1]; exact hB
  have h89 := (C.round89r M F R E U Fx) rfl B B₂ hB0 hB₂ E_F hNet_F hSkew_F Sy_F
    hΔs_F (fun v hv => by
      have hv' := (Finset.mem_sdiff.1 hv).2
      rw [← hs1] at hv' ⊢
      exact hHoldF v hv')
  exact ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B B₂).2.2.2.2 h89.1 hEq


/-- **The next proposal is in a reader's tree at its tick** (the delivery step of `quiet_waiting_same_entry_far_upTo`, a
theorem of its own so that each proof stays within the default heartbeat budget). The proposer of slot `s''` sends `B'`
at its tick `iP` to the start of slot `s''`, at least one delay after `tGAT`, and holds `B'` after that tick. A validator
`u`, outside the adversary set at its tick `k` to a clock value `c` at least the vote time of slot `s''`, at a real time
at most the action time of round `r`, whose finalized block is `B'` or an ancestor of `B'`, holds `B'` at `k`
(`proposal_held_at_later_tick_of_deadline`, the deadline of the send at most the action time of round `r`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`, `tGAT`, `tAwakeEnd`: the times;
  `r`: the round bounding the delivery premises; `s''`: the slot of `B'`; `iP`: the proposer's tick; `k`, `c`, `u`:
  the reader's tick, its clock value and the reader.

Read aloud: an honest reader whose finalized block is on the next proposal's chain has received that proposal by its
tick at or after the slot's vote time. -/
theorem waiting_far_proposal_held_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r s'' iP k c : ℕ) (B' : Block V) (u : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (aR M S r)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (hRoots : RootsNameBlocksUntil M A x (aR M S r))
    (hParent : ParentHeldAtDelivery M x)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hEnd : aR M S r ≤ tAwakeEnd) (hGST : GST ≤ tGAT)
    (hs'' : 1 ≤ s'') (hgs : tGAT + Δ S ≤ M.slotStart S.C s'') (hsA : M.slotStart S.C s'' + Δ S ≤ aR M S r)
    (hsv : M.slotStart S.C s'' + Δ S ≤ M.voteTime S.C s'')
    (hlP : x.lbl iP = Event.tick (S.P.proposer s'') (M.slotStart S.C s''))
    (hsentP : (⟨S.P.proposer s'', NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (iP + 1) - x.sent iP)
    (hBP : B' ∈ (x.st (iP + 1) (S.P.proposer s'')).tree)
    (hc1 : M.voteTime S.C s'' ≤ c) (hk' : x.lbl k = Event.tick u c) (hu : u ∉ A.corrupted k)
    (hTk : x.time k ≤ ((aR M S r : ℕ) : ℝ))
    (hFB' : (x.st k u).finalized.AncestorEq B') :
    B' ∈ (x.st k u).tree := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hs1'' : s'' - 1 + 1 = s'' := by omega
  have hTE : x.time k ≤ tAwakeEnd := by
    have : ((aR M S r : ℕ) : ℝ) ≤ (tAwakeEnd : ℝ) := by exact_mod_cast hEnd
    linarith
  -- the deadline of the proposer's send: at most the action time of round `r`, and `ΔClockAhead` before `c`
  have hTP1 := ((time_of_lbl_tick M) x R E hlP).2.2
  have hGs : ((GST : ℕ) : ℝ) ≤ ((M.slotStart S.C s'' : ℕ) : ℝ) := by
    exact_mod_cast (show GST ≤ M.slotStart S.C s'' by omega)
  have hmaxP : max (x.time (iP + 1)) ((GST : ℕ) : ℝ) ≤ ((M.slotStart S.C s'' : ℕ) : ℝ) + ΔClockBehind :=
    max_le hTP1 (by linarith)
  have hsAR : ((M.slotStart S.C s'' : ℕ) : ℝ) + Δ S ≤ ((aR M S r : ℕ) : ℝ) := by exact_mod_cast hsA
  have hcs : ((M.slotStart S.C s'' : ℕ) : ℝ) + Δ S ≤ (c : ℝ) := by exact_mod_cast (le_trans hsv hc1)
  refine (proposal_held_at_later_tick_of_deadline M F U) S A x R (s'' - 1) iP k c B' (S.P.proposer s'') u E hSkew
    hRedeliver ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hTk hRoots) hParent
    (by rw [hs1'']; exact hc1) hk' ?_ (by rw [hs1'']; exact hlP) hsentP hBP
    (GoldilocksCorrectness.Statements.AbstractTrace.deadlineUpTo_eq_some.2 ⟨by linarith, rfl⟩) (by linarith)
    ((compatible_iff _ _).2 (Or.inl hFB'))
  intro j h1 h2
  have hwj : u ∉ A.corrupted j := E.not_mem_corrupted_of_le h2 hu
  rw [hs1''] at h1
  have hgsR : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((M.slotStart S.C s'' : ℕ) : ℝ) := by exact_mod_cast hgs
  push_cast at hgsR
  refine Finset.mem_sdiff.2 ⟨hAwake j u (le_trans (htime h2) hTE) (by linarith [htime (Nat.le_succ j)]) hwj, hwj⟩

/-- `quiet_waiting_same_entry_cutoff_upTo` when the later opening is not the next one (`i' ≠ i + 1`): the route of
`quiet_rising_heights_differ_cutoff` through the next proposal `B'`, at `B`'s height and extending `B`
(`quiet_waiting_next_proposal`), with `h_j < h` at the readers' ticks from `waiting_h_j_lt_at_tick`. A theorem of
its own so that each proof stays within the default heartbeat budget.

The variables: as in `quiet_waiting_same_entry_cutoff_upTo`.

Restated with the delivery premises of `quiet_waiting_same_entry_cutoff_upTo` (the UpTo twin of `quiet_waiting_same_entry_far`).

Read aloud: a waiting quiet opening and a later one, not the next, at one height, have one entry. -/
theorem quiet_waiting_same_entry_far_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ r H₂ m i i' : ℕ) (rs : ℕ → ℕ)
    (B B₂ : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (aR M S r)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (aR M S r))
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
    (hT₁0 : T₁ + Δ S ≤ M.slotStart S.C (rs 0 * S.C.R - S.C.k - 1))
    (hii' : i < i') (hi' : i' < m) (hir' : rs (i' + 1) * S.C.R ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening M S A x rs m)
    (hNo : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C (rs (i + 1) * S.C.R) → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    (hNo' : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i' * S.C.R - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C (rs (i' + 1) * S.C.R) → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    {ΔNet_F : ℕ} (E_F : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.slotStart S.C (rs (i + 1) * S.C.R))) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S) {Δs_F : ℕ}
    (Sy_F : SyncedWithinUpTo A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST (M.slotStart S.C (rs (i + 1) * S.C.R)))
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- every validator outside the adversary set at the support cutoff of the slot after opening `i`'s first slot is
    -- active through the attestations' sync delay after the later of that first slot's duty window's start and `GST`
    -- (; the row `quiet_waiting_next_proposal_upTo` reads)
    (hHoldF : ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (rs i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hWait : ∀ B' : Block V, ProposalAt M S x (rs (i + 1) * S.C.R) B' →
      (M.chainStateOf S.C B').h ≤ (M.chainStateOf S.C B).h)
    (hTop : (M.chainStateOf S.C B).h ≤ H₂)
    (hB : ProposalAt M S x (rs i * S.C.R) B)
      (hB₂ : ProposalAt M S x (rs i' * S.C.R) B₂)
    (hi1 : ¬ i' = i + 1) :
    (M.chainStateOf S.C B).h = (M.chainStateOf S.C B₂).h →
      (M.chainStateOf S.C B).T_h = (M.chainStateOf S.C B₂).T_h := by
  intro hEq
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hAΔ : ΔClockAhead < Δ S := by linarith
  have hBΔ : ΔClockBehind < Δ S := by linarith
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hmono := r_lt_of_lt_of_mono rs m hSeq.mono
  have hri1 : rs (i + 1) ≤ rs i' := by
    rcases Nat.lt_or_ge (i + 1) i' with h | h
    · exact le_of_lt (hmono _ _ h (by omega))
    · have : i + 1 = i' := by omega
      rw [this]
  have hsR' : rs i' * S.C.R + S.C.R ≤ rs (i' + 1) * S.C.R := (opening_round_step M F) hSeq hi'
  have hir : rs (i + 1) * S.C.R ≤ r * S.C.R := by
    have := Nat.mul_le_mul_right S.C.R hri1
    omega
  -- the case of the next opening: `B₂` is the next proposal, and extends `B` (`round89r`)
  have hri : rs (i + 1) < rs i' := hmono _ _ (by omega) (by omega)
  have hsRi : rs i * S.C.R + S.C.R ≤ rs (i + 1) * S.C.R := (opening_round_step M F) hSeq (by omega)
  -- the next proposal `B'`, at `B`'s height, extending `B`
  obtain ⟨B', hB', hBB'a, hBB'e, hBq', hhlo, hhhi⟩ := (quiet_waiting_next_proposal_upTo M F U Fx) S A x R GST tGAT
    tAwakeEnd T₁ r H₂ m i rs B E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hT₁s hTick
    hThird hAwake hActive hCommittees hH₂ hOld hEnd hSeq hT₁0 (by omega) hir hNoCol hNo E_F hNet_F hSkew_F
    Sy_F hΔs_F hHoldF hWait hTop hB
  -- the two contexts
  obtain ⟨hs1, C⟩ := (quietCtx_of_upTo M F U) S A x R GST tGAT tAwakeEnd r m i rs (E.mono ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) hNet hSkew hRedeliver (Sy.mono ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) hΔs
    ((roots_cutoff_behind_of_aR M F U) S (by omega) E.ahead_nonneg hSkew hRoots) hParent hGST hThird hAwake
    hActive hCommittees hEnd hSeq (by omega) hsRi hir hNoCol hNo
  obtain ⟨hs1', C'⟩ := (quietCtx_of_upTo M F U) S A x R GST tGAT tAwakeEnd r m i' rs (E.mono ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) hNet hSkew hRedeliver (Sy.mono ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))) hΔs
    ((roots_cutoff_behind_of_aR M F U) S (by omega) E.ahead_nonneg hSkew hRoots) hParent hGST hThird hAwake
    hActive hCommittees hEnd hSeq hi' hsR' hir' hNoCol hNo'
  have hB₂0 : ProposalAt M S x (rs i' * S.C.R - 1 + 1) B₂ := by rw [← hs1']; exact hB₂
  set s₀ := rs i * S.C.R - 1 with hs₀def
  set s'' := rs (i + 1) * S.C.R with hs''def
  set s₀' := rs i' * S.C.R - 1 with hs₀'def
  set s₃ := rs (i' + 1) * S.C.R with hs₃def
  clear_value s₀ s'' s₀' s₃
  have hsR'2 := C'.sR
  have hs''s₀' : s'' + S.C.R ≤ s₀' + 1 := by
    have h' : (rs (i + 1) + 1) * S.C.R ≤ rs i' * S.C.R := Nat.mul_le_mul_right _ hri
    rw [Nat.add_mul, Nat.one_mul] at h'
    omega
  have hEnd' := (C'.cut_end M F)
  -- the times
  have hw0 := (C.win M F U) (le_refl (s₀ + 1))
  have hw0' := (C'.win M F U) (le_refl (s₀' + 1))
  have h0s : rs 0 * S.C.R ≤ s₀ + 1 := (C.rs0 M F)
  have hanc0 := hw0.2
  rw [anchorCW_eq] at hanc0
  have hte := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S
  have hssm : ∀ {a b : ℕ}, a ≤ b → M.slotStart S.C a ≤ M.slotStart S.C b := fun h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S h
  have hscm : ∀ {a b : ℕ}, a ≤ b → M.supportCutoff S.C a ≤ M.supportCutoff S.C b := fun h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h
  obtain ⟨hvA, hcA, -, hsA, -⟩ := hte (s₀ + 1 - S.C.k - 1)
  obtain ⟨hvB, hcB, -, hsB, -⟩ := hte (s'' - S.C.k - 1)
  obtain ⟨hv'', hc'', -, hs''1, -⟩ := hte s''
  obtain ⟨-, hcQ, -, hsQ, -⟩ := hte (s₀' + 1)
  obtain ⟨-, hcQ1, -, -, -⟩ := hte (s₀' + 1 + 1)
  obtain ⟨-, -, -, hs00, -⟩ := hte (rs 0 * S.C.R - S.C.k - 1)
  obtain ⟨-, hcS0, -, -, -⟩ := hte (s₀ + 1)
  have hmE := hssm (show s₀ + 1 - S.C.k - 1 ≤ s₀ + 1 by omega)
  have hmA := hssm (show s₀ + 1 - S.C.k - 1 + 1 ≤ s'' - S.C.k - 1 by omega)
  have hmB := hssm (show rs 0 * S.C.R - S.C.k - 1 + 1 ≤ s'' by omega)
  have hmC := hssm (show s₀ + 1 - S.C.k - 1 ≤ s'' by omega)
  have hmD := hssm (show s'' ≤ s₀' + 1 by omega)
  have hcR : M.supportCutoff S.C (s₀' + 1 + 1) ≤ aR M S r := by
    unfold aR
    exact hscm (by omega)
  have hT₁sl : T₁ + Δ S ≤ M.slotStart S.C (s₀' + 1 - S.C.k - 1) := by
    have h1 := hssm (show rs 0 * S.C.R - S.C.k - 1 ≤ s₀' + 1 - S.C.k - 1 by
      have := (C'.rs0 M F)
      omega)
    omega
  -- the climb's context
  have CC := (ClimbCtxUpTo.of_clock M F U R E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hT₁s hThird hAwake hH₂
    hOld hEnd hTick (by have := hscm (show s₀ + 1 ≤ r * S.C.R by omega); omega))
  set h := (M.chainStateOf S.C B).h with hhdef
  clear_value h
  have hh : h + 1 = H₂ ∨ h = H₂ := by
    unfold Height at *
    omega
  have hB₂h : (M.chainStateOf S.C B₂).h = h := hEq.symm
  -- at the height `1` the entry is the genesis block
  by_cases hh1 : h ≤ 1
  · have hb1 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B B).1.1
    have hb2 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B₂ B₂).1.1
    have hg := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_genesis_h M F) S.C
    have g1 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C
      (Block.genesis : Block V) B).2.2.2.2 (genesis_ancestorEq B) (by rw [hg, ← hhdef]; unfold Height at *; omega)
    have g2 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C
      (Block.genesis : Block V) B₂).2.2.2.2 (genesis_ancestorEq B₂) (by rw [hg, hB₂h]; unfold Height at *; omega)
    rw [← g1, ← g2]
  -- no tick of an honest validator from `T₁ + 1 + Δ S` to the later opening's support cutoff starts from a
  -- `head_height_floor` greater than `h`
  have hF := (floor_le_before_quiet_tick_from_upTo M F U Fx) R E CC C' hT₁sl h hh B₂ hB₂0 hB₂h
    (le_trans ((stepBefore_mono M) x R E ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show s₀' + 1 ≤ r * S.C.R by omega))) (Nat.sub_le _ _))
  -- what a tick from the vote time of slot `s''` to the later opening's support cutoff reads
  have hRd : ∀ (u : V) (c kt : ℕ), M.voteTime S.C s'' ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl kt = Event.tick u c → u ∉ A.corrupted kt →
      x.tickInput u c = x.st kt u ∧ M.head_height_floor (x.st kt u) ≤ h ∧
        hMax M S.C (x.st kt u) ≤ h + 1 ∧ (x.st kt u).justifiedHeight ≤ h ∧
        x.time kt ≤ ((aR M S r : ℕ) : ℝ) ∧ M.nodeInv S.C S.P S.X (x.st kt u) := by
    intro u c kt hc1 hc2 hkt hukt
    have hTu : x.tickInput u c = x.st kt u := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hkt]
    have hfu := hF u c kt (by omega) hc2 hkt hukt
    rw [hTu] at hfu
    have hinv := (lem11_node_invariant M F S A x R E kt u hukt).1
    have hmx := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_le_floor_add_one M F) S.C S.P S.X _ hinv
    have hjl := (h_j_lt_h_max_st M F) S A x R E kt u
    have hkt2 := (E.tick_active kt u c hkt).2.2
    have hTa : ((M.supportCutoff S.C (s₀' + 1) : ℕ) : ℝ) + Δ S ≤ ((aR M S r : ℕ) : ℝ) := by
      exact_mod_cast (show M.supportCutoff S.C (s₀' + 1) + Δ S ≤ aR M S r by omega)
    have hc2R : (c : ℝ) ≤ ((M.supportCutoff S.C (s₀' + 1) : ℕ) : ℝ) := by exact_mod_cast hc2
    refine ⟨hTu, hfu, by unfold Height at *; omega, by unfold Height at *; omega, by linarith, hinv⟩
  -- the later opening's proposer, honest to its slot's support cutoff
  have e₀' : rs i' * S.C.R = s₀' + 1 := by omega
  have hqH : S.P.proposer (s₀' + 1) ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀' + 1)) := by
    have h' := hSeq.honest i' (le_of_lt hi')
    rw [e₀'] at h'
    exact h'
  have hμeq : rs i' * S.C.R - S.C.k - 1 = s₀' + 1 - S.C.k - 1 := by omega
  rw [hμeq] at hNo'
  obtain ⟨iB₂, hlB₂, hsentB₂⟩ := id hB₂0
  -- no validator outside the adversary set at a tick from the vote time of slot `s''` to the later opening's
  -- support cutoff has `h_j` at least `h` there
  have hJlt : ∀ (u : V) (c k : ℕ), M.voteTime S.C s'' ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl k = Event.tick u c → u ∉ A.corrupted k →
      (x.st k u).justifiedHeight < h := by
    have hR' : RootsNameBlocksUntil M A x ((M.slotStart S.C (s₀' + 1) + Δ S : ℕ) : ℝ) :=
      (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
        (by exact_mod_cast (show M.slotStart S.C (s₀' + 1) + Δ S ≤ aR M S r by omega)) hRoots
    have hcs : M.supportCutoff S.C (s₀' + 1) ≤ M.supportCutoff S.C s₃ := hscm (by omega)
    have hEndN : M.supportCutoff S.C (s₀' + 1) + Δ S ≤ tAwakeEnd := by unfold aR at hcR hEnd; omega
    have hT₁cR : T₁ + 1 + Δ S ≤ M.voteTime S.C s'' := by omega
    have hh2 : 2 ≤ h := by unfold Height at *; omega
    obtain ⟨f1, f2, f3, f4, f5, f6⟩ := (waiting_slot_facts M F U) S s₀' T₁ tGAT Δs hT₁sl hT₁s
    have hsaR : M.slotStart S.C (s₀' + 1) ≤ aR M S r := by omega
    exact (waiting_h_j_lt_at_tick_upTo M F U Fx) S A x R GST tGAT tAwakeEnd T₁ s₀'
      (M.slotStart S.C (s₀' + 1 - S.C.k - 1)) (M.voteTime S.C (s₀' + 1 - S.C.k - 1)) (M.voteTime S.C s'')
      (M.supportCutoff S.C s₃) h (S.P.proposer (s₀' + 1)) B₂ (E.mono hsaR) hNet hSkew hRedeliver (Sy.mono hsaR) hR'
      hParent hThird hAwake hGST hT₁s f1 f2 hT₁sl f3 hT₁cR hcs hEndN f4 f5 f6 hqH ⟨iB₂, hlB₂, hsentB₂⟩ hB₂h hh2
      hF hNo'
  -- `head_height_floor` at those ticks is at most `B'`'s chain-state height
  have hFl : ∀ (u : V) (c k : ℕ), M.voteTime S.C s'' ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl k = Event.tick u c → u ∉ A.corrupted k →
      M.head_height_floor (x.tickInput u c) ≤ (M.chainStateOf S.C B').h := by
    intro u c k hc1 hc2 hk' hu
    obtain ⟨hTu, hfu, -⟩ := hRd u c k hc1 hc2 hk' hu
    rw [hTu]
    unfold Height at *
    omega
  -- an honest holder of `B'` at those ticks, outside the adversary set one delay after, has its root on `B'`'s chain
  have hRootB' : ∀ (u : V) (c k : ℕ), M.voteTime S.C s'' ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl k = Event.tick u c → u ∉ A.corrupted k → u ∉ A.corruptedAtTime x (x.time k + Δ S) →
      B' ∈ (x.tickInput u c).tree → (M.get_fc_root (x.tickInput u c)).AncestorEq B' := by
    intro u c k hc1 hc2 hk' hu _huΔ hB'u
    obtain ⟨hTu, hfu, hmx, hjl, hTk, hinv⟩ := hRd u c k hc1 hc2 hk' hu
    have hjh := hJlt u c k hc1 hc2 hk' hu
    rw [hTu] at hB'u ⊢
    have hBh := le_hMax M (C := S.C) hB'u
    have hTE : x.time k ≤ tAwakeEnd := by
      have : ((aR M S r : ℕ) : ℝ) ≤ (tAwakeEnd : ℝ) := by exact_mod_cast hEnd
      linarith
    have hFB' : (x.st k u).finalized.AncestorEq B' :=
      (F_ancestorEq_of_high_st M F Fx) S A x R E hRoots tAwakeEnd k k u u B' hThird hTE hTE hu hu hB'u
        (by unfold Height at *; omega) (max_le hTk hTk)
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X (x.st k u) hinv with ⟨hJ, hm1, hc⟩ | ⟨hFr, -⟩
    · rw [hJ]
      by_contra hJB
      have hct := (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_true_of M F) S.C S.P S.X
        (x.st k u) hinv B' hm1 hB'u hFB' (by unfold Height at *; omega) hJB
      rw [hc] at hct
      cases hct
    · rw [hFr]
      exact hFB'
  -- `B'` is in the tree at those ticks
  obtain ⟨iP, hlP, hsentP⟩ := hB'
  have hBP : B' ∈ (x.st (iP + 1) (S.P.proposer s'')).tree := by
    have : x.tickOutput (S.P.proposer s'') (M.slotStart S.C s'') = x.st (iP + 1) (S.P.proposer s'') := by
      unfold Trace.tickOutput
      rw [(tickStep_eq_of_lbl M) x E hlP]
    rw [← this]
    exact hBq'
  have hgs'' : tGAT + Δ S ≤ M.slotStart S.C s'' := by omega
  have hsA'' : M.slotStart S.C s'' + Δ S ≤ aR M S r := by omega
  have hsv'' : M.slotStart S.C s'' + Δ S ≤ M.voteTime S.C s'' := by omega
  have hs''1 : 1 ≤ s'' := by omega
  have hDel : ∀ (u : V) (c k : ℕ), M.voteTime S.C s'' ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl k = Event.tick u c → u ∉ A.corrupted k → u ∉ A.corruptedAtTime x (x.time k + Δ S) →
      B' ∈ (x.tickInput u c).tree := by
    intro u c k hc1 hc2 hk' hu _huΔ
    obtain ⟨hTu, -, -, -, hTk, -⟩ := hRd u c k hc1 hc2 hk' hu
    have hjh := hJlt u c k hc1 hc2 hk' hu
    rw [hTu]
    have hp1 := E.not_mem_corrupted_succ_of_tick hlP
    have hTP : x.time (iP + 1) ≤ x.time k := by
      have h1 := ((time_of_lbl_tick M) x R E hlP).2.2
      have h2 := (E.tick_active k u c hk').2.1
      have h3 : ((M.slotStart S.C s'' : ℕ) : ℝ) + Δ S ≤ (c : ℝ) := by exact_mod_cast (le_trans hsv'' hc1)
      linarith
    have hTE : x.time k ≤ tAwakeEnd := by
      have : ((aR M S r : ℕ) : ℝ) ≤ (tAwakeEnd : ℝ) := by exact_mod_cast hEnd
      linarith
    have hFB' : (x.st k u).finalized.AncestorEq B' :=
      (F_ancestorEq_of_high_st M F Fx) S A x R E hRoots tAwakeEnd k (iP + 1) u (S.P.proposer s'') B' hThird hTE
        (le_trans hTP hTE) hu hp1 hBP (by unfold Height at *; omega) (max_le hTk (le_trans hTP hTk))
    exact (waiting_far_proposal_held_upTo M F U) S A x R GST tGAT tAwakeEnd r s'' iP k c B' u E hNet hSkew hRedeliver
      hRoots hParent hAwake hEnd hGST hs''1 hgs'' hsA'' hsv'' hlP hsentP hBP hc1 hk' hu hTk hFB'
  -- the finalized block at those ticks, of a validator outside the adversary set at the tick alone: the
  -- chain state of a block `D` the reader holds finalized it (`finalizedFromChain_of_exec`); when that finalization
  -- height is less than `B'`'s chain-state height, Lemma 68 at the reader's tick and the proposer's step after its tick
  -- makes it `B'` or an ancestor of `B'`; otherwise `D`'s chain state has `h_j` at least `h`, and so has the reader at
  -- its tick (`h_j_of_mem_T_of_exec`), against `hJlt`
  have hFin : ∀ (u : V) (c k : ℕ), M.voteTime S.C s'' ≤ c → c ≤ M.supportCutoff S.C (s₀' + 1) →
      x.lbl k = Event.tick u c → u ∉ A.corrupted k → (x.tickInput u c).finalized.compatible B' = true := by
    intro u c k hc1 hc2 hk' hu
    obtain ⟨hTu, -, -, -, hTk, -⟩ := hRd u c k hc1 hc2 hk' hu
    rw [hTu]
    obtain ⟨D, hD, hFD⟩ := (finalizedFromChain_of_exec M F) S A x R E k u
    by_cases hlt : (M.chainStateOf S.C D).h_F < (M.chainStateOf S.C B').h
    · have hp1 := E.not_mem_corrupted_succ_of_tick hlP
      have hTP1 : x.time (iP + 1) ≤ ((aR M S r : ℕ) : ℝ) := by
        have h1 := ((time_of_lbl_tick M) x R E hlP).2.2
        have h2 : ((M.slotStart S.C s'' : ℕ) : ℝ) + Δ S ≤ ((aR M S r : ℕ) : ℝ) := by
          exact_mod_cast (show M.slotStart S.C s'' + Δ S ≤ aR M S r by omega)
        linarith
      have hmax : max (x.time k) (x.time (iP + 1)) ≤ ((aR M S r : ℕ) : ℝ) := max_le hTk hTP1
      have hEndR : ((aR M S r : ℕ) : ℝ) ≤ (tAwakeEnd : ℝ) := by exact_mod_cast hEnd
      rw [hFD, compatible_iff]
      exact Or.inl ((lem68_honest_past_finalized M F Fx) S A x R E hRoots k (iP + 1) u (S.P.proposer s'') D B'
        (hThird.mono (le_trans hmax hEndR)) hu hp1 hD hBP hlt hmax)
    push_neg at hlt
    exfalso
    have hjh := hJlt u c k hc1 hc2 hk' hu
    have hf1 : 1 ≤ (M.chainStateOf S.C D).h_F := by unfold Height at *; omega
    have hFanc : (M.chainStateOf S.C D).F.AncestorEq D :=
      (((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).2.2 hf1).2.2.1
    have hjD := (GoldilocksCorrectness.Record.Statements.Executions.h_j_of_mem_T_of_exec M F) S A x R E k u D hD
      (by rw [hFD]; exact hFanc)
    have h47 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C D D).1
    unfold Height at *
    omega
  -- no change from a validator's own tick to the vote time of slot `s'' − k − 1` to before its ticks to clock values
  -- at most the support cutoff of slot `s''`: the window of opening `i` read from a later start
  have hNo'' := (noChange_tick_start_later M F) R E hSkew hAwake (tGAT := tGAT) (tAwakeEnd := tAwakeEnd)
    (c₀ := M.voteTime S.C (s₀ + 1 - S.C.k - 1)) (c₁ := M.voteTime S.C (s'' - S.C.k - 1))
    (by omega) (by omega) (by have := hscm (show s₀ + 1 ≤ r * S.C.R + 1 by omega); unfold aR at hEnd; omega)
    (by rw [show s₀ + 1 = rs i * S.C.R by omega]; exact hNo)
  -- the shared part: `B'` is an ancestor of `B₂`'s parent
  have hB'P₂ := (next_proposal_ancestorEq_later_parent_upTo M F U Fx) S A x R GST tGAT tAwakeEnd T₁ r m i i' s'' s₀' s₃ rs B' B₂
    E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hT₁s hTick hThird hAwake hActive hCommittees hEnd hSeq hT₁0
    hs''def hs₀'def (by omega) hi' hri (by omega) hir' hNoCol hNo'' ⟨iP, hlP, hsentP⟩ hB₂
    (fun u c k h1 h2 h3 h4 _ => hFl u c k h1 h2 h3 h4) hRootB' hDel hFin
  obtain ⟨-, -, hB₂par?, -⟩ := (proposal_parent_walk_end M F U) S A x R E s₀' iB₂ B₂ _ hlB₂ hsentB₂
  have hPB₂ := GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_parent? hB₂par?
  have hBB₂ := ancestorEq_trans hBB'a (ancestorEq_trans hB'P₂ hPB₂)
  exact ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B B₂).2.2.2.2 hBB₂
    (by rw [← hhdef, hB₂h])


/-- **Two waiting quiet openings at one height share the height's entry** (probe copy of
`quiet_rising_heights_differ_cutoff`). The route of the copy, with the next proposal `B'` after `B`
at `B`'s height `h`: no honest validator has `h_j ≥ h` before the later opening's support cutoff
(`h_j_lt_or_genesis_before_cutoff`), so the root step and the delivery step of the copy go
through, and `B'` is an ancestor of `B₂`: the two have one entry (Lemma 47 (e)).

The threshold time `T₁` may be as late as one delay before the start of slot
`rs 0 * R − k − 1`, in place of at most the start of slot
`rs 0 * R − 2k`: the climb takes `T₁` three delays later so that the first honest
attestation above the threshold comes at a round whose slot `r * R + 1` starts at or after the
committee premise's anchor. The proof reads `hT₁0` only to bound `T₁ + Δ` by
the start of a later slot.

Roots name blocks until `aR M S r`: the climb's context `ClimbCtx` carries the premise at the action
time of round `r`; the honest round opening slots' contexts `QuietCtx` read up to support cutoffs of
slots at most `r * R`, before it.

Restated with the delivery premises up to `aR M S r`: the bound of its roots `hRoots`, the bundle
`ClimbCtxUpTo`'s; the honest round opening slots' bundles `QuietCtxUpTo` read up to support cutoffs
of slots at most `r * R`, before it; the attestations (`hSyncF`, `hCatchF`) up to
`M.slotStart S.C (rs (i + 1) * S.C.R)`, the bound
`QuietCtxUpTo.round89r` reads them at for
the next opening.

The variables:
- `M`: the model; `F`: its facts.

Restated: takes `hHoldF`, the holder row of opening `i`'s first
slot that `quiet_waiting_next_proposal_upTo` and `round89r` read; the body is the split of
`quiet_waiting_same_entry_cutoff` (`quiet_waiting_same_entry_next_upTo`, `quiet_waiting_same_entry_far_upTo`).

Read aloud: two quiet openings waiting at one height wait on the same entry, with the delivery
premises up to the action time of round `r` (those of the FG messages up to the start of slot
`rs (i + 1) * R`). -/
theorem quiet_waiting_same_entry_cutoff_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ r H₂ m i i' : ℕ) (rs : ℕ → ℕ)
    (B B₂ : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (aR M S r)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (aR M S r))
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
    (hT₁0 : T₁ + Δ S ≤ M.slotStart S.C (rs 0 * S.C.R - S.C.k - 1))
    (hii' : i < i') (hi' : i' < m) (hir' : rs (i' + 1) * S.C.R ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening M S A x rs m)
    (hNo : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C (rs (i + 1) * S.C.R) → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    (hNo' : ∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i' * S.C.R - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C (rs (i' + 1) * S.C.R) → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    {ΔNet_F : ℕ} (E_F : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.slotStart S.C (rs (i + 1) * S.C.R))) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S) {Δs_F : ℕ}
    (Sy_F : SyncedWithinUpTo A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST (M.slotStart S.C (rs (i + 1) * S.C.R)))
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- every validator outside the adversary set at the support cutoff of the slot after opening `i`'s first slot is
    -- active through the attestations' sync delay after the later of that first slot's duty window's start and `GST`
    -- (; the row `quiet_waiting_next_proposal_upTo` reads)
    (hHoldF : ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (rs i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hWait : ∀ B' : Block V, ProposalAt M S x (rs (i + 1) * S.C.R) B' →
      (M.chainStateOf S.C B').h ≤ (M.chainStateOf S.C B).h)
    (hTop : (M.chainStateOf S.C B).h ≤ H₂)
    (hB : ProposalAt M S x (rs i * S.C.R) B)
      (hB₂ : ProposalAt M S x (rs i' * S.C.R) B₂) :
    (M.chainStateOf S.C B).h = (M.chainStateOf S.C B₂).h →
      (M.chainStateOf S.C B).T_h = (M.chainStateOf S.C B₂).T_h := by
  by_cases hi1 : i' = i + 1
  · exact (quiet_waiting_same_entry_next_upTo M F U Fx) S A x R GST tGAT tAwakeEnd T₁ r H₂ m i i' rs B B₂ E hNet hSkew hRedeliver Sy hΔs hRoots hParent
      hGST hT₁s hTick hThird hAwake hActive hCommittees hH₂ hOld hEnd hSeq hT₁0 hii' hi' hir' hNoCol hNo hNo' E_F
      hNet_F hSkew_F Sy_F hΔs_F hHoldF hWait hTop hB hB₂ hi1
  · exact (quiet_waiting_same_entry_far_upTo M F U Fx) S A x R GST tGAT tAwakeEnd T₁ r H₂ m i i' rs B B₂ E hNet hSkew hRedeliver Sy hΔs hRoots hParent
      hGST hT₁s hTick hThird hAwake hActive hCommittees hH₂ hOld hEnd hSeq hT₁0 hii' hi' hir' hNoCol hNo hNo' E_F
      hNet_F hSkew_F Sy_F hΔs_F hHoldF hWait hTop hB hB₂ hi1

end GoldilocksCorrectness.Record.Proofs.Executions

