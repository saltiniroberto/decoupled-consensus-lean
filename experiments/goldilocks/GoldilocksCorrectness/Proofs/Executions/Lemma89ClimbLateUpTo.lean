module
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

@[expose] public section

/-!
# `Lemma89ClimbLate.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89ClimbLate.lean` that name a
delivery premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the
deadlines. The bound of
each twin is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in
the twin's own parameters.

* `quiet_rising_next_proposal_late`, `quiet_straddler_heights`,
  `quiet_rising_heights_differ_cutoff`, `quiet_rising_before_fast_round_le_two_cutoff`,
  `quiet_waiting_next_proposal`, `quiet_waiting_same_entry_cutoff`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart anchorCW)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_voteTime dutyWindowStart_mono
  dutyWindowStart_of_anchor one_le_Δ proposalWindowStart_eqJ slotStart_eq slotStart_mono
  supportCutoff_eq supportCutoff_lt_of_lt supportCutoff_mono viewFreeze_eq voteTime_eq voteTime_mono
  voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_J_spec chainStateOf_height_mono
  lem47_chain_state_heights)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (fg_contest_true_of h_max_le_floor_add_one
  h_max_sub_one_le_floor mem_fg_to_ac_tree mem_viable_heads_iff root_cases)

open GoldilocksCorrectness.Proofs.Routines (get_anchor_cases_locked)

open GoldilocksCorrectness.Proofs.Routines (anchorCW_eq is_live_iff)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_genesis_h fc_root_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq ancestorEq_compatible ancestorEq_antisymm ancestorEq_genesis_iff)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
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
`h_max` at least `H₂` (B2), so `H₂ ≤ h(B) + 1`.

The copy with the threshold time `T₁` up to one delay before the start of slot
`rs 0 * R − k − 1`: the landed form asks `T₁` at most the start of
slot `rs 0 * R − 2k`, and the climb takes `T₁` three delays later so that the first honest
attestation above the threshold comes at a round whose slot `r * R + 1` starts at or after the
committee premise's anchor. The proof is unchanged: it reads `hT₁0` only to bound `T₁ + Δ` by
the start of a later slot.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `H₂`: the threshold; `m`: the index of the last honest round opening slot; `i`: the index of an honest round opening slot; `rs`: the rounds of the honest round opening slots;
  `B`: its proposal.

Roots name blocks until `aR S r`: the climb's context `ClimbCtx` carries the premise at the action
time of round `r`; the honest round opening slots' contexts `QuietCtx` read up to support cutoffs of
slots at most `r * R`, before it.

Restated with the delivery premises up to `aR S r`: the bound of its roots `hRoots`, the bundle `ClimbCtxUpTo`'s; the honest round opening slots' bundles `QuietCtxUpTo` read up to support cutoffs of slots at most `r * R`, before it. -/
theorem quiet_rising_next_proposal_late_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd T₁ r H₂ m i : ℕ) (rs : ℕ → ℕ)
    (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (aR S r))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (aR S r))
    (hRoots : RootsNameBlocksUntil S Sched x (aR S r))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT) (hT₁ : tGAT ≤ T₁)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hH₂ : OldHeightAttained S Sched x T₁ H₂)
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hEnd : aR S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hT₁0 : T₁ + Δ S ≤ slotStart S (rs 0 * S.C.R - S.C.k - 1))
    (hi : i < m) (hir : rs (i + 1) * S.C.R ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening S Sched x rs m)
    (hNo : ∀ (w : V) (t' : ℕ), voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' →
      t' < supportCutoff S (rs (i + 1) * S.C.R) → w ∉ Sched.adv (t' : Int) →
      ¬ ForkChoiceChangeAt S Sched x w t')
    (hRise : RisingAt S Sched x rs i)
    (hB : ProposalAt S Sched x (rs i * S.C.R) B) :
    ∃ B' : Block V, ProposalAt S Sched x (rs (i + 1) * S.C.R) B' ∧
      (chainStateOf S.C B).h < (chainStateOf S.C B').h ∧
      B' ∈ (stateBefore x (slotStart S (rs (i + 1) * S.C.R) + 1)
        (S.P.proposer (rs (i + 1) * S.C.R))).S.T ∧
      H₂ ≤ (chainStateOf S.C B).h + 1 ∧ (chainStateOf S.C B).h ≤ H₂ := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  obtain ⟨hs1, C⟩ := quietCtx_of_upTo S Sched x GST tGAT tAwakeEnd r m i rs hDiv hMono
    (hSync.mono (supportCutoff_mono S (by omega))) (hCatch.mono (supportCutoff_mono S (by omega)))
    (hRoots.mono (supportCutoff_mono S (by omega))) hParent hOwner hU hGST hThird hAwake
    hCommittees hEnd hSeq hi
    (opening_round_step hSeq hi) hir hNoCol hNo
  have hB0 : ProposalAt S Sched x (rs i * S.C.R - 1 + 1) B := by rw [← hs1]; exact hB
  have hRise' := hRise
  set s₀ := rs i * S.C.R - 1 with hs₀def
  set s'' := rs (i + 1) * S.C.R with hs''def
  clear_value s₀ s''
  have hsR := C.sR
  have hEnd' := C.cut_end
  have CC : ClimbCtxUpTo S Sched x GST tGAT tAwakeEnd T₁ r H₂ :=
    ⟨hDiv, hMono, hSync, hCatch, hRoots, hParent, hU, hGST, hT₁, hThird, hAwake, hH₂,
      hOld, hEnd⟩
  -- the times
  have hw0 := C.win (le_refl (s₀ + 1))
  have h0s : rs 0 * S.C.R ≤ s₀ + 1 := C.rs0
  have hT₁s₀ : T₁ + Δ S ≤ slotStart S (s₀ + 1 - S.C.k - 1) := by
    have h1 := slotStart_mono S (show rs 0 * S.C.R - S.C.k - 1 ≤ s₀ + 1 - S.C.k - 1 by
      omega)
    have h2 : slotStart S (rs 0 * S.C.R - 2 * S.C.k + 1) =
        slotStart S (rs 0 * S.C.R - 2 * S.C.k) + 4 * Δ S := by
      rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
    omega
  have hss'' : slotStart S (s'' - 1 + 1) = slotStart S s'' := by rw [show s'' - 1 + 1 = s'' by omega]
  have hssμ := slotStart_mono S (show s₀ + 1 - S.C.k - 1 ≤ s'' by omega)
  have hvs'' := voteTime_eq S s''
  have hcs'' := supportCutoff_eq S s''
  have hanc0 := hw0.2
  rw [anchorCW_eq] at hanc0
  -- the next proposal `B'`
  have hqH : S.P.proposer s'' ∉ Sched.adv ((supportCutoff S s'' : ℕ) : Int) := by
    have h := hSeq.honest (i + 1) (by omega)
    rw [hs''def]
    exact h
  have hqAH : ∀ t : ℕ, tGAT ≤ t → t ≤ supportCutoff S s'' →
      S.P.proposer s'' ∈ Sched.awake (t : Int) ∧ S.P.proposer s'' ∉ Sched.adv (t : Int) := by
    intro t h1 h2
    have hq' : S.P.proposer s'' ∉ Sched.adv (t : Int) :=
      fun hh => hqH (hMono _ _ (by exact_mod_cast h2) hh)
    exact ⟨hAwake t h1 (le_trans h2 (le_trans (supportCutoff_mono S (by omega)) hEnd'))
      _ hq', hq'⟩
  have hs''2 : s'' - 2 + 2 = s'' := by omega
  have hpw := proposalWindowStart_eqJ S (s'' - 2)
  have hA21 : anchorCW S tGAT ≤ slotStart S (s'' - 2 + 1 + 1) := by
    rw [show s'' - 2 + 1 + 1 = s'' by omega]
    exact le_trans hw0.2 hssμ
  have hdwA := dutyWindowStart_of_anchor S tGAT (s'' - 2 + 1) hA21
  obtain ⟨iB', B', hl', hsent'⟩ := honest_proposer_proposesJ S Sched x (s'' - 2) hDiv hMono
    (by
      intro t h1 h2
      rw [hpw] at h1
      rw [hs''2] at h2 ⊢
      exact hqAH t (by omega) (by omega))
  rw [hs''2] at hl' hsent'
  have hB' : ProposalAt S Sched x s'' B' := ⟨iB', hl', hsent'⟩
  have hBB' := hRise B B' hB (by rw [← hs''def]; exact hB')
  -- the proposer of `B'` holds it
  have hB'0 : ProposalAt S Sched x (s'' - 1 + 1) B' := by
    rw [show s'' - 1 + 1 = s'' by omega]
    exact hB'
  have hPV' := proposal_parent_viable_head S Sched x (s'' - 1) B' _ hB'0
  have hPV'' := (mem_viable_heads_iff _ _).1 hPV'
  obtain ⟨iB'', hlB'', hsentB''⟩ := hB'0
  obtain ⟨-, -, hB'par?, -⟩ := proposal_parent_walk_end S Sched x (s'' - 1) iB'' B' _
    hlB'' hsentB''
  have hPB' := GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_parent? hB'par?
  have hRootNew' : ∀ B₁ ∈ (stateBefore x (slotStart S (s'' - 1 + 1)) (S.P.proposer (s'' - 1 + 1))).S.T,
      B₁.root ≠ B'.root := by
    intro B₁ hB₁ heq
    apply hNoCol
    rw [GoldilocksCorrectness.Proofs.View.rootCollisionAtOpening_unfold]
    refine ⟨i + 1, by omega, B', ?_, ?_⟩
    · rw [← hs''def]
      exact hB'
    · rw [← hs''def]
      rw [GoldilocksCorrectness.Proofs.View.rootCollisionAtProposal_unfold]
      show ∃ B₁ ∈ (stateBefore x (slotStart S s'') (S.P.proposer s'')).S.T, B₁.root = B'.root
      rw [show s'' - 1 + 1 = s'' by omega] at hB₁
      exact ⟨B₁, hB₁, heq⟩
  have hBq := lem22a_proposer_holds_own_proposal S Sched x (s'' - 1) iB'' B' _ hDiv hMono hlB''
    hsentB'' hRootNew' hPV''.1
    ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans hPV''.2.1 hPB')))
  have hti := (time_of_lbl_tickAllAwake x hlB'').2
  have hBq' : B' ∈ (stateBefore x (slotStart S s'' + 1) (S.P.proposer s'')).S.T := by
    have hle : iB'' + 1 ≤ stepBefore x (slotStart S s'' + 1) :=
      (time_lt_iff_le_stepBefore x hDiv (by omega)).1 (by rw [hti, hss'']; omega)
    have h' := mem_T_mono x _ hle hBq
    rw [show s'' - 1 + 1 = s'' by omega] at h'
    exact h'
  -- the heights
  have haR : slotStart S s'' + 1 ≤ aR S r := by
    have h1 := supportCutoff_mono S (show s'' ≤ r * S.C.R + 1 by omega)
    unfold aR
    omega
  have hB'top := held_height_le_before_action S Sched x tAwakeEnd r H₂ (slotStart S s'' + 1) _ B' hU
    hThird hOld haR hEnd hBq'
  have hcl2 := C.clause2 B hB0
  have hA2 : anchorCW S tGAT ≤ slotStart S (s₀ + 1 + 1) :=
    le_trans hw0.2 (slotStart_mono S (by omega))
  have hMaj1 := committee_majority_of_committeeSleepiness S Sched _ (s₀ + 1) hCommittees hA2
  obtain ⟨v₀, hv₀⟩ : (S.P.committee (s₀ + 1) ∩ roundMembers S Sched (s₀ + 1 + 1)).Nonempty :=
    Finset.card_pos.1 (by omega)
  have hv₀H : v₀ ∈ Hon S Sched (s₀ + 1) := (Finset.mem_inter.1 hv₀).2
  have hv₀b : v₀ ∉ Sched.adv ((supportCutoff S (s₀ + 1 + 1) : ℕ) : Int) := (Finset.mem_sdiff.1 hv₀H).2
  have hsc₀2 := supportCutoff_eq S (s₀ + 1 + 1)
  have hv₀2 := voteTime_eq S (s₀ + 1 + 1)
  have hss₀1 : slotStart S (s₀ + 1 + 1) = slotStart S (s₀ + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s₀ + 1), Nat.mul_add, Nat.mul_one]
  have hss₀μ := slotStart_mono S (show s₀ + 1 - S.C.k - 1 ≤ s₀ + 1 by omega)
  have hbnd := CC.bounds (t := supportCutoff S (s₀ + 1 + 1)) (w := v₀) (by omega)
    (by unfold aR; exact supportCutoff_mono S (by omega)) hv₀b
  have hflv := h_max_sub_one_le_floor (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v₀).S
  have hfl2 := (hcl2 v₀ hv₀H).2
  refine ⟨B', hB', hBB', hBq', ?_, ?_⟩
  · unfold Height at *
    omega
  · unfold Height at *
    omega

/-- **The quiet honest round opening slot whose round holds `r * R` proposes at height `H₂ − 1` or
`H₂`.** The proof; the audited statement is in `Statements/Executions/Lemma89Statements.lean`.

The route: the context `QuietCtx` with the end `s'' := r * R` (`quietCtx_of`). The
upper bound: were the proposal `B` above `H₂`, `quiet_top_gives_attestation_cutoff` at `s'' := r * R`
gives an honest attestation above `H₂` at a time at most `aR S (rs i) < aR S r`, against `hOld`.
The lower bound, as in `quiet_rising_next_proposal_late`: a committee member `v₀` of slot `rs i * R`
honest at the support cutoff of the next slot has `head_height_floor` at most `h(B)` (the round's
second clause) and `h_max` at least `H₂` (`ClimbCtx.bounds`), and `h_max − 1` is at most its
`head_height_floor` (`h_max_sub_one_le_floor`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `H₂`: the threshold; `m`: the last honest round opening slot's index; `i`: the honest round
  opening slot; `rs`: the rounds of the honest round opening slots; `B`: its proposal.

Roots name blocks until `aR S r`: the climb's context `ClimbCtx` carries the premise at the action
time of round `r`; the honest round opening slots' contexts `QuietCtx` read up to support cutoffs of
slots at most `r * R`, before it.

Restated with the delivery premises up to `aR S r`: the bound of its roots `hRoots`, the bundle `ClimbCtxUpTo`'s; the honest round opening slots' bundles `QuietCtxUpTo` read up to support cutoffs of slots at most `r * R`, before it. -/
theorem quiet_straddler_heights_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd T₁ r H₂ m i : ℕ) (rs : ℕ → ℕ)
    (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (aR S r))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (aR S r))
    (hRoots : RootsNameBlocksUntil S Sched x (aR S r))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT) (hT₁ : tGAT ≤ T₁)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hH₂ : OldHeightAttained S Sched x T₁ H₂)
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hEnd : aR S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hT₁0 : T₁ + Δ S ≤ slotStart S (rs 0 * S.C.R - S.C.k - 1))
    (hi : i < m) (hir : rs i * S.C.R + S.C.R ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening S Sched x rs m)
    (hNo : ∀ (w : V) (t' : ℕ), voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' →
      t' < supportCutoff S (r * S.C.R) → w ∉ Sched.adv (t' : Int) →
      ¬ ForkChoiceChangeAt S Sched x w t')
    (hB : ProposalAt S Sched x (rs i * S.C.R) B) :
    H₂ ≤ (chainStateOf S.C B).h + 1 ∧ (chainStateOf S.C B).h ≤ H₂ := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  -- the upper bound
  have hTop : (chainStateOf S.C B).h ≤ H₂ := by
    by_contra hgt
    obtain ⟨t₀, v, a, ht₀, hA, ha⟩ := quiet_top_gives_attestation_cutoff_upTo S Sched x GST tGAT
      tAwakeEnd r m i H₂ (r * S.C.R) rs B hDiv hMono (hSync.mono (supportCutoff_mono S (by omega)))
      (hCatch.mono (supportCutoff_mono S (by omega)))
      (hRoots.mono (supportCutoff_mono S (by omega))) hParent hOwner hU
      hGST hThird hAwake hCommittees hEnd hSeq hi hir le_rfl hNoCol hNo hB
      (by unfold Height at *; omega)
    obtain ⟨j, hl, hAw, hHon, hm⟩ := hA
    have hlt : t₀ < aR S r := by
      have h1 := supportCutoff_lt_of_lt S (show rs i * S.C.R + 1 < r * S.C.R + 1 by omega)
      unfold aR at ht₀ ⊢
      omega
    have := hOld j t₀ v a hl hlt hAw hHon hm
    exact absurd this (not_le.2 ha)
  -- the lower bound
  obtain ⟨hs1, C⟩ := quietCtx_of_upTo S Sched x GST tGAT tAwakeEnd r m i rs hDiv hMono
    (hSync.mono (supportCutoff_mono S (by omega))) (hCatch.mono (supportCutoff_mono S (by omega)))
    (hRoots.mono (supportCutoff_mono S (by omega))) hParent hOwner hU hGST hThird hAwake
    hCommittees hEnd hSeq hi hir le_rfl hNoCol
    hNo
  have hB0 : ProposalAt S Sched x (rs i * S.C.R - 1 + 1) B := by rw [← hs1]; exact hB
  set s₀ := rs i * S.C.R - 1 with hs₀def
  clear_value s₀
  have CC : ClimbCtxUpTo S Sched x GST tGAT tAwakeEnd T₁ r H₂ :=
    ⟨hDiv, hMono, hSync, hCatch, hRoots, hParent, hU, hGST, hT₁, hThird, hAwake, hH₂,
      hOld, hEnd⟩
  have hw0 := C.win (le_refl (s₀ + 1))
  have h0s : rs 0 * S.C.R ≤ s₀ + 1 := C.rs0
  have hT₁s₀ : T₁ + Δ S ≤ slotStart S (s₀ + 1 - S.C.k - 1) := by
    have h1 := slotStart_mono S (show rs 0 * S.C.R - S.C.k - 1 ≤ s₀ + 1 - S.C.k - 1 by
      omega)
    have h2 : slotStart S (rs 0 * S.C.R - 2 * S.C.k + 1) =
        slotStart S (rs 0 * S.C.R - 2 * S.C.k) + 4 * Δ S := by
      rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
    omega
  have hcl2 := C.clause2 B hB0
  have hA2 : anchorCW S tGAT ≤ slotStart S (s₀ + 1 + 1) :=
    le_trans hw0.2 (slotStart_mono S (by omega))
  have hMaj1 := committee_majority_of_committeeSleepiness S Sched _ (s₀ + 1) hCommittees hA2
  obtain ⟨v₀, hv₀⟩ : (S.P.committee (s₀ + 1) ∩ roundMembers S Sched (s₀ + 1 + 1)).Nonempty :=
    Finset.card_pos.1 (by omega)
  have hv₀H : v₀ ∈ Hon S Sched (s₀ + 1) := (Finset.mem_inter.1 hv₀).2
  have hv₀b : v₀ ∉ Sched.adv ((supportCutoff S (s₀ + 1 + 1) : ℕ) : Int) := (Finset.mem_sdiff.1 hv₀H).2
  have hsc₀2 := supportCutoff_eq S (s₀ + 1 + 1)
  have hv₀2 := voteTime_eq S (s₀ + 1 + 1)
  have hss₀1 : slotStart S (s₀ + 1 + 1) = slotStart S (s₀ + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s₀ + 1), Nat.mul_add, Nat.mul_one]
  have hss₀μ := slotStart_mono S (show s₀ + 1 - S.C.k - 1 ≤ s₀ + 1 by omega)
  have hbnd := CC.bounds (t := supportCutoff S (s₀ + 1 + 1)) (w := v₀) (by omega)
    (by unfold aR; exact supportCutoff_mono S (by omega)) hv₀b
  have hflv := h_max_sub_one_le_floor (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v₀).S
  have hfl2 := (hcl2 v₀ hv₀H).2
  refine ⟨?_, hTop⟩
  unfold Height at *
  omega

set_option maxHeartbeats 1000000 in
/-- **B12 restated, part 1, on a copy: two rising quiet openings are at different heights.** The
proof; the audited statement is in `Statements/Executions/Lemma89Statements.lean`.

The route, by contradiction with both proposals `B`, `B₂` at the height `h`: the next proposal
`B'` after `B` has height at least `h + 1` (rising) and at most `H₂ + 1` (A2), so `h` is `H₂ − 1` or
`H₂` (`head_height_floor` (the least chain-state height a viable block may have) at `B`'s action time is at most `h`, B2). No honest validator's `head_height_floor` reaches `h + 1` before the
later opening's support cutoff (`floor_le_before_quiet`); so `B'` reaches every honest validator one
delay after its proposal (`held_spread`), and there it has `h_max = h + 1`, no contest and its root
on `B'`'s chain. The round's base at `B'`'s slot (`WinCtx.base`) makes the honest votes of that slot
extend `B'`; `lem79_step_sets` carries the chain invariant relative to `B'` to the slot before the
later opening, whose proposer's anchor is then on `B'`'s chain or comparable with it, so `B'` is an
ancestor of `B₂`'s parent (`proposal_parent_extends_majority_block`): `B₂` is higher than `h`.

The threshold time `T₁` may be as late as one delay before the start of slot
`rs 0 * R − k − 1`, in place of at most the start of slot
`rs 0 * R − 2k`: the climb takes `T₁` three delays later so that the first honest
attestation above the threshold comes at a round whose slot `r * R + 1` starts at or after the
committee premise's anchor. The proof reads `hT₁0` only to bound `T₁ + Δ` by
the start of a later slot.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `H₂`: the threshold; `m`: the index of the last honest round opening slot; `i < i'`: the indices of the two honest round opening slots; `rs`: the
  openings' rounds; `B`, `B₂`: their proposals.

Roots name blocks until `aR S r`: the climb's context `ClimbCtx` carries the premise at the action
time of round `r`; the honest round opening slots' contexts `QuietCtx` read up to support cutoffs of
slots at most `r * R`, before it.

Restated with the delivery premises up to `aR S r`: the bound of its roots `hRoots`, the bundle `ClimbCtxUpTo`'s; the honest round opening slots' bundles `QuietCtxUpTo` read up to support cutoffs of slots at most `r * R`, before it. -/
theorem quiet_rising_heights_differ_cutoff_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd T₁ r H₂ m i i' s''₂ : ℕ)
    (rs : ℕ → ℕ)
    (B B₂ : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (aR S r))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (aR S r))
    (hRoots : RootsNameBlocksUntil S Sched x (aR S r))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT) (hT₁ : tGAT ≤ T₁)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hH₂ : OldHeightAttained S Sched x T₁ H₂)
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hEnd : aR S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hT₁0 : T₁ + Δ S ≤ slotStart S (rs 0 * S.C.R - S.C.k - 1))
    (hii' : i < i') (hi' : i' < m) (hsR' : rs i' * S.C.R + S.C.R ≤ s''₂)
    (hir' : s''₂ ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening S Sched x rs m)
    (hNo : ∀ (w : V) (t' : ℕ), voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' →
      t' < supportCutoff S (rs (i + 1) * S.C.R) → w ∉ Sched.adv (t' : Int) →
      ¬ ForkChoiceChangeAt S Sched x w t')
    (hNo' : ∀ (w : V) (t' : ℕ), voteTime S (rs i' * S.C.R - S.C.k - 1) ≤ t' →
      t' < supportCutoff S s''₂ → w ∉ Sched.adv (t' : Int) →
      ¬ ForkChoiceChangeAt S Sched x w t')
    (hRise : RisingAt S Sched x rs i)
    (hB : ProposalAt S Sched x (rs i * S.C.R) B) (hB₂ : ProposalAt S Sched x (rs i' * S.C.R) B₂) :
    (chainStateOf S.C B).h ≠ (chainStateOf S.C B₂).h := by
  intro hEq
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
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
  -- the next proposal `B'`, and the heights
  obtain ⟨B', hB', hBB', hBq', hhlo, hhhi⟩ := quiet_rising_next_proposal_late_upTo S Sched x GST tGAT
    tAwakeEnd T₁ r H₂ m i rs B hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hT₁
    hThird hAwake hCommittees hH₂ hOld hEnd hSeq hT₁0 (by omega) hir hNoCol hNo hRise hB
  -- the two contexts
  obtain ⟨hs1, C⟩ := quietCtx_of_upTo S Sched x GST tGAT tAwakeEnd r m i rs hDiv hMono
    (hSync.mono (supportCutoff_mono S (by omega))) (hCatch.mono (supportCutoff_mono S (by omega)))
    (hRoots.mono (supportCutoff_mono S (by omega))) hParent hOwner hU hGST hThird hAwake
    hCommittees hEnd hSeq (by omega)
    (opening_round_step hSeq (by omega)) hir hNoCol
    hNo
  obtain ⟨hs1', C'⟩ := quietCtx_of_upTo S Sched x GST tGAT tAwakeEnd r m i' rs hDiv hMono
    (hSync.mono (supportCutoff_mono S (by omega))) (hCatch.mono (supportCutoff_mono S (by omega)))
    (hRoots.mono (supportCutoff_mono S (by omega))) hParent hOwner hU hGST hThird hAwake
    hCommittees hEnd hSeq hi' hsR' hir' hNoCol
    hNo'
  have hB0 : ProposalAt S Sched x (rs i * S.C.R - 1 + 1) B := by rw [← hs1]; exact hB
  have hB₂0 : ProposalAt S Sched x (rs i' * S.C.R - 1 + 1) B₂ := by rw [← hs1']; exact hB₂
  set s₀ := rs i * S.C.R - 1 with hs₀def
  set s'' := rs (i + 1) * S.C.R with hs''def
  set s₀' := rs i' * S.C.R - 1 with hs₀'def
  set s₃ := s''₂ with hs₃def
  clear_value s₀ s'' s₀' s₃
  have hsR := C.sR
  have hsR' := C'.sR
  have hs''s₀' : s'' + S.C.R ≤ s₀' + 1 := by
    have h' : (rs (i + 1) + 1) * S.C.R ≤ rs i' * S.C.R := Nat.mul_le_mul_right _ hri
    rw [Nat.add_mul, Nat.one_mul] at h'
    omega
  have hEnd' := C'.cut_end
  have hcut' := C'.cut_le
  -- the climb's context
  have CC : ClimbCtxUpTo S Sched x GST tGAT tAwakeEnd T₁ r H₂ :=
    ⟨hDiv, hMono, hSync, hCatch, hRoots, hParent, hU, hGST, hT₁, hThird, hAwake, hH₂,
      hOld, hEnd⟩
  -- the times
  have hw0 := C.win (le_refl (s₀ + 1))
  have hw'' := C.win (σ := s'') (by omega)
  have hw0' := C'.win (le_refl (s₀' + 1))
  have h0s : rs 0 * S.C.R ≤ s₀ + 1 := C.rs0
  have hT₁s : T₁ + Δ S ≤ slotStart S (s₀' + 1 - S.C.k - 1) := by
    have h1 := slotStart_mono S (show rs 0 * S.C.R - S.C.k - 1 ≤ s₀' + 1 - S.C.k - 1 by
      have := C'.rs0
      omega)
    have h2 : slotStart S (rs 0 * S.C.R - 2 * S.C.k + 1) =
        slotStart S (rs 0 * S.C.R - 2 * S.C.k) + 4 * Δ S := by
      rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
    omega
  have hT₁s₀ : T₁ + Δ S ≤ slotStart S (s₀ + 1 - S.C.k - 1) := by
    have h1 := slotStart_mono S (show rs 0 * S.C.R - S.C.k - 1 ≤ s₀ + 1 - S.C.k - 1 by
      omega)
    have h2 : slotStart S (rs 0 * S.C.R - 2 * S.C.k + 1) =
        slotStart S (rs 0 * S.C.R - 2 * S.C.k) + 4 * Δ S := by
      rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
    omega
  have hss'' : slotStart S (s'' - 1 + 1) = slotStart S s'' := by rw [show s'' - 1 + 1 = s'' by omega]
  have hssμ := slotStart_mono S (show s₀ + 1 - S.C.k - 1 ≤ s'' by omega)
  have hssμ' := slotStart_mono S (show s'' ≤ s₀' + 1 by omega)
  have hssμ'' := slotStart_mono S (show s₀' + 1 - S.C.k - 1 ≤ s₀' + 1 by omega)
  have hvs'' := voteTime_eq S s''
  have hcs'' := supportCutoff_eq S s''
  have hcs''1 := supportCutoff_eq S (s'' + 1)
  have hvs''1 := voteTime_eq S (s'' + 1)
  have hss''1 : slotStart S (s'' + 1) = slotStart S s'' + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hc₀'1 := supportCutoff_eq S (s₀' + 1)
  have hv₀'1 := voteTime_eq S (s₀' + 1)
  have hsc₀'mono := supportCutoff_mono S (show s'' + 1 ≤ s₀' + 1 by omega)
  have hsc₀₃ := supportCutoff_mono S (show s₀' + 1 ≤ s₃ by omega)
  have hcR : supportCutoff S (s₀' + 1) ≤ aR S r := supportCutoff_mono S (by omega)
  have hanc0 := hw0.2
  rw [anchorCW_eq] at hanc0
  have hGSTt : GST ≤ T₁ := le_trans hGST hT₁
  -- the next proposal `B'`
  have hqH : S.P.proposer s'' ∉ Sched.adv ((supportCutoff S s'' : ℕ) : Int) := by
    have h := hSeq.honest (i + 1) (by omega)
    rw [hs''def]
    exact h
  have hqAH : ∀ t : ℕ, tGAT ≤ t → t ≤ supportCutoff S s'' →
      S.P.proposer s'' ∈ Sched.awake (t : Int) ∧ S.P.proposer s'' ∉ Sched.adv (t : Int) := by
    intro t h1 h2
    have hq' : S.P.proposer s'' ∉ Sched.adv (t : Int) :=
      fun hh => hqH (hMono _ _ (by exact_mod_cast h2) hh)
    exact ⟨hAwake t h1 (le_trans h2 (le_trans (supportCutoff_mono S (by omega)) hEnd'))
      _ hq', hq'⟩
  set h := (chainStateOf S.C B).h with hhdef
  clear_value h
  have hh : h + 1 = H₂ ∨ h = H₂ := by
    unfold Height at *
    omega
  have hB₂h : (chainStateOf S.C B₂).h = h := hEq.symm
  -- no honest floor reaches `h + 1` before the later opening's support cutoff
  have hF : ∀ (u : V) (t : ℕ), T₁ + 1 ≤ t → t ≤ supportCutoff S (s₀' + 1) →
      u ∉ Sched.adv (t : Int) → head_height_floor (stateBefore x t u).S ≤ h :=
    fun u t h1 h2 hu => floor_le_before_quiet_upTo CC C' hT₁s h hh B₂ hB₂0 hB₂h u t h1 h2 hu
  -- an honest holder of `B'` has its root on `B'`'s chain
  have hRootB' : ∀ (u : V) (t : ℕ), T₁ + 1 ≤ t → t ≤ supportCutoff S (s₀' + 1) →
      u ∉ Sched.adv (t : Int) → B' ∈ (stateBefore x t u).S.T →
      (get_fc_root (stateBefore x t u).S).AncestorEq B' := by
    intro u t h1 h2 hu hB'u
    have hfu := hF u t h1 h2 hu
    have hmx := h_max_le_floor_add_one (stateBefore x t u).S
    have hBh := height_le_h_max S Sched x t u B' hB'u
    have hjl := h_j_lt_h_max S Sched x t u
    have hTE : t ≤ tAwakeEnd := by omega
    have hFB' : (stateBefore x t u).S.F.AncestorEq B' :=
      F_ancestorEq_of_high S Sched x hMono hU hRoots tAwakeEnd t t u u B' hThird hTE hTE hu hu hB'u
        (by unfold Height at *; omega) (max_le (by omega) (by omega))
    rcases root_cases (stateBefore x t u).S with ⟨hJ, hm1, hc⟩ | ⟨hFr, -⟩
    · rw [hJ]
      by_contra hJB
      have hct := fg_contest_true_of _ B' hm1 hB'u hFB'
        (by rw [σ_eq_of_stateBefore S Sched x t u B' hB'u]; unfold Height at *; omega) hJB
      rw [hc] at hct
      cases hct
    · rw [hFr]
      exact hFB'
  -- `B'` reaches every honest validator one delay after its proposal
  have hDel : ∀ (u : V) (t : ℕ), slotStart S s'' + 1 + Δ S ≤ t → t ≤ supportCutoff S (s₀' + 1) →
      u ∉ Sched.adv (t : Int) → B' ∈ (stateBefore x t u).S.T := by
    intro u t h1 h2 hu
    have hqb : S.P.proposer s'' ∉ Sched.adv ((slotStart S s'' : ℕ) : Int) :=
      (hqAH _ (by omega) (by omega)).2
    have hwin : ∀ t' : ℕ, slotStart S s'' + 1 ≤ t' → t' ≤ slotStart S s'' + 1 + Δ S →
        u ∈ Sched.awake (t' : Int) ∧ u ∉ Sched.adv (t' : Int) := by
      intro t' h1' h2'
      have hu' : u ∉ Sched.adv (t' : Int) := fun hh => hu (hMono _ _ (by exact_mod_cast
        (show t' ≤ t by omega)) hh)
      exact ⟨hAwake t' (by omega) (by omega) u hu', hu'⟩
    have hhu : u ∉ Sched.adv ((slotStart S s'' + 1 + Δ S : ℕ) : Int) :=
      fun hh => hu (hMono _ _ (by exact_mod_cast h1) hh)
    rcases held_spread_upTo S Sched x GST tAwakeEnd (slotStart S s'' + 1) (slotStart S s'' + 1) _ u B'
        hDiv hMono (hSync.mono (by omega)) (hCatch.mono (by omega))
        (hRoots.mono (by omega)) hParent hU hThird le_rfl
        (by omega) (by omega) (honest_config_succ x hDiv hqb) hBq' hwin with ⟨hBu, -⟩ | hlo
    · exact (stateBefore_grows x hDiv u h1).1 hBu
    · exfalso
      have hfu := hF u (slotStart S s'' + 1 + Δ S) (by omega) (by omega) hhu
      have hmx := h_max_le_floor_add_one (stateBefore x (slotStart S s'' + 1 + Δ S) u).S
      have hjl := h_j_lt_h_max S Sched x (slotStart S s'' + 1 + Δ S) u
      unfold Height at *
      omega
  -- the window's context at the next opening, inside the first opening's range
  have W1 : WinCtxUpTo S Sched x GST tGAT tAwakeEnd r m (i + 1) rs (s'' - 1) := by
    refine ⟨hDiv, hMono, hSync.mono (le_trans (supportCutoff_mono S (by omega)) hcR),
      hCatch.mono (le_trans (supportCutoff_mono S (by omega)) hcR),
      hRoots.mono (le_trans (supportCutoff_mono S (by omega)) hcR), hParent, hOwner, hU, hGST,
      hThird, hAwake, hCommittees, hEnd, hSeq, by omega, by rw [← hs''def]; omega, by omega, ?_⟩
    intro w t' h1 h2 h3
    exact C.hNo w t' (le_trans (voteTime_mono S (by omega)) h1)
      (lt_of_lt_of_le h2 (supportCutoff_mono S (by omega))) h3
  have hB'P : ProposalAt S Sched x (s'' - 1 + 1) B' := by
    rw [show s'' - 1 + 1 = s'' by omega]
    exact hB'
  have hsc''1 := supportCutoff_eq S (s'' + 1)
  -- the round's base at `B'`'s slot
  obtain ⟨hHeld', hBase', -⟩ := W1.base hNoCol B' hB'P (by
    intro v hv
    rw [show s'' - 1 + 1 = s'' by omega] at hv ⊢
    have hvb : v ∉ Sched.adv ((supportCutoff S (s'' + 1) : ℕ) : Int) := (Finset.mem_sdiff.1 hv).2
    exact hRootB' v _ (by omega) (by omega) hvb (hDel v _ (by omega) (by omega) hvb))
  rw [show s'' - 1 + 1 = s'' by omega] at hHeld' hBase'
  have hmemR : ∀ a b : ℕ, a ≤ b → b ≤ s₃ → ∀ u ∈ roundMembers S Sched b,
      u ∈ roundMembers S Sched a := fun a b hab hb u hu =>
    (roundMembers_mono S Sched a b tAwakeEnd hMono hab
      (le_trans (supportCutoff_mono S hb) hEnd')).1 hu
  -- the chain invariant relative to `B'`, carried to the slot before the later opening
  have hCarry : ∀ n, s'' + n ≤ s₀' →
      HonestChainExtends S Sched x (Hon S Sched (s'' + n)) B' (s'' + n) := by
    intro n
    induction n with
    | zero =>
      intro _
      simpa using hBase'
    | succ n ih =>
      intro hn
      have ihn := ih (by omega)
      rw [show s'' + (n + 1) = s'' + n + 1 by omega]
      -- the times of the slot `σ := s'' + n`
      have hA0 : anchorCW S tGAT ≤ slotStart S (s'' + n + 1) :=
        le_trans hw0.2 (slotStart_mono S (by omega))
      have hA1 : anchorCW S tGAT ≤ slotStart S (s'' + n + 1 + 1) :=
        le_trans hw0.2 (slotStart_mono S (by omega))
      have hdw0 := dutyWindowStart_of_anchor S tGAT (s'' + n) hA0
      have hdw1 := dutyWindowStart_of_anchor S tGAT (s'' + n + 1) hA1
      have hMaj0 := committee_majority_of_committeeSleepiness S Sched _ (s'' + n) hCommittees hA0
      have hMaj1 := committee_majority_of_committeeSleepiness S Sched _ (s'' + n + 1) hCommittees
        hA1
      have hscn := supportCutoff_mono S (show s'' + n + 1 + 1 ≤ s₀' + 1 by omega)
      have hscn1 := supportCutoff_mono S (show s'' + n + 1 ≤ s₀' + 1 by omega)
      have hvn := voteTime_eq S (s'' + n)
      have hvn1 := voteTime_eq S (s'' + n + 1)
      have hcn1 := supportCutoff_eq S (s'' + n + 1)
      have hcn2 := supportCutoff_eq S (s'' + n + 1 + 1)
      have hvn2 := voteTime_eq S (s'' + n + 1 + 1)
      have hssn : slotStart S (s'' + n + 1) = slotStart S (s'' + n) + 4 * Δ S := by
        rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
      have hssn1 : slotStart S (s'' + n + 1 + 1) = slotStart S (s'' + n + 1) + 4 * Δ S := by
        rw [slotStart_eq, slotStart_eq S (s'' + n + 1), Nat.mul_add, Nat.mul_one]
      have hssn0 := slotStart_mono S (show s'' ≤ s'' + n by omega)
      have hdwv0 := dutyWindowStart_le_voteTime S (s'' + n)
      have hdwv1 := dutyWindowStart_le_voteTime S (s'' + n + 1)
      have hfzn := viewFreeze_eq S (s'' + n)
      -- the members' windows
      have hwinn : ∀ σ : ℕ, σ + 1 ≤ s₀' + 1 → tGAT + Δ S ≤ dutyWindowStart S σ →
          ∀ v ∈ Hon S Sched σ, ∀ t : ℕ, dutyWindowStart S σ ≤ t → t ≤ supportCutoff S (σ + 1) →
          v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int) := by
        intro σ hσ hdσ v hv t h1 h2
        have hvb : v ∉ Sched.adv ((supportCutoff S (σ + 1) : ℕ) : Int) := (Finset.mem_sdiff.1 hv).2
        have hv' : v ∉ Sched.adv (t : Int) := fun hh => hvb (hMono _ _ (by exact_mod_cast h2) hh)
        have hscσ := supportCutoff_mono S hσ
        exact ⟨hAwake t (by omega) (by omega) v hv', hv'⟩
      have hvoters : ∀ σ : ℕ, σ + 1 ≤ s₀' + 1 → tGAT + Δ S ≤ dutyWindowStart S σ →
          ∀ u ∈ S.P.committee σ ∩ Hon S Sched σ, u ∈ Hon S Sched σ ∧ u ∈ S.P.committee σ ∧
            ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = σ ∧
              ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S σ) ∧
                (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
                  x[i + 1].sent - x[i].sent := by
        intro σ hσ hdσ u hu
        obtain ⟨hK, huH⟩ := Finset.mem_inter.1 hu
        have hdv := dutyWindowStart_le_voteTime S σ
        have hvc : voteTime S σ ≤ supportCutoff S (σ + 1) := by
          have := supportCutoff_eq S (σ + 1)
          have := voteTime_succ S σ
          omega
        obtain ⟨i', vote, hl, hvi, hvs, hsent⟩ := honest_votes_of_window S Sched x σ u hDiv hMono
          (fun t h1 h2 => (hwinn σ hσ hdσ u huH t h1 (by omega)).1)
          (hwinn σ hσ hdσ u huH _ hdv hvc).2 hK
        exact ⟨huH, hK, vote, hvi, hvs, i', hl, hsent⟩
      -- the frames relative to `B'`
      have hv''n : voteTime S s'' ≤ voteTime S (s'' + n) := voteTime_mono S (by omega)
      have hv''n1 : voteTime S s'' ≤ voteTime S (s'' + n + 1) := voteTime_mono S (by omega)
      have hthF : voteTime S s'' ≤ viewFreeze S (s'' + n) := by omega
      have hT₁v : T₁ + 1 ≤ voteTime S (s'' + n + 1) := by omega
      have hvc1 : voteTime S (s'' + n + 1) ≤ supportCutoff S (s₀' + 1) := by omega
      have hT₁c : T₁ + 1 ≤ supportCutoff S (s'' + n + 1 + 1) := by omega
      have hvc2 : voteTime S s'' ≤ supportCutoff S (s'' + n + 1 + 1) := by omega
      have hvc12 : voteTime S (s'' + n + 1) ≤ supportCutoff S (s'' + n + 1 + 1) := by omega
      have hle1 : s'' + 1 ≤ s'' + n + 1 + 1 := by omega
      have hle2 : s'' + n + 1 + 1 ≤ s₃ := by omega
      have hSF : ∀ w ∈ Hon S Sched (s'' + n + 1), StepFrameAt S Sched x B' (s'' + n) w := by
        intro w hw
        have hwb : w ∉ Sched.adv ((supportCutoff S (s'' + n + 1 + 1) : ℕ) : Int) :=
          (Finset.mem_sdiff.1 hw).2
        have hws'' : w ∈ Hon S Sched s'' := hmemR (s'' + 1) (s'' + n + 1 + 1) hle1 hle2 w hw
        have hBw := hHeld' w hws''
        have hwv : w ∉ Sched.adv ((voteTime S (s'' + n + 1) : ℕ) : Int) :=
          fun hh => hwb (hMono _ _ (by exact_mod_cast hvc12) hh)
        have hBw1 : B' ∈ (stateBefore x (voteTime S (s'' + n + 1)) w).S.T :=
          (stateBefore_grows x hDiv w hv''n1).1 hBw
        have hBw2 : B' ∈ (stateBefore x (supportCutoff S (s'' + n + 1 + 1)) w).S.T :=
          (stateBefore_grows x hDiv w hvc2).1 hBw
        have hr1 := hRootB' w (voteTime S (s'' + n + 1)) hT₁v hvc1 hwv hBw1
        have hf1 := hF w (voteTime S (s'' + n + 1)) hT₁v hvc1 hwv
        have hr2 := hRootB' w (supportCutoff S (s'' + n + 1 + 1)) hT₁c hscn hwb hBw2
        have hf1' : head_height_floor (stateBefore x (voteTime S (s'' + n + 1)) w).S ≤
            (chainStateOf S.C B').h := by
          unfold Height at *
          omega
        exact stepFrame_of_compat S Sched x hDiv B' B' (s'' + n) w (voteTime S s'')
          (ancestorEq_refl B') hBw hthF hv''n1 ((compatible_iff _ _).2 (Or.inl hr1)) hf1'
          ((compatible_iff _ _).2 (Or.inl hr2))
      exact lem79_step_sets_upTo S Sched x GST (s'' + n) (Hon S Sched (s'' + n))
        (Hon S Sched (s'' + n + 1)) (fun s => S.P.committee s ∩ Hon S Sched s) B' hDiv hMono
        (hSync.mono (le_trans (supportCutoff_mono S (by omega)) hcR))
        (hCatch.mono (le_trans (supportCutoff_mono S (by omega)) hcR))
        (hRoots.mono (le_trans (supportCutoff_mono S (by omega)) hcR)) hParent
        hOwner (by omega) ihn
        (hmemR (s'' + n + 1) (s'' + n + 1 + 1) (Nat.le_succ _) (by omega))
        (hwinn (s'' + n) (by omega) hdw0) (hwinn (s'' + n + 1) (by omega) hdw1)
        (hvoters (s'' + n) (by omega) hdw0) (hvoters (s'' + n + 1) (by omega) hdw1)
        (fun w _ => (counting_of_committee_majority S Sched x (s'' + n) (voteTime S (s'' + n + 1))
          (Hon S Sched (s'' + n)) w hMaj0).2.2)
        (fun v _ => (counting_of_committee_majority S Sched x (s'' + n + 1)
          (supportCutoff S (s'' + n + 1 + 1)) (Hon S Sched (s'' + n + 1)) v hMaj1).2.1)
        (fun w hw => (hSF w hw).1) (fun w hw => (hSF w hw).2.1) (fun w hw => (hSF w hw).2.2)
  have hCE := hCarry (s₀' - s'') (by omega)
  rw [show s'' + (s₀' - s'') = s₀' by omega] at hCE
  have hCE1 := hCarry (s₀' - 1 - s'') (by omega)
  rw [show s'' + (s₀' - 1 - s'') = s₀' - 1 by omega] at hCE1
  -- the later opening's proposer
  have hq'H : S.P.proposer (s₀' + 1) ∉ Sched.adv ((supportCutoff S (s₀' + 1) : ℕ) : Int) := by
    have h' := hSeq.honest i' (le_of_lt hi')
    rw [hs1'] at h'
    exact h'
  have hq'AH : ∀ t : ℕ, tGAT ≤ t → t ≤ supportCutoff S (s₀' + 1) →
      S.P.proposer (s₀' + 1) ∈ Sched.awake (t : Int) ∧
        S.P.proposer (s₀' + 1) ∉ Sched.adv (t : Int) := by
    intro t h1 h2
    have hq' : S.P.proposer (s₀' + 1) ∉ Sched.adv (t : Int) :=
      fun hh => hq'H (hMono _ _ (by exact_mod_cast h2) hh)
    exact ⟨hAwake t h1 (by omega) _ hq', hq'⟩
  have hss₀' : slotStart S (s₀' + 1) = slotStart S s₀' + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv₀' := voteTime_eq S s₀'
  have hc₀' := supportCutoff_eq S s₀'
  have hss₀'1 := slotStart_mono S (show s'' ≤ s₀' by omega)
  have hq'b : S.P.proposer (s₀' + 1) ∉ Sched.adv ((slotStart S (s₀' + 1) : ℕ) : Int) :=
    (hq'AH _ (by omega) (by omega)).2
  have hB'q : B' ∈ (stateBefore x (slotStart S (s₀' + 1)) (S.P.proposer (s₀' + 1))).S.T :=
    hDel _ _ (by omega) (by omega) hq'b
  have hRq := hRootB' _ _ (by omega) (by omega) hq'b hB'q
  have hFq := hF _ (slotStart S (s₀' + 1)) (by omega) (by omega) hq'b
  have hFB'q := ancestorEq_trans (F_ancestorEq_fc_root_of_stateBefore S Sched x _ _) hRq
  have hVHq : B' ∈ (fg_to_ac (stateBefore x (slotStart S (s₀' + 1)) (S.P.proposer (s₀' + 1))).S).viable_heads := by
    rw [mem_viable_heads_iff, fc_root_eq]
    refine ⟨hB'q, hFB'q, hRq, ?_⟩
    rw [σ_eq_of_stateBefore S Sched x _ _ B' hB'q]
    unfold Height at *
    omega
  have hF3p : ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S (s₀' + 1)) (S.P.proposer (s₀' + 1))).S).tree,
      W ∈ (fg_to_ac (stateBefore x (slotStart S (s₀' + 1)) (S.P.proposer (s₀' + 1))).S).viable_heads ∧
      B'.AncestorEq W :=
    ⟨B', (mem_fg_to_ac_tree _ _).2 ⟨hB'q, hFB'q⟩, hVHq, ancestorEq_refl B'⟩
  -- the anchor is comparable with `B'`
  have hcq' : supportCutoff S (s₀' - 1 + 1) ≤ supportCutoff S (s₀' + 1) :=
    supportCutoff_mono S (by omega)
  have hq'Hm : S.P.proposer (s₀' + 1) ∈ Hon S Sched (s₀' - 1) :=
    Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun hh => hq'H (hMono _ _ (by exact_mod_cast hcq') hh)⟩
  have hAcmp : (get_anchor (stateBefore x (slotStart S (s₀' + 1)) (S.P.proposer (s₀' + 1))).A
      (fg_to_ac (stateBefore x (slotStart S (s₀' + 1)) (S.P.proposer (s₀' + 1))).S)
      ((slotStart S (s₀' + 1) : ℕ) : Int)).AncestorEq B' ∨
      B'.AncestorEq (get_anchor (stateBefore x (slotStart S (s₀' + 1)) (S.P.proposer (s₀' + 1))).A
      (fg_to_ac (stateBefore x (slotStart S (s₀' + 1)) (S.P.proposer (s₀' + 1))).S)
      ((slotStart S (s₀' + 1) : ℕ) : Int)) := by
    rcases get_anchor_cases_locked (stateBefore x (slotStart S (s₀' + 1)) (S.P.proposer (s₀' + 1))).A
      (fg_to_ac (stateBefore x (slotStart S (s₀' + 1)) (S.P.proposer (s₀' + 1))).S)
      ((slotStart S (s₀' + 1) : ℕ) : Int) with ha | ⟨-, e, he, hl, hAe⟩
    · left
      rw [ha, fc_root_eq]
      exact hRq
    · have hl' := hl
      simp only [is_live_iff] at hl'
      have hA' : anchorCW S tGAT ≤ slotStart S (s₀' - 1 + 1 + 1) :=
        le_trans hw0.2 (slotStart_mono S (by omega))
      have hdw' := dutyWindowStart_of_anchor S tGAT (s₀' - 1 + 1) hA'
      have hsc' := supportCutoff_eq S (s₀' - 1 + 1)
      have hv' := voteTime_eq S (s₀' - 1 + 1)
      have hv2' := voteTime_eq S (s₀' - 1 + 2)
      have hss' : slotStart S (s₀' - 1 + 1) = slotStart S s₀' := by
        rw [show s₀' - 1 + 1 = s₀' by omega]
      have hss2' : slotStart S (s₀' - 1 + 2) = slotStart S (s₀' + 1) := by
        rw [show s₀' - 1 + 2 = s₀' + 1 by omega]
      have hdwq : tGAT ≤ dutyWindowStart S (s₀' - 1 + 1) := by omega
      have hlt1 : supportCutoff S (s₀' - 1 + 1) < slotStart S (s₀' + 1) := by omega
      have hlt2 : slotStart S (s₀' + 1) ≤ voteTime S (s₀' - 1 + 2) := by omega
      have hcq : slotStart S (s₀' + 1) ≤ supportCutoff S (s₀' + 1) := by omega
      rcases live_lock_entry_source S Sched x (s₀' - 1) (slotStart S (s₀' + 1)) _ hDiv
          (fun t h1' h2' => hq'AH t (le_trans hdwq (le_trans (dutyWindowStart_mono S (by omega)) h1')) (le_trans h2' hcq)) hlt1 hlt2 e he
          hl'.1 with
        ⟨C₁, hC₁, heC₁⟩ | ⟨A₃, hR₃, e', he', hl₃, hee'⟩
      · have hBC₁ := hCE1.2.2 _ hq'Hm C₁ hC₁
        exact ancestorEq_compatible (ancestorEq_trans hAe heC₁) hBC₁
      · have hcmp := hCE1.2.1 _ hq'Hm A₃ hR₃ e' he' hl₃
        rcases (compatible_iff _ _).1 hcmp with he'B | hBe'
        · exact Or.inl (ancestorEq_trans hAe (ancestorEq_trans hee' he'B))
        · exact ancestorEq_compatible (ancestorEq_trans hAe hee') hBe'
  -- the honest votes of slot `s₀'` extend `B'`
  have hA₀' : anchorCW S tGAT ≤ slotStart S (s₀' + 1) := le_trans hw0.2 (slotStart_mono S (by omega))
  have hMaj₀' := committee_majority_of_committeeSleepiness S Sched _ s₀' hCommittees hA₀'
  have hdw₀' := dutyWindowStart_of_anchor S tGAT s₀' hA₀'
  set Hs : Finset V := S.P.committee s₀' ∩ Hon S Sched s₀' with hHsdef
  have hex : ∀ u ∈ Hs, ∃ H_u : Block V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s₀') ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s₀' H_u.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H_u ∈ (stateBefore x (voteTime S s₀') u).S.T ∧ B'.AncestorEq H_u := by
    intro u hu
    obtain ⟨hK, huH⟩ := Finset.mem_inter.1 hu
    have hub : u ∉ Sched.adv ((supportCutoff S (s₀' + 1) : ℕ) : Int) := (Finset.mem_sdiff.1 huH).2
    have hdv := dutyWindowStart_le_voteTime S s₀'
    have hvc : voteTime S s₀' ≤ supportCutoff S (s₀' + 1) := by omega
    obtain ⟨i', vote, hl, -, -, hsent⟩ := honest_votes_of_window S Sched x s₀' u hDiv hMono
      (fun t h1 h2 => hAwake t (by omega) (by omega) u
        (fun hh => hub (hMono _ _ (by exact_mod_cast (show t ≤ supportCutoff S (s₀' + 1) by
          omega)) hh)))
      (fun hh => hub (hMono _ _ (by exact_mod_cast hvc) hh)) hK
    obtain ⟨H_u, hT, hvt, hBH⟩ := hCE.1 u huH vote ⟨i', hl, hsent⟩
    subst hvt
    exact ⟨H_u, ⟨i', hl, hsent⟩, hT, hBH⟩
  choose Hc hHc using hex
  let Hf : V → Block V := fun u => if h' : u ∈ Hs then Hc u h' else B'
  have hHf : ∀ u (hu : u ∈ Hs), Hf u = Hc u hu := fun u hu => dif_pos hu
  obtain ⟨iB₂, hlB₂, hsentB₂⟩ := hB₂0
  have hB'P₂ : B'.AncestorEq B₂.parent := by
    rcases hAcmp with hAB | hBA
    · refine (proposal_parent_extends_majority_block_upTo S Sched x GST s₀' iB₂ Hs Hf B' B₂ _ hDiv hMono
        (hSync.mono (le_trans (supportCutoff_mono S (by omega)) hcR))
        (hCatch.mono (le_trans (supportCutoff_mono S (by omega)) hcR))
        (hRoots.mono (le_trans (supportCutoff_mono S (by omega)) hcR))
        hParent hOwner (by omega) ?_ ?_
        (fun t h1 h2 => hq'AH t (by omega) (by omega)) hlB₂ hsentB₂ hF3p hAB).1
      · intro u hu
        rw [hHf u hu]
        obtain ⟨hK, huH⟩ := Finset.mem_inter.1 hu
        have hub : u ∉ Sched.adv ((supportCutoff S (s₀' + 1) : ℕ) : Int) :=
          (Finset.mem_sdiff.1 huH).2
        exact ⟨hK, fun hh => hub (hMono _ _ (by exact_mod_cast (show slotStart S (s₀' + 1) ≤
          supportCutoff S (s₀' + 1) by omega)) hh), (hHc u hu).1, (hHc u hu).2.1, (hHc u hu).2.2⟩
      · intro votes_p support_p hP
        rw [hP.1]
        exact (counting_of_committee_majority S Sched x s₀' (slotStart S (s₀' + 1))
          (Hon S Sched s₀') _ hMaj₀').2.1
    · exact ancestorEq_trans hBA (get_anchor_ancestorEq_proposal_parent S Sched x (s₀' + 1) iB₂ B₂
        _ hlB₂ hsentB₂)
  obtain ⟨-, -, hB₂par?, -⟩ := proposal_parent_walk_end S Sched x s₀' iB₂ B₂ _ hlB₂ hsentB₂
  have hPB₂ := GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_parent? hB₂par?
  have hh1 := chainStateOf_height_mono S.C (ancestorEq_trans hB'P₂ hPB₂)
  unfold Height at *
  omega

open Classical in
/-- **B12 restated, part 2, on a copy: at most two rising quiet openings before the climb's end.**
In the climb's context, the honest round opening slots `i < m` with `rs i * R < r * R`, no
fork-choice change from the vote time of slot `rs i * R − k − 1` to before the support
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
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `H₂`: the threshold; `m`: the index of the last honest round opening slot; `rs`: the rounds of the honest round opening slots.

Roots name blocks until `aR S r`: `quiet_rising_next_proposal_late`, `quiet_straddler_heights` and
`quiet_rising_heights_differ_cutoff`, at the action time of round `r`.

Restated with the delivery premises up to `aR S r`: the bound of its roots `hRoots`, the bundle `ClimbCtxUpTo`'s; the honest round opening slots' bundles `QuietCtxUpTo` read up to support cutoffs of slots at most `r * R`, before it. -/
theorem quiet_rising_before_fast_round_le_two_cutoff_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd T₁ r H₂ m : ℕ) (rs : ℕ → ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (aR S r))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (aR S r))
    (hRoots : RootsNameBlocksUntil S Sched x (aR S r))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT) (hT₁ : tGAT ≤ T₁)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hH₂ : OldHeightAttained S Sched x T₁ H₂)
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hEnd : aR S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hT₁0 : T₁ + Δ S ≤ slotStart S (rs 0 * S.C.R - S.C.k - 1))
    (hNoCol : ¬ RootCollisionAtOpening S Sched x rs m) :
    ((Finset.range m).filter (fun i => rs i * S.C.R < r * S.C.R ∧
      (∀ (w : V) (t' : ℕ), voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' →
        t' < supportCutoff S (min (rs (i + 1) * S.C.R) (r * S.C.R)) →
        w ∉ Sched.adv (t' : Int) → ¬ ForkChoiceChangeAt S Sched x w t') ∧
      (rs (i + 1) * S.C.R ≤ r * S.C.R → RisingAt S Sched x rs i))).card ≤ 2 := by
  set F := (Finset.range m).filter (fun i => rs i * S.C.R < r * S.C.R ∧
      (∀ (w : V) (t' : ℕ), voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' →
        t' < supportCutoff S (min (rs (i + 1) * S.C.R) (r * S.C.R)) →
        w ∉ Sched.adv (t' : Int) → ¬ ForkChoiceChangeAt S Sched x w t') ∧
      (rs (i + 1) * S.C.R ≤ r * S.C.R → RisingAt S Sched x rs i)) with hFdef
  have hP : ∀ i, i ≤ m → ∃ B : Block V, ProposalAt S Sched x (rs i * S.C.R) B :=
    fun i hi => opening_proposal_exists S Sched x tGAT tAwakeEnd m i rs hDiv hMono hAwake
      hSeq hi
  let Bf : ℕ → Block V := fun i =>
    if hi : i ≤ m then Classical.choose (hP i hi) else Block.genesis
  have hBf : ∀ i (hi : i ≤ m), ProposalAt S Sched x (rs i * S.C.R) (Bf i) := by
    intro i hi
    simp only [Bf, dif_pos hi]
    exact Classical.choose_spec (hP i hi)
  have hmem : ∀ i ∈ F, i < m ∧ rs i * S.C.R < r * S.C.R ∧
      (∀ (w : V) (t' : ℕ), voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' →
        t' < supportCutoff S (min (rs (i + 1) * S.C.R) (r * S.C.R)) →
        w ∉ Sched.adv (t' : Int) → ¬ ForkChoiceChangeAt S Sched x w t') ∧
      (rs (i + 1) * S.C.R ≤ r * S.C.R → RisingAt S Sched x rs i) := by
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
      (∀ (w : V) (t' : ℕ), voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' →
        t' < supportCutoff S (min (rs (i + 1) * S.C.R) (r * S.C.R)) →
        w ∉ Sched.adv (t' : Int) → ¬ ForkChoiceChangeAt S Sched x w t') →
      ∀ (w : V) (t' : ℕ), voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' →
        t' < supportCutoff S (rs (i + 1) * S.C.R) → w ∉ Sched.adv (t' : Int) →
        ¬ ForkChoiceChangeAt S Sched x w t' := by
    intro i hir hNo
    rw [min_eq_left hir] at hNo
    exact hNo
  let f : ℕ → ℕ := fun i => (chainStateOf S.C (Bf i)).h
  have hmaps : ∀ i ∈ F, f i ∈ (insert (H₂ - 1) {H₂} : Finset ℕ) := by
    intro i hi
    obtain ⟨him, hlt, hNo, hRise⟩ := hmem i hi
    have hh : H₂ ≤ (chainStateOf S.C (Bf i)).h + 1 ∧ (chainStateOf S.C (Bf i)).h ≤ H₂ := by
      by_cases hir : rs (i + 1) * S.C.R ≤ r * S.C.R
      · obtain ⟨-, -, -, -, h1, h2⟩ := quiet_rising_next_proposal_late_upTo S Sched x GST tGAT
          tAwakeEnd T₁ r H₂ m i rs (Bf i) hDiv hMono hSync hCatch hRoots hParent hOwner hU
          hGST hT₁ hThird hAwake hCommittees hH₂ hOld hEnd hSeq hT₁0 him hir hNoCol
          (hNoNext i hir hNo) (hRise hir) (hBf i (le_of_lt him))
        exact ⟨h1, h2⟩
      · rw [min_eq_right (le_of_lt (Nat.lt_of_not_le hir))] at hNo
        exact quiet_straddler_heights_upTo S Sched x GST tGAT tAwakeEnd T₁ r H₂ m i rs (Bf i) hDiv
          hMono hSync hCatch hRoots hParent hOwner hU hGST hT₁ hThird hAwake hCommittees
          hH₂ hOld hEnd hSeq hT₁0 him (hmul _ hlt) hNoCol hNo (hBf i (le_of_lt him))
    rw [Finset.mem_insert, Finset.mem_singleton]
    show (chainStateOf S.C (Bf i)).h = H₂ - 1 ∨ (chainStateOf S.C (Bf i)).h = H₂
    unfold Height at *
    omega
  -- two of them: the earlier one's next slot is at or before the later one's, so it rises
  have hpair : ∀ i ∈ F, ∀ i' ∈ F, i < i' → f i ≠ f i' := by
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
      le_min (opening_round_step hSeq him') (hmul _ hlt')
    exact quiet_rising_heights_differ_cutoff_upTo S Sched x GST tGAT tAwakeEnd T₁ r H₂ m i i'
      (min (rs (i' + 1) * S.C.R) (r * S.C.R)) rs (Bf i) (Bf i') hDiv hMono hSync hCatch
      hRoots hParent hOwner hU hGST hT₁ hThird hAwake hCommittees hH₂ hOld hEnd hSeq hT₁0 hlt him'
      hsR' (min_le_right _ _) hNoCol (hNoNext i hir hNo) hNo' (hRise hir)
      (hBf i (le_of_lt him)) (hBf i' (le_of_lt him')) hff
  have hinj : Set.InjOn f F := by
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
`B`'s chain at `B`'s chain-state height (Lemma 89r at the opening, `QuietCtx.round89r`).

The threshold time `T₁` may be as late as one delay before the start of slot
`rs 0 * R − k − 1`, in place of at most the start of slot
`rs 0 * R − 2k`: the climb takes `T₁` three delays later so that the first honest
attestation above the threshold comes at a round whose slot `r * R + 1` starts at or after the
committee premise's anchor. The proof reads `hT₁0` only to bound `T₁ + Δ` by
the start of a later slot.

Roots name blocks until `aR S r`: the climb's context `ClimbCtx` carries the premise at the action
time of round `r`; the honest round opening slots' contexts `QuietCtx` read up to support cutoffs of
slots at most `r * R`, before it.

Restated with the delivery premises up to `aR S r`: the bound of its roots `hRoots`, the bundle `ClimbCtxUpTo`'s; the honest round opening slots' bundles `QuietCtxUpTo` read up to support cutoffs of slots at most `r * R`, before it; the attestations (`hSyncF`, `hCatchF`) up to `slotStart S (rs (i + 1) * S.C.R)`, the bound `QuietCtxUpTo.round89r` reads them at for the next opening. -/
theorem quiet_waiting_next_proposal_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd T₁ r H₂ m i : ℕ) (rs : ℕ → ℕ)
    (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (aR S r))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (aR S r))
    (hRoots : RootsNameBlocksUntil S Sched x (aR S r))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT) (hT₁ : tGAT ≤ T₁)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hH₂ : OldHeightAttained S Sched x T₁ H₂)
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hEnd : aR S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hT₁0 : T₁ + Δ S ≤ slotStart S (rs 0 * S.C.R - S.C.k - 1))
    (hi : i < m) (hir : rs (i + 1) * S.C.R ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening S Sched x rs m)
    (hNo : ∀ (w : V) (t' : ℕ), voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' →
      t' < supportCutoff S (rs (i + 1) * S.C.R) → w ∉ Sched.adv (t' : Int) →
      ¬ ForkChoiceChangeAt S Sched x w t')
    (hSyncF : SynchronyFromWakeUpTo S Sched x (Δ_F S) GST fgObject (slotStart S (rs (i + 1) * S.C.R)))
    (hCatchF : CatchUpOnWakeUpTo S Sched x (Δ_F S) GST fgObject (slotStart S (rs (i + 1) * S.C.R)))
    (hWait : ∀ B' : Block V, ProposalAt S Sched x (rs (i + 1) * S.C.R) B' →
      (chainStateOf S.C B').h ≤ (chainStateOf S.C B).h)
    (hTop : (chainStateOf S.C B).h ≤ H₂)
    (hB : ProposalAt S Sched x (rs i * S.C.R) B) :
    ∃ B' : Block V, ProposalAt S Sched x (rs (i + 1) * S.C.R) B' ∧
      B.AncestorEq B' ∧ (chainStateOf S.C B').h = (chainStateOf S.C B).h ∧
      B' ∈ (stateBefore x (slotStart S (rs (i + 1) * S.C.R) + 1)
        (S.P.proposer (rs (i + 1) * S.C.R))).S.T ∧
      H₂ ≤ (chainStateOf S.C B).h + 1 ∧ (chainStateOf S.C B).h ≤ H₂ := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  obtain ⟨hs1, C⟩ := quietCtx_of_upTo S Sched x GST tGAT tAwakeEnd r m i rs hDiv hMono
    (hSync.mono (supportCutoff_mono S (by omega))) (hCatch.mono (supportCutoff_mono S (by omega)))
    (hRoots.mono (supportCutoff_mono S (by omega))) hParent hOwner hU hGST hThird hAwake
    hCommittees hEnd hSeq hi
    (opening_round_step hSeq hi) hir hNoCol hNo
  have hB0 : ProposalAt S Sched x (rs i * S.C.R - 1 + 1) B := by rw [← hs1]; exact hB
  set s₀ := rs i * S.C.R - 1 with hs₀def
  set s'' := rs (i + 1) * S.C.R with hs''def
  clear_value s₀ s''
  have hsR := C.sR
  have hEnd' := C.cut_end
  have CC : ClimbCtxUpTo S Sched x GST tGAT tAwakeEnd T₁ r H₂ :=
    ⟨hDiv, hMono, hSync, hCatch, hRoots, hParent, hU, hGST, hT₁, hThird, hAwake, hH₂,
      hOld, hEnd⟩
  -- the times
  have hw0 := C.win (le_refl (s₀ + 1))
  have h0s : rs 0 * S.C.R ≤ s₀ + 1 := C.rs0
  have hT₁s₀ : T₁ + Δ S ≤ slotStart S (s₀ + 1 - S.C.k - 1) := by
    have h1 := slotStart_mono S (show rs 0 * S.C.R - S.C.k - 1 ≤ s₀ + 1 - S.C.k - 1 by
      omega)
    have h2 : slotStart S (rs 0 * S.C.R - 2 * S.C.k + 1) =
        slotStart S (rs 0 * S.C.R - 2 * S.C.k) + 4 * Δ S := by
      rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
    omega
  have hss'' : slotStart S (s'' - 1 + 1) = slotStart S s'' := by rw [show s'' - 1 + 1 = s'' by omega]
  have hssμ := slotStart_mono S (show s₀ + 1 - S.C.k - 1 ≤ s'' by omega)
  have hvs'' := voteTime_eq S s''
  have hcs'' := supportCutoff_eq S s''
  have hanc0 := hw0.2
  rw [anchorCW_eq] at hanc0
  -- the next proposal `B'`
  have hqH : S.P.proposer s'' ∉ Sched.adv ((supportCutoff S s'' : ℕ) : Int) := by
    have h := hSeq.honest (i + 1) (by omega)
    rw [hs''def]
    exact h
  have hqAH : ∀ t : ℕ, tGAT ≤ t → t ≤ supportCutoff S s'' →
      S.P.proposer s'' ∈ Sched.awake (t : Int) ∧ S.P.proposer s'' ∉ Sched.adv (t : Int) := by
    intro t h1 h2
    have hq' : S.P.proposer s'' ∉ Sched.adv (t : Int) :=
      fun hh => hqH (hMono _ _ (by exact_mod_cast h2) hh)
    exact ⟨hAwake t h1 (le_trans h2 (le_trans (supportCutoff_mono S (by omega)) hEnd'))
      _ hq', hq'⟩
  have hs''2 : s'' - 2 + 2 = s'' := by omega
  have hpw := proposalWindowStart_eqJ S (s'' - 2)
  have hA21 : anchorCW S tGAT ≤ slotStart S (s'' - 2 + 1 + 1) := by
    rw [show s'' - 2 + 1 + 1 = s'' by omega]
    exact le_trans hw0.2 hssμ
  have hdwA := dutyWindowStart_of_anchor S tGAT (s'' - 2 + 1) hA21
  obtain ⟨iB', B', hl', hsent'⟩ := honest_proposer_proposesJ S Sched x (s'' - 2) hDiv hMono
    (by
      intro t h1 h2
      rw [hpw] at h1
      rw [hs''2] at h2 ⊢
      exact hqAH t (by omega) (by omega))
  rw [hs''2] at hl' hsent'
  have hB' : ProposalAt S Sched x s'' B' := ⟨iB', hl', hsent'⟩
  have hW := hWait B' hB'
  have h89 := C.round89r hs''def.symm B B' hB0 hB' hSyncF hCatchF
  have hBB' : B.AncestorEq B' ∧ (chainStateOf S.C B').h = (chainStateOf S.C B).h := by
    refine ⟨h89.1, ?_⟩
    rcases h89.2.1 with h' | ⟨h', -⟩
    · unfold Height at *
      omega
    · exact h'
  -- the proposer of `B'` holds it
  have hB'0 : ProposalAt S Sched x (s'' - 1 + 1) B' := by
    rw [show s'' - 1 + 1 = s'' by omega]
    exact hB'
  have hPV' := proposal_parent_viable_head S Sched x (s'' - 1) B' _ hB'0
  have hPV'' := (mem_viable_heads_iff _ _).1 hPV'
  obtain ⟨iB'', hlB'', hsentB''⟩ := hB'0
  obtain ⟨-, -, hB'par?, -⟩ := proposal_parent_walk_end S Sched x (s'' - 1) iB'' B' _
    hlB'' hsentB''
  have hPB' := GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_parent? hB'par?
  have hRootNew' : ∀ B₁ ∈ (stateBefore x (slotStart S (s'' - 1 + 1)) (S.P.proposer (s'' - 1 + 1))).S.T,
      B₁.root ≠ B'.root := by
    intro B₁ hB₁ heq
    apply hNoCol
    rw [GoldilocksCorrectness.Proofs.View.rootCollisionAtOpening_unfold]
    refine ⟨i + 1, by omega, B', ?_, ?_⟩
    · rw [← hs''def]
      exact hB'
    · rw [← hs''def]
      rw [GoldilocksCorrectness.Proofs.View.rootCollisionAtProposal_unfold]
      show ∃ B₁ ∈ (stateBefore x (slotStart S s'') (S.P.proposer s'')).S.T, B₁.root = B'.root
      rw [show s'' - 1 + 1 = s'' by omega] at hB₁
      exact ⟨B₁, hB₁, heq⟩
  have hBq := lem22a_proposer_holds_own_proposal S Sched x (s'' - 1) iB'' B' _ hDiv hMono hlB''
    hsentB'' hRootNew' hPV''.1
    ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans hPV''.2.1 hPB')))
  have hti := (time_of_lbl_tickAllAwake x hlB'').2
  have hBq' : B' ∈ (stateBefore x (slotStart S s'' + 1) (S.P.proposer s'')).S.T := by
    have hle : iB'' + 1 ≤ stepBefore x (slotStart S s'' + 1) :=
      (time_lt_iff_le_stepBefore x hDiv (by omega)).1 (by rw [hti, hss'']; omega)
    have h' := mem_T_mono x _ hle hBq
    rw [show s'' - 1 + 1 = s'' by omega] at h'
    exact h'
  -- the heights
  have haR : slotStart S s'' + 1 ≤ aR S r := by
    have h1 := supportCutoff_mono S (show s'' ≤ r * S.C.R + 1 by omega)
    unfold aR
    omega
  have hB'top := held_height_le_before_action S Sched x tAwakeEnd r H₂ (slotStart S s'' + 1) _ B' hU
    hThird hOld haR hEnd hBq'
  have hcl2 := C.clause2 B hB0
  have hA2 : anchorCW S tGAT ≤ slotStart S (s₀ + 1 + 1) :=
    le_trans hw0.2 (slotStart_mono S (by omega))
  have hMaj1 := committee_majority_of_committeeSleepiness S Sched _ (s₀ + 1) hCommittees hA2
  obtain ⟨v₀, hv₀⟩ : (S.P.committee (s₀ + 1) ∩ roundMembers S Sched (s₀ + 1 + 1)).Nonempty :=
    Finset.card_pos.1 (by omega)
  have hv₀H : v₀ ∈ Hon S Sched (s₀ + 1) := (Finset.mem_inter.1 hv₀).2
  have hv₀b : v₀ ∉ Sched.adv ((supportCutoff S (s₀ + 1 + 1) : ℕ) : Int) := (Finset.mem_sdiff.1 hv₀H).2
  have hsc₀2 := supportCutoff_eq S (s₀ + 1 + 1)
  have hv₀2 := voteTime_eq S (s₀ + 1 + 1)
  have hss₀1 : slotStart S (s₀ + 1 + 1) = slotStart S (s₀ + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s₀ + 1), Nat.mul_add, Nat.mul_one]
  have hss₀μ := slotStart_mono S (show s₀ + 1 - S.C.k - 1 ≤ s₀ + 1 by omega)
  have hbnd := CC.bounds (t := supportCutoff S (s₀ + 1 + 1)) (w := v₀) (by omega)
    (by unfold aR; exact supportCutoff_mono S (by omega)) hv₀b
  have hflv := h_max_sub_one_le_floor (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v₀).S
  have hfl2 := (hcl2 v₀ hv₀H).2
  refine ⟨B', hB', hBB'.1, hBB'.2, hBq', ?_, hTop⟩
  unfold Height at *
  omega

set_option maxHeartbeats 1000000 in
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

Roots name blocks until `aR S r`: the climb's context `ClimbCtx` carries the premise at the action
time of round `r`; the honest round opening slots' contexts `QuietCtx` read up to support cutoffs of
slots at most `r * R`, before it.

Restated with the delivery premises up to `aR S r`: the bound of its roots `hRoots`, the bundle `ClimbCtxUpTo`'s; the honest round opening slots' bundles `QuietCtxUpTo` read up to support cutoffs of slots at most `r * R`, before it; the attestations (`hSyncF`, `hCatchF`) up to `slotStart S (rs (i + 1) * S.C.R)`, the bound `QuietCtxUpTo.round89r` reads them at for the next opening. -/
theorem quiet_waiting_same_entry_cutoff_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd T₁ r H₂ m i i' : ℕ) (rs : ℕ → ℕ)
    (B B₂ : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (aR S r))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (aR S r))
    (hRoots : RootsNameBlocksUntil S Sched x (aR S r))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT) (hT₁ : tGAT ≤ T₁)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hH₂ : OldHeightAttained S Sched x T₁ H₂)
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hEnd : aR S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hT₁0 : T₁ + Δ S ≤ slotStart S (rs 0 * S.C.R - S.C.k - 1))
    (hii' : i < i') (hi' : i' < m) (hir' : rs (i' + 1) * S.C.R ≤ r * S.C.R)
    (hNoCol : ¬ RootCollisionAtOpening S Sched x rs m)
    (hNo : ∀ (w : V) (t' : ℕ), voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' →
      t' < supportCutoff S (rs (i + 1) * S.C.R) → w ∉ Sched.adv (t' : Int) →
      ¬ ForkChoiceChangeAt S Sched x w t')
    (hNo' : ∀ (w : V) (t' : ℕ), voteTime S (rs i' * S.C.R - S.C.k - 1) ≤ t' →
      t' < supportCutoff S (rs (i' + 1) * S.C.R) → w ∉ Sched.adv (t' : Int) →
      ¬ ForkChoiceChangeAt S Sched x w t')
    (hSyncF : SynchronyFromWakeUpTo S Sched x (Δ_F S) GST fgObject (slotStart S (rs (i + 1) * S.C.R)))
    (hCatchF : CatchUpOnWakeUpTo S Sched x (Δ_F S) GST fgObject (slotStart S (rs (i + 1) * S.C.R)))
    (hWait : ∀ B' : Block V, ProposalAt S Sched x (rs (i + 1) * S.C.R) B' →
      (chainStateOf S.C B').h ≤ (chainStateOf S.C B).h)
    (hTop : (chainStateOf S.C B).h ≤ H₂)
    (hB : ProposalAt S Sched x (rs i * S.C.R) B) (hB₂ : ProposalAt S Sched x (rs i' * S.C.R) B₂) :
    (chainStateOf S.C B).h = (chainStateOf S.C B₂).h →
      (chainStateOf S.C B).T_h = (chainStateOf S.C B₂).T_h := by
  intro hEq
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  have hmono := r_lt_of_lt_of_mono rs m hSeq.mono
  have hri1 : rs (i + 1) ≤ rs (i' + 1) := by
    rcases Nat.lt_or_ge (i + 1) (i' + 1) with h | h
    · exact le_of_lt (hmono _ _ h (by omega))
    · have : i + 1 = i' + 1 := by omega
      rw [this]
  have hir : rs (i + 1) * S.C.R ≤ r * S.C.R := le_trans (Nat.mul_le_mul_right _ hri1) hir'
  -- the case of the next opening
  by_cases hi1 : i' = i + 1
  · subst hi1
    obtain ⟨hs1, C⟩ := quietCtx_of_upTo S Sched x GST tGAT tAwakeEnd r m i rs hDiv hMono
      (hSync.mono (supportCutoff_mono S (by omega))) (hCatch.mono (supportCutoff_mono S (by omega)))
      (hRoots.mono (supportCutoff_mono S (by omega))) hParent hOwner hU hGST hThird hAwake
      hCommittees hEnd hSeq (by omega)
      (opening_round_step hSeq (by omega)) hir hNoCol
      hNo
    have hB0 : ProposalAt S Sched x (rs i * S.C.R - 1 + 1) B := by rw [← hs1]; exact hB
    have h89 := C.round89r rfl B B₂ hB0 hB₂ hSyncF hCatchF
    exact (lem47_chain_state_heights S.C B B₂).2.2.2.2 h89.1 hEq
  have hri : rs (i + 1) < rs i' := hmono _ _ (by omega) (by omega)
  -- the next proposal `B'`, and the heights
  obtain ⟨B', hB', hBB'a, hBB'e, hBq', hhlo, hhhi⟩ := quiet_waiting_next_proposal_upTo S Sched x GST tGAT
    tAwakeEnd T₁ r H₂ m i rs B hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hT₁
    hThird hAwake hCommittees hH₂ hOld hEnd hSeq hT₁0 (by omega) hir hNoCol hNo hSyncF hCatchF hWait hTop hB
  -- the two contexts
  obtain ⟨hs1, C⟩ := quietCtx_of_upTo S Sched x GST tGAT tAwakeEnd r m i rs hDiv hMono
    (hSync.mono (supportCutoff_mono S (by omega))) (hCatch.mono (supportCutoff_mono S (by omega)))
    (hRoots.mono (supportCutoff_mono S (by omega))) hParent hOwner hU hGST hThird hAwake
    hCommittees hEnd hSeq (by omega)
    (opening_round_step hSeq (by omega)) hir hNoCol
    hNo
  obtain ⟨hs1', C'⟩ := quietCtx_of_upTo S Sched x GST tGAT tAwakeEnd r m i' rs hDiv hMono
    (hSync.mono (supportCutoff_mono S (by omega))) (hCatch.mono (supportCutoff_mono S (by omega)))
    (hRoots.mono (supportCutoff_mono S (by omega))) hParent hOwner hU hGST hThird hAwake
    hCommittees hEnd hSeq hi'
    (opening_round_step hSeq hi') hir' hNoCol hNo'
  have hB0 : ProposalAt S Sched x (rs i * S.C.R - 1 + 1) B := by rw [← hs1]; exact hB
  have hB₂0 : ProposalAt S Sched x (rs i' * S.C.R - 1 + 1) B₂ := by rw [← hs1']; exact hB₂
  set s₀ := rs i * S.C.R - 1 with hs₀def
  set s'' := rs (i + 1) * S.C.R with hs''def
  set s₀' := rs i' * S.C.R - 1 with hs₀'def
  set s₃ := rs (i' + 1) * S.C.R with hs₃def
  clear_value s₀ s'' s₀' s₃
  have hsR := C.sR
  have hsR' := C'.sR
  have hs''s₀' : s'' + S.C.R ≤ s₀' + 1 := by
    have h' : (rs (i + 1) + 1) * S.C.R ≤ rs i' * S.C.R := Nat.mul_le_mul_right _ hri
    rw [Nat.add_mul, Nat.one_mul] at h'
    omega
  have hEnd' := C'.cut_end
  have hcut' := C'.cut_le
  -- the climb's context
  have CC : ClimbCtxUpTo S Sched x GST tGAT tAwakeEnd T₁ r H₂ :=
    ⟨hDiv, hMono, hSync, hCatch, hRoots, hParent, hU, hGST, hT₁, hThird, hAwake, hH₂,
      hOld, hEnd⟩
  -- the times
  have hw0 := C.win (le_refl (s₀ + 1))
  have hw'' := C.win (σ := s'') (by omega)
  have hw0' := C'.win (le_refl (s₀' + 1))
  have h0s : rs 0 * S.C.R ≤ s₀ + 1 := C.rs0
  have hT₁s : T₁ + Δ S ≤ slotStart S (s₀' + 1 - S.C.k - 1) := by
    have h1 := slotStart_mono S (show rs 0 * S.C.R - S.C.k - 1 ≤ s₀' + 1 - S.C.k - 1 by
      have := C'.rs0
      omega)
    have h2 : slotStart S (rs 0 * S.C.R - 2 * S.C.k + 1) =
        slotStart S (rs 0 * S.C.R - 2 * S.C.k) + 4 * Δ S := by
      rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
    omega
  have hT₁s₀ : T₁ + Δ S ≤ slotStart S (s₀ + 1 - S.C.k - 1) := by
    have h1 := slotStart_mono S (show rs 0 * S.C.R - S.C.k - 1 ≤ s₀ + 1 - S.C.k - 1 by
      omega)
    have h2 : slotStart S (rs 0 * S.C.R - 2 * S.C.k + 1) =
        slotStart S (rs 0 * S.C.R - 2 * S.C.k) + 4 * Δ S := by
      rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
    omega
  have hss'' : slotStart S (s'' - 1 + 1) = slotStart S s'' := by rw [show s'' - 1 + 1 = s'' by omega]
  have hssμ := slotStart_mono S (show s₀ + 1 - S.C.k - 1 ≤ s'' by omega)
  have hssμ' := slotStart_mono S (show s'' ≤ s₀' + 1 by omega)
  have hssμ'' := slotStart_mono S (show s₀' + 1 - S.C.k - 1 ≤ s₀' + 1 by omega)
  have hvs'' := voteTime_eq S s''
  have hcs'' := supportCutoff_eq S s''
  have hcs''1 := supportCutoff_eq S (s'' + 1)
  have hvs''1 := voteTime_eq S (s'' + 1)
  have hss''1 : slotStart S (s'' + 1) = slotStart S s'' + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hc₀'1 := supportCutoff_eq S (s₀' + 1)
  have hv₀'1 := voteTime_eq S (s₀' + 1)
  have hsc₀'mono := supportCutoff_mono S (show s'' + 1 ≤ s₀' + 1 by omega)
  have hsc₀₃ := supportCutoff_mono S (show s₀' + 1 ≤ s₃ by omega)
  have hcR : supportCutoff S (s₀' + 1) ≤ aR S r := supportCutoff_mono S (by omega)
  have hanc0 := hw0.2
  rw [anchorCW_eq] at hanc0
  have hGSTt : GST ≤ T₁ := le_trans hGST hT₁
  -- the next proposal `B'`
  have hqH : S.P.proposer s'' ∉ Sched.adv ((supportCutoff S s'' : ℕ) : Int) := by
    have h := hSeq.honest (i + 1) (by omega)
    rw [hs''def]
    exact h
  have hqAH : ∀ t : ℕ, tGAT ≤ t → t ≤ supportCutoff S s'' →
      S.P.proposer s'' ∈ Sched.awake (t : Int) ∧ S.P.proposer s'' ∉ Sched.adv (t : Int) := by
    intro t h1 h2
    have hq' : S.P.proposer s'' ∉ Sched.adv (t : Int) :=
      fun hh => hqH (hMono _ _ (by exact_mod_cast h2) hh)
    exact ⟨hAwake t h1 (le_trans h2 (le_trans (supportCutoff_mono S (by omega)) hEnd'))
      _ hq', hq'⟩
  set h := (chainStateOf S.C B).h with hhdef
  clear_value h
  have hh : h + 1 = H₂ ∨ h = H₂ := by
    unfold Height at *
    omega
  have hB₂h : (chainStateOf S.C B₂).h = h := hEq.symm
  -- no honest floor reaches `h + 1` before the later opening's support cutoff
  have hF : ∀ (u : V) (t : ℕ), T₁ + 1 ≤ t → t ≤ supportCutoff S (s₀' + 1) →
      u ∉ Sched.adv (t : Int) → head_height_floor (stateBefore x t u).S ≤ h :=
    fun u t h1 h2 hu => floor_le_before_quiet_upTo CC C' hT₁s h hh B₂ hB₂0 hB₂h u t h1 h2 hu
  -- at the height `1` the entry is the genesis block
  by_cases hh1 : h ≤ 1
  · have hb1 := (lem47_chain_state_heights S.C B B).1.1
    have hb2 := (lem47_chain_state_heights S.C B₂ B₂).1.1
    have g1 := (lem47_chain_state_heights S.C (Block.genesis : Block V) B).2.2.2.2
      (genesis_ancestorEq B) (by rw [chainStateOf_genesis_h]; unfold Height at *; omega)
    have g2 := (lem47_chain_state_heights S.C (Block.genesis : Block V) B₂).2.2.2.2
      (genesis_ancestorEq B₂) (by rw [chainStateOf_genesis_h]; unfold Height at *; omega)
    rw [← g1, ← g2]
  -- no honest validator has `h_j` at least `h` before the later opening's support cutoff
  have hq'H0 : S.P.proposer (s₀' + 1) ∉ Sched.adv ((supportCutoff S (s₀' + 1) : ℕ) : Int) := by
    have h' := hSeq.honest i' (le_of_lt hi')
    rw [hs1'] at h'
    exact h'
  have hq'AH0 : ∀ t : ℕ, tGAT ≤ t → t ≤ supportCutoff S (s₀' + 1) →
      S.P.proposer (s₀' + 1) ∈ Sched.awake (t : Int) ∧
        S.P.proposer (s₀' + 1) ∉ Sched.adv (t : Int) := by
    intro t h1 h2
    have hq' : S.P.proposer (s₀' + 1) ∉ Sched.adv (t : Int) :=
      fun hh => hq'H0 (hMono _ _ (by exact_mod_cast h2) hh)
    exact ⟨hAwake t h1 (by omega) _ hq', hq'⟩
  have hss₀'0 : slotStart S (s₀' + 1) = slotStart S s₀' + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hμ₀ := voteTime_eq S (s₀' + 1 - S.C.k - 1)
  have hμ₀' := slotStart_mono S (show s₀' + 1 - S.C.k - 1 ≤ s₀' by omega)
  have hJlt : ∀ (u : V) (t : ℕ), T₁ + 1 ≤ t → t ≤ supportCutoff S (s₀' + 1) →
      u ∉ Sched.adv (t : Int) → (stateBefore x t u).S.h_j < h := by
    intro u t h1 h2 hu
    rcases h_j_lt_or_genesis_before_cutoff_upTo S Sched x GST tAwakeEnd tGAT
        (slotStart S (s₀' + 1) - Δ S) (supportCutoff S (s₀' + 1)) s₀' h (S.P.proposer (s₀' + 1)) B₂
        hDiv hMono (hSync.mono (by omega)) (hCatch.mono (by omega))
        (hRoots.mono (by omega)) hParent hU hThird hGST
        (by omega) (by omega) (by omega) (fun t' h1' h2' => hq'AH0 t' h1' (by omega)) hB₂0 hB₂h
        (fun u' t' h1' h2' hu' => hF u' t' (by omega) h2' hu')
        (fun w t' h1' h2' hw => hNo' w t' (by rw [hs1']; omega)
          (lt_of_lt_of_le h2' hsc₀₃) hw)
        u t (by omega) h2 hu with hlt | hg
    · exact hlt
    · obtain ⟨⟨D, -, hJD, hjD⟩, -, -⟩ := cachesWitnessed_of_stateBefore S Sched x t u
      by_contra hge
      have h1' : 1 ≤ (chainStateOf S.C D).h_j := by
        rw [← hjD]
        unfold Height at *
        omega
      have hJh := (chainStateOf_J_spec S.C D).2.2 h1'
      rw [← hJD, hg] at hJh
      have hg1 : (chainStateOf S.C (Block.genesis : Block V)).h = 1 :=
        chainStateOf_genesis_h S.C
      rw [hg1, ← hjD] at hJh
      unfold Height at *
      omega
  -- an honest holder of `B'` has its root on `B'`'s chain
  have hRootB' : ∀ (u : V) (t : ℕ), T₁ + 1 ≤ t → t ≤ supportCutoff S (s₀' + 1) →
      u ∉ Sched.adv (t : Int) → B' ∈ (stateBefore x t u).S.T →
      (get_fc_root (stateBefore x t u).S).AncestorEq B' := by
    intro u t h1 h2 hu hB'u
    have hfu := hF u t h1 h2 hu
    have hjh := hJlt u t h1 h2 hu
    have hmx := h_max_le_floor_add_one (stateBefore x t u).S
    have hBh := height_le_h_max S Sched x t u B' hB'u
    have hjl := h_j_lt_h_max S Sched x t u
    have hTE : t ≤ tAwakeEnd := by omega
    have hFB' : (stateBefore x t u).S.F.AncestorEq B' :=
      F_ancestorEq_of_high S Sched x hMono hU hRoots tAwakeEnd t t u u B' hThird hTE hTE hu hu hB'u
        (by unfold Height at *; omega) (max_le (by omega) (by omega))
    rcases root_cases (stateBefore x t u).S with ⟨hJ, hm1, hc⟩ | ⟨hFr, -⟩
    · rw [hJ]
      by_contra hJB
      have hct := fg_contest_true_of _ B' hm1 hB'u hFB'
        (by rw [σ_eq_of_stateBefore S Sched x t u B' hB'u]; unfold Height at *; omega) hJB
      rw [hc] at hct
      cases hct
    · rw [hFr]
      exact hFB'
  -- `B'` reaches every honest validator one delay after its proposal
  have hDel : ∀ (u : V) (t : ℕ), slotStart S s'' + 1 + Δ S ≤ t → t ≤ supportCutoff S (s₀' + 1) →
      u ∉ Sched.adv (t : Int) → B' ∈ (stateBefore x t u).S.T := by
    intro u t h1 h2 hu
    have hqb : S.P.proposer s'' ∉ Sched.adv ((slotStart S s'' : ℕ) : Int) :=
      (hqAH _ (by omega) (by omega)).2
    have hwin : ∀ t' : ℕ, slotStart S s'' + 1 ≤ t' → t' ≤ slotStart S s'' + 1 + Δ S →
        u ∈ Sched.awake (t' : Int) ∧ u ∉ Sched.adv (t' : Int) := by
      intro t' h1' h2'
      have hu' : u ∉ Sched.adv (t' : Int) := fun hh => hu (hMono _ _ (by exact_mod_cast
        (show t' ≤ t by omega)) hh)
      exact ⟨hAwake t' (by omega) (by omega) u hu', hu'⟩
    have hhu : u ∉ Sched.adv ((slotStart S s'' + 1 + Δ S : ℕ) : Int) :=
      fun hh => hu (hMono _ _ (by exact_mod_cast h1) hh)
    rcases held_spread_upTo S Sched x GST tAwakeEnd (slotStart S s'' + 1) (slotStart S s'' + 1) _ u B'
        hDiv hMono (hSync.mono (by omega)) (hCatch.mono (by omega))
        (hRoots.mono (by omega)) hParent hU hThird le_rfl
        (by omega) (by omega) (honest_config_succ x hDiv hqb) hBq' hwin with ⟨hBu, -⟩ | hlo
    · exact (stateBefore_grows x hDiv u h1).1 hBu
    · exfalso
      have hfu := hF u (slotStart S s'' + 1 + Δ S) (by omega) (by omega) hhu
      have hjh := hJlt u (slotStart S s'' + 1 + Δ S) (by omega) (by omega) hhu
      have hmx := h_max_le_floor_add_one (stateBefore x (slotStart S s'' + 1 + Δ S) u).S
      have hjl := h_j_lt_h_max S Sched x (slotStart S s'' + 1 + Δ S) u
      unfold Height at *
      omega
  -- the window's context at the next opening, inside the first opening's range
  have W1 : WinCtxUpTo S Sched x GST tGAT tAwakeEnd r m (i + 1) rs (s'' - 1) := by
    refine ⟨hDiv, hMono, hSync.mono (le_trans (supportCutoff_mono S (by omega)) hcR),
      hCatch.mono (le_trans (supportCutoff_mono S (by omega)) hcR),
      hRoots.mono (le_trans (supportCutoff_mono S (by omega)) hcR), hParent, hOwner, hU, hGST,
      hThird, hAwake, hCommittees, hEnd, hSeq, by omega, by rw [← hs''def]; omega, by omega, ?_⟩
    intro w t' h1 h2 h3
    exact C.hNo w t' (le_trans (voteTime_mono S (by omega)) h1)
      (lt_of_lt_of_le h2 (supportCutoff_mono S (by omega))) h3
  have hB'P : ProposalAt S Sched x (s'' - 1 + 1) B' := by
    rw [show s'' - 1 + 1 = s'' by omega]
    exact hB'
  have hsc''1 := supportCutoff_eq S (s'' + 1)
  -- the round's base at `B'`'s slot
  obtain ⟨hHeld', hBase', -⟩ := W1.base hNoCol B' hB'P (by
    intro v hv
    rw [show s'' - 1 + 1 = s'' by omega] at hv ⊢
    have hvb : v ∉ Sched.adv ((supportCutoff S (s'' + 1) : ℕ) : Int) := (Finset.mem_sdiff.1 hv).2
    exact hRootB' v _ (by omega) (by omega) hvb (hDel v _ (by omega) (by omega) hvb))
  rw [show s'' - 1 + 1 = s'' by omega] at hHeld' hBase'
  have hmemR : ∀ a b : ℕ, a ≤ b → b ≤ s₃ → ∀ u ∈ roundMembers S Sched b,
      u ∈ roundMembers S Sched a := fun a b hab hb u hu =>
    (roundMembers_mono S Sched a b tAwakeEnd hMono hab
      (le_trans (supportCutoff_mono S hb) hEnd')).1 hu
  -- the chain invariant relative to `B'`, carried to the slot before the later opening
  have hCarry : ∀ n, s'' + n ≤ s₀' →
      HonestChainExtends S Sched x (Hon S Sched (s'' + n)) B' (s'' + n) := by
    intro n
    induction n with
    | zero =>
      intro _
      simpa using hBase'
    | succ n ih =>
      intro hn
      have ihn := ih (by omega)
      rw [show s'' + (n + 1) = s'' + n + 1 by omega]
      -- the times of the slot `σ := s'' + n`
      have hA0 : anchorCW S tGAT ≤ slotStart S (s'' + n + 1) :=
        le_trans hw0.2 (slotStart_mono S (by omega))
      have hA1 : anchorCW S tGAT ≤ slotStart S (s'' + n + 1 + 1) :=
        le_trans hw0.2 (slotStart_mono S (by omega))
      have hdw0 := dutyWindowStart_of_anchor S tGAT (s'' + n) hA0
      have hdw1 := dutyWindowStart_of_anchor S tGAT (s'' + n + 1) hA1
      have hMaj0 := committee_majority_of_committeeSleepiness S Sched _ (s'' + n) hCommittees hA0
      have hMaj1 := committee_majority_of_committeeSleepiness S Sched _ (s'' + n + 1) hCommittees
        hA1
      have hscn := supportCutoff_mono S (show s'' + n + 1 + 1 ≤ s₀' + 1 by omega)
      have hscn1 := supportCutoff_mono S (show s'' + n + 1 ≤ s₀' + 1 by omega)
      have hvn := voteTime_eq S (s'' + n)
      have hvn1 := voteTime_eq S (s'' + n + 1)
      have hcn1 := supportCutoff_eq S (s'' + n + 1)
      have hcn2 := supportCutoff_eq S (s'' + n + 1 + 1)
      have hvn2 := voteTime_eq S (s'' + n + 1 + 1)
      have hssn : slotStart S (s'' + n + 1) = slotStart S (s'' + n) + 4 * Δ S := by
        rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
      have hssn1 : slotStart S (s'' + n + 1 + 1) = slotStart S (s'' + n + 1) + 4 * Δ S := by
        rw [slotStart_eq, slotStart_eq S (s'' + n + 1), Nat.mul_add, Nat.mul_one]
      have hssn0 := slotStart_mono S (show s'' ≤ s'' + n by omega)
      have hdwv0 := dutyWindowStart_le_voteTime S (s'' + n)
      have hdwv1 := dutyWindowStart_le_voteTime S (s'' + n + 1)
      have hfzn := viewFreeze_eq S (s'' + n)
      -- the members' windows
      have hwinn : ∀ σ : ℕ, σ + 1 ≤ s₀' + 1 → tGAT + Δ S ≤ dutyWindowStart S σ →
          ∀ v ∈ Hon S Sched σ, ∀ t : ℕ, dutyWindowStart S σ ≤ t → t ≤ supportCutoff S (σ + 1) →
          v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int) := by
        intro σ hσ hdσ v hv t h1 h2
        have hvb : v ∉ Sched.adv ((supportCutoff S (σ + 1) : ℕ) : Int) := (Finset.mem_sdiff.1 hv).2
        have hv' : v ∉ Sched.adv (t : Int) := fun hh => hvb (hMono _ _ (by exact_mod_cast h2) hh)
        have hscσ := supportCutoff_mono S hσ
        exact ⟨hAwake t (by omega) (by omega) v hv', hv'⟩
      have hvoters : ∀ σ : ℕ, σ + 1 ≤ s₀' + 1 → tGAT + Δ S ≤ dutyWindowStart S σ →
          ∀ u ∈ S.P.committee σ ∩ Hon S Sched σ, u ∈ Hon S Sched σ ∧ u ∈ S.P.committee σ ∧
            ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = σ ∧
              ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S σ) ∧
                (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
                  x[i + 1].sent - x[i].sent := by
        intro σ hσ hdσ u hu
        obtain ⟨hK, huH⟩ := Finset.mem_inter.1 hu
        have hdv := dutyWindowStart_le_voteTime S σ
        have hvc : voteTime S σ ≤ supportCutoff S (σ + 1) := by
          have := supportCutoff_eq S (σ + 1)
          have := voteTime_succ S σ
          omega
        obtain ⟨i', vote, hl, hvi, hvs, hsent⟩ := honest_votes_of_window S Sched x σ u hDiv hMono
          (fun t h1 h2 => (hwinn σ hσ hdσ u huH t h1 (by omega)).1)
          (hwinn σ hσ hdσ u huH _ hdv hvc).2 hK
        exact ⟨huH, hK, vote, hvi, hvs, i', hl, hsent⟩
      -- the frames relative to `B'`
      have hv''n : voteTime S s'' ≤ voteTime S (s'' + n) := voteTime_mono S (by omega)
      have hv''n1 : voteTime S s'' ≤ voteTime S (s'' + n + 1) := voteTime_mono S (by omega)
      have hthF : voteTime S s'' ≤ viewFreeze S (s'' + n) := by omega
      have hT₁v : T₁ + 1 ≤ voteTime S (s'' + n + 1) := by omega
      have hvc1 : voteTime S (s'' + n + 1) ≤ supportCutoff S (s₀' + 1) := by omega
      have hT₁c : T₁ + 1 ≤ supportCutoff S (s'' + n + 1 + 1) := by omega
      have hvc2 : voteTime S s'' ≤ supportCutoff S (s'' + n + 1 + 1) := by omega
      have hvc12 : voteTime S (s'' + n + 1) ≤ supportCutoff S (s'' + n + 1 + 1) := by omega
      have hle1 : s'' + 1 ≤ s'' + n + 1 + 1 := by omega
      have hle2 : s'' + n + 1 + 1 ≤ s₃ := by omega
      have hSF : ∀ w ∈ Hon S Sched (s'' + n + 1), StepFrameAt S Sched x B' (s'' + n) w := by
        intro w hw
        have hwb : w ∉ Sched.adv ((supportCutoff S (s'' + n + 1 + 1) : ℕ) : Int) :=
          (Finset.mem_sdiff.1 hw).2
        have hws'' : w ∈ Hon S Sched s'' := hmemR (s'' + 1) (s'' + n + 1 + 1) hle1 hle2 w hw
        have hBw := hHeld' w hws''
        have hwv : w ∉ Sched.adv ((voteTime S (s'' + n + 1) : ℕ) : Int) :=
          fun hh => hwb (hMono _ _ (by exact_mod_cast hvc12) hh)
        have hBw1 : B' ∈ (stateBefore x (voteTime S (s'' + n + 1)) w).S.T :=
          (stateBefore_grows x hDiv w hv''n1).1 hBw
        have hBw2 : B' ∈ (stateBefore x (supportCutoff S (s'' + n + 1 + 1)) w).S.T :=
          (stateBefore_grows x hDiv w hvc2).1 hBw
        have hr1 := hRootB' w (voteTime S (s'' + n + 1)) hT₁v hvc1 hwv hBw1
        have hf1 := hF w (voteTime S (s'' + n + 1)) hT₁v hvc1 hwv
        have hr2 := hRootB' w (supportCutoff S (s'' + n + 1 + 1)) hT₁c hscn hwb hBw2
        have hf1' : head_height_floor (stateBefore x (voteTime S (s'' + n + 1)) w).S ≤
            (chainStateOf S.C B').h := by
          unfold Height at *
          omega
        exact stepFrame_of_compat S Sched x hDiv B' B' (s'' + n) w (voteTime S s'')
          (ancestorEq_refl B') hBw hthF hv''n1 ((compatible_iff _ _).2 (Or.inl hr1)) hf1'
          ((compatible_iff _ _).2 (Or.inl hr2))
      exact lem79_step_sets_upTo S Sched x GST (s'' + n) (Hon S Sched (s'' + n))
        (Hon S Sched (s'' + n + 1)) (fun s => S.P.committee s ∩ Hon S Sched s) B' hDiv hMono
        (hSync.mono (le_trans (supportCutoff_mono S (by omega)) hcR))
        (hCatch.mono (le_trans (supportCutoff_mono S (by omega)) hcR))
        (hRoots.mono (le_trans (supportCutoff_mono S (by omega)) hcR)) hParent
        hOwner (by omega) ihn
        (hmemR (s'' + n + 1) (s'' + n + 1 + 1) (Nat.le_succ _) (by omega))
        (hwinn (s'' + n) (by omega) hdw0) (hwinn (s'' + n + 1) (by omega) hdw1)
        (hvoters (s'' + n) (by omega) hdw0) (hvoters (s'' + n + 1) (by omega) hdw1)
        (fun w _ => (counting_of_committee_majority S Sched x (s'' + n) (voteTime S (s'' + n + 1))
          (Hon S Sched (s'' + n)) w hMaj0).2.2)
        (fun v _ => (counting_of_committee_majority S Sched x (s'' + n + 1)
          (supportCutoff S (s'' + n + 1 + 1)) (Hon S Sched (s'' + n + 1)) v hMaj1).2.1)
        (fun w hw => (hSF w hw).1) (fun w hw => (hSF w hw).2.1) (fun w hw => (hSF w hw).2.2)
  have hCE := hCarry (s₀' - s'') (by omega)
  rw [show s'' + (s₀' - s'') = s₀' by omega] at hCE
  have hCE1 := hCarry (s₀' - 1 - s'') (by omega)
  rw [show s'' + (s₀' - 1 - s'') = s₀' - 1 by omega] at hCE1
  -- the later opening's proposer
  have hq'H : S.P.proposer (s₀' + 1) ∉ Sched.adv ((supportCutoff S (s₀' + 1) : ℕ) : Int) := by
    have h' := hSeq.honest i' (le_of_lt hi')
    rw [hs1'] at h'
    exact h'
  have hq'AH : ∀ t : ℕ, tGAT ≤ t → t ≤ supportCutoff S (s₀' + 1) →
      S.P.proposer (s₀' + 1) ∈ Sched.awake (t : Int) ∧
        S.P.proposer (s₀' + 1) ∉ Sched.adv (t : Int) := by
    intro t h1 h2
    have hq' : S.P.proposer (s₀' + 1) ∉ Sched.adv (t : Int) :=
      fun hh => hq'H (hMono _ _ (by exact_mod_cast h2) hh)
    exact ⟨hAwake t h1 (by omega) _ hq', hq'⟩
  have hss₀' : slotStart S (s₀' + 1) = slotStart S s₀' + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv₀' := voteTime_eq S s₀'
  have hc₀' := supportCutoff_eq S s₀'
  have hss₀'1 := slotStart_mono S (show s'' ≤ s₀' by omega)
  have hq'b : S.P.proposer (s₀' + 1) ∉ Sched.adv ((slotStart S (s₀' + 1) : ℕ) : Int) :=
    (hq'AH _ (by omega) (by omega)).2
  have hB'q : B' ∈ (stateBefore x (slotStart S (s₀' + 1)) (S.P.proposer (s₀' + 1))).S.T :=
    hDel _ _ (by omega) (by omega) hq'b
  have hRq := hRootB' _ _ (by omega) (by omega) hq'b hB'q
  have hFq := hF _ (slotStart S (s₀' + 1)) (by omega) (by omega) hq'b
  have hFB'q := ancestorEq_trans (F_ancestorEq_fc_root_of_stateBefore S Sched x _ _) hRq
  have hVHq : B' ∈ (fg_to_ac (stateBefore x (slotStart S (s₀' + 1)) (S.P.proposer (s₀' + 1))).S).viable_heads := by
    rw [mem_viable_heads_iff, fc_root_eq]
    refine ⟨hB'q, hFB'q, hRq, ?_⟩
    rw [σ_eq_of_stateBefore S Sched x _ _ B' hB'q]
    unfold Height at *
    omega
  have hF3p : ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S (s₀' + 1)) (S.P.proposer (s₀' + 1))).S).tree,
      W ∈ (fg_to_ac (stateBefore x (slotStart S (s₀' + 1)) (S.P.proposer (s₀' + 1))).S).viable_heads ∧
      B'.AncestorEq W :=
    ⟨B', (mem_fg_to_ac_tree _ _).2 ⟨hB'q, hFB'q⟩, hVHq, ancestorEq_refl B'⟩
  -- the anchor is comparable with `B'`
  have hcq' : supportCutoff S (s₀' - 1 + 1) ≤ supportCutoff S (s₀' + 1) :=
    supportCutoff_mono S (by omega)
  have hq'Hm : S.P.proposer (s₀' + 1) ∈ Hon S Sched (s₀' - 1) :=
    Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun hh => hq'H (hMono _ _ (by exact_mod_cast hcq') hh)⟩
  have hAcmp : (get_anchor (stateBefore x (slotStart S (s₀' + 1)) (S.P.proposer (s₀' + 1))).A
      (fg_to_ac (stateBefore x (slotStart S (s₀' + 1)) (S.P.proposer (s₀' + 1))).S)
      ((slotStart S (s₀' + 1) : ℕ) : Int)).AncestorEq B' ∨
      B'.AncestorEq (get_anchor (stateBefore x (slotStart S (s₀' + 1)) (S.P.proposer (s₀' + 1))).A
      (fg_to_ac (stateBefore x (slotStart S (s₀' + 1)) (S.P.proposer (s₀' + 1))).S)
      ((slotStart S (s₀' + 1) : ℕ) : Int)) := by
    rcases get_anchor_cases_locked (stateBefore x (slotStart S (s₀' + 1)) (S.P.proposer (s₀' + 1))).A
      (fg_to_ac (stateBefore x (slotStart S (s₀' + 1)) (S.P.proposer (s₀' + 1))).S)
      ((slotStart S (s₀' + 1) : ℕ) : Int) with ha | ⟨-, e, he, hl, hAe⟩
    · left
      rw [ha, fc_root_eq]
      exact hRq
    · have hl' := hl
      simp only [is_live_iff] at hl'
      have hA' : anchorCW S tGAT ≤ slotStart S (s₀' - 1 + 1 + 1) :=
        le_trans hw0.2 (slotStart_mono S (by omega))
      have hdw' := dutyWindowStart_of_anchor S tGAT (s₀' - 1 + 1) hA'
      have hsc' := supportCutoff_eq S (s₀' - 1 + 1)
      have hv' := voteTime_eq S (s₀' - 1 + 1)
      have hv2' := voteTime_eq S (s₀' - 1 + 2)
      have hss' : slotStart S (s₀' - 1 + 1) = slotStart S s₀' := by
        rw [show s₀' - 1 + 1 = s₀' by omega]
      have hss2' : slotStart S (s₀' - 1 + 2) = slotStart S (s₀' + 1) := by
        rw [show s₀' - 1 + 2 = s₀' + 1 by omega]
      have hdwq : tGAT ≤ dutyWindowStart S (s₀' - 1 + 1) := by omega
      have hlt1 : supportCutoff S (s₀' - 1 + 1) < slotStart S (s₀' + 1) := by omega
      have hlt2 : slotStart S (s₀' + 1) ≤ voteTime S (s₀' - 1 + 2) := by omega
      have hcq : slotStart S (s₀' + 1) ≤ supportCutoff S (s₀' + 1) := by omega
      rcases live_lock_entry_source S Sched x (s₀' - 1) (slotStart S (s₀' + 1)) _ hDiv
          (fun t h1' h2' => hq'AH t (le_trans hdwq (le_trans (dutyWindowStart_mono S (by omega)) h1')) (le_trans h2' hcq)) hlt1 hlt2 e he
          hl'.1 with
        ⟨C₁, hC₁, heC₁⟩ | ⟨A₃, hR₃, e', he', hl₃, hee'⟩
      · have hBC₁ := hCE1.2.2 _ hq'Hm C₁ hC₁
        exact ancestorEq_compatible (ancestorEq_trans hAe heC₁) hBC₁
      · have hcmp := hCE1.2.1 _ hq'Hm A₃ hR₃ e' he' hl₃
        rcases (compatible_iff _ _).1 hcmp with he'B | hBe'
        · exact Or.inl (ancestorEq_trans hAe (ancestorEq_trans hee' he'B))
        · exact ancestorEq_compatible (ancestorEq_trans hAe hee') hBe'
  -- the honest votes of slot `s₀'` extend `B'`
  have hA₀' : anchorCW S tGAT ≤ slotStart S (s₀' + 1) := le_trans hw0.2 (slotStart_mono S (by omega))
  have hMaj₀' := committee_majority_of_committeeSleepiness S Sched _ s₀' hCommittees hA₀'
  have hdw₀' := dutyWindowStart_of_anchor S tGAT s₀' hA₀'
  set Hs : Finset V := S.P.committee s₀' ∩ Hon S Sched s₀' with hHsdef
  have hex : ∀ u ∈ Hs, ∃ H_u : Block V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s₀') ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s₀' H_u.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H_u ∈ (stateBefore x (voteTime S s₀') u).S.T ∧ B'.AncestorEq H_u := by
    intro u hu
    obtain ⟨hK, huH⟩ := Finset.mem_inter.1 hu
    have hub : u ∉ Sched.adv ((supportCutoff S (s₀' + 1) : ℕ) : Int) := (Finset.mem_sdiff.1 huH).2
    have hdv := dutyWindowStart_le_voteTime S s₀'
    have hvc : voteTime S s₀' ≤ supportCutoff S (s₀' + 1) := by omega
    obtain ⟨i', vote, hl, -, -, hsent⟩ := honest_votes_of_window S Sched x s₀' u hDiv hMono
      (fun t h1 h2 => hAwake t (by omega) (by omega) u
        (fun hh => hub (hMono _ _ (by exact_mod_cast (show t ≤ supportCutoff S (s₀' + 1) by
          omega)) hh)))
      (fun hh => hub (hMono _ _ (by exact_mod_cast hvc) hh)) hK
    obtain ⟨H_u, hT, hvt, hBH⟩ := hCE.1 u huH vote ⟨i', hl, hsent⟩
    subst hvt
    exact ⟨H_u, ⟨i', hl, hsent⟩, hT, hBH⟩
  choose Hc hHc using hex
  let Hf : V → Block V := fun u => if h' : u ∈ Hs then Hc u h' else B'
  have hHf : ∀ u (hu : u ∈ Hs), Hf u = Hc u hu := fun u hu => dif_pos hu
  obtain ⟨iB₂, hlB₂, hsentB₂⟩ := hB₂0
  have hB'P₂ : B'.AncestorEq B₂.parent := by
    rcases hAcmp with hAB | hBA
    · refine (proposal_parent_extends_majority_block_upTo S Sched x GST s₀' iB₂ Hs Hf B' B₂ _ hDiv hMono
        (hSync.mono (le_trans (supportCutoff_mono S (by omega)) hcR))
        (hCatch.mono (le_trans (supportCutoff_mono S (by omega)) hcR))
        (hRoots.mono (le_trans (supportCutoff_mono S (by omega)) hcR))
        hParent hOwner (by omega) ?_ ?_
        (fun t h1 h2 => hq'AH t (by omega) (by omega)) hlB₂ hsentB₂ hF3p hAB).1
      · intro u hu
        rw [hHf u hu]
        obtain ⟨hK, huH⟩ := Finset.mem_inter.1 hu
        have hub : u ∉ Sched.adv ((supportCutoff S (s₀' + 1) : ℕ) : Int) :=
          (Finset.mem_sdiff.1 huH).2
        exact ⟨hK, fun hh => hub (hMono _ _ (by exact_mod_cast (show slotStart S (s₀' + 1) ≤
          supportCutoff S (s₀' + 1) by omega)) hh), (hHc u hu).1, (hHc u hu).2.1, (hHc u hu).2.2⟩
      · intro votes_p support_p hP
        rw [hP.1]
        exact (counting_of_committee_majority S Sched x s₀' (slotStart S (s₀' + 1))
          (Hon S Sched s₀') _ hMaj₀').2.1
    · exact ancestorEq_trans hBA (get_anchor_ancestorEq_proposal_parent S Sched x (s₀' + 1) iB₂ B₂
        _ hlB₂ hsentB₂)
  obtain ⟨-, -, hB₂par?, -⟩ := proposal_parent_walk_end S Sched x s₀' iB₂ B₂ _ hlB₂ hsentB₂
  have hPB₂ := GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_parent? hB₂par?
  have hBB₂ := ancestorEq_trans hBB'a (ancestorEq_trans hB'P₂ hPB₂)
  exact (lem47_chain_state_heights S.C B B₂).2.2.2.2 hBB₂ (by rw [← hhdef, hB₂h])

end GoldilocksCorrectness.Proofs.Executions

