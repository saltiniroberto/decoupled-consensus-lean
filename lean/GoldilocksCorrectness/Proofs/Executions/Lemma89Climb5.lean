module
public import GoldilocksCorrectness.Proofs.View.Bridges
public import GoldilocksCorrectness.Proofs.Executions.Lemma89ClimbLate
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Count
public import GoldilocksCorrectness.Statements.Executions.Lemma89CountDefs
public import GoldilocksCorrectness.Proofs.Routines.Schedule

@[expose] public section

/-!
# Lemma 89, part B: the climb to the first honest fast block (three span lengths, count 9)

The climb's assembly on the span premise of record, `OpeningsOutsideWaitsAndWindows`, from
`scratch/goldilocks_healed/probe_recount_1.lean` (`climb_to_fast_block5`):

- `slotStart_div_le`: the slot `τ / 4Δ` holds the time `τ`;
- `opening_proposal_held`, `opening_proposal_unique`: with no root collision at an opening, an
  opening's proposal has the opening's slot, is held by its proposer one time unit after the slot's
  start, and is the opening's only proposal;
- `climb_count_before`: with the threshold `H₂` at `T₁` and every honest attestation before
  `aR S r` at most `H₂`, there are two spans of `δt` slots and four spans of `k + 2` slots outside
  which
  at most six honest round opening slots `i < m` with `rs i * R < r * R` lie: four with a
  fork-choice change in their round (one per kind), two quiet and rising or the quiet one whose
  round holds `r * R`; the waiting ones lie in the wait span at their height's entry
  (`quiet_waiting_same_entry_cutoff`);
- `after_of_before`: the counting step, at most six outside honest round opening slots before a
  slot and `need` in all leave `need − 6` at or after it;
- `climb_to_fast_block`: the climb, the collision disjunct or the first honest fast block one
  height above the threshold, with three honest round opening slots at least `k + 2` slots after
  its round.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff anchorCW)
open GoldilocksCorrectness.Proofs.Routines (after_of_before one_le_Δ slotStart_div_le slotStart_eq
  slotStart_mono supportCutoff_eq supportCutoff_mono supportCutoff_succ_eq voteTime_eq
  voteTime_mono)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_T_h_spec lem47_chain_state_heights)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (mem_viable_heads_iff)

open GoldilocksCorrectness.Proofs.Routines (slot_lt_of_ancestorEq_of_treeClosed)
open GoldilocksCorrectness.Statements.Routines (TreeClosed)

open GoldilocksCorrectness.Proofs.Routines (anchorCW_eq)

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

/-! ## Kit -/

/-- **An opening's proposal has the opening's slot and is held by its proposer.** With the honest
openings `rs 0 < … < rs m` and no opening's proposal colliding with a block its proposer held: a
proposal `B` of opening `j ≤ m` has slot `rs j * R`, and the proposer of that slot holds `B` one
time unit after the slot's start.

Why: `B`'s parent is a viable head of its proposer (`proposal_parent_viable_head`), its root is new
to the proposer (no collision), so the proposer holds it after its tick
(`lem22a_proposer_holds_own_proposal`); the walk's end gives its slot (`proposal_parent_walk_end`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tGAT`, `tAwakeEnd`: the phase; `m`:
  the index of the last honest round opening slot; `j`: the index of an honest round opening slot; `rs`: the rounds of the honest round opening slots; `B`: the proposal. -/
theorem opening_proposal_held (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (tGAT tAwakeEnd m j : ℕ) (rs : ℕ → ℕ) (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hj : j ≤ m) (hNoCol : ¬ RootCollisionAtOpening S Sched x rs m)
    (hB : ProposalAt S Sched x (rs j * S.C.R) B) :
    B.slot = rs j * S.C.R ∧
      B ∈ (stateBefore x (slotStart S (rs j * S.C.R) + 1) (S.P.proposer (rs j * S.C.R))).S.T := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hmono := r_lt_of_lt_of_mono rs m hSeq.mono
  have h0j : rs 0 * S.C.R ≤ rs j * S.C.R := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h]
    · exact Nat.mul_le_mul_right _ (le_of_lt (hmono 0 j h hj))
  obtain ⟨h2k, -⟩ := window_after_anchor S Sched rs m tGAT tAwakeEnd (rs j * S.C.R) hSeq h0j
  set s'' := rs j * S.C.R with hs''def
  clear_value s''
  have hss'' : slotStart S (s'' - 1 + 1) = slotStart S s'' := by rw [show s'' - 1 + 1 = s'' by omega]
  have hB'0 : ProposalAt S Sched x (s'' - 1 + 1) B := by
    rw [show s'' - 1 + 1 = s'' by omega]
    exact hB
  have hPV' := proposal_parent_viable_head S Sched x (s'' - 1) B _ hB'0
  have hPV'' := (mem_viable_heads_iff _ _).1 hPV'
  obtain ⟨iB'', hlB'', hsentB''⟩ := hB'0
  obtain ⟨hslot, -, hB'par?, -⟩ := proposal_parent_walk_end S Sched x (s'' - 1) iB'' B _
    hlB'' hsentB''
  have hPB' := GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_parent? hB'par?
  have hRootNew' : ∀ B₁ ∈ (stateBefore x (slotStart S (s'' - 1 + 1)) (S.P.proposer (s'' - 1 + 1))).S.T,
      B₁.root ≠ B.root := by
    intro B₁ hB₁ heq
    apply hNoCol
    rw [GoldilocksCorrectness.Proofs.View.rootCollisionAtOpening_unfold]
    refine ⟨j, hj, B, ?_, ?_⟩
    · rw [← hs''def]
      exact hB
    · rw [← hs''def]
      rw [GoldilocksCorrectness.Proofs.View.rootCollisionAtProposal_unfold]
      show ∃ B₁ ∈ (stateBefore x (slotStart S s'') (S.P.proposer s'')).S.T, B₁.root = B.root
      rw [show s'' - 1 + 1 = s'' by omega] at hB₁
      exact ⟨B₁, hB₁, heq⟩
  have hBq := lem22a_proposer_holds_own_proposal S Sched x (s'' - 1) iB'' B _ hDiv hMono hlB''
    hsentB'' hRootNew' hPV''.1
    ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans hPV''.2.1 hPB')))
  have hti := (time_of_lbl_tickAllAwake x hlB'').2
  refine ⟨hslot.trans (by omega : s'' - 1 + 1 = s''), ?_⟩
  have hle : iB'' + 1 ≤ stepBefore x (slotStart S s'' + 1) :=
    (time_lt_iff_le_stepBefore x hDiv (t := slotStart S s'' + 1) (by omega)).1
      (by rw [hti, hss'']; omega)
  have h' := mem_T_mono x _ hle hBq
  rw [show s'' - 1 + 1 = s'' by omega] at h'
  exact h'

/-- **An opening has one proposal.** With the honest round opening slots of the rounds `rs 0 < … < rs m`, unforgeability
and no opening's proposal colliding with a block its proposer held: two proposals of opening
`j ≤ m` are equal.

Why: the proposer holds the first one one time unit after the slot's start, with the slot's number
(`opening_proposal_held`), and is honest through that time (`HonestOpeningSeq.honest`); the only
block of that slot an honest validator holds is the proposal (`only_block_of_unforgeability`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tGAT`, `tAwakeEnd`: the phase; `m`:
  the index of the last honest round opening slot; `j`: the index of an honest round opening slot; `rs`: the rounds of the honest round opening slots; `B`, `B'`: the
  proposals. -/
theorem opening_proposal_unique (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (tGAT tAwakeEnd m j : ℕ) (rs : ℕ → ℕ) (B B' : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hj : j ≤ m) (hNoCol : ¬ RootCollisionAtOpening S Sched x rs m)
    (hB : ProposalAt S Sched x (rs j * S.C.R) B) (hB' : ProposalAt S Sched x (rs j * S.C.R) B') :
    B = B' := by
  have hΔ := one_le_Δ S
  obtain ⟨hslot, hheld⟩ := opening_proposal_held S Sched x tGAT tAwakeEnd m j rs B hDiv hMono hSeq
    hj hNoCol hB
  have hcut : slotStart S (rs j * S.C.R) + 1 ≤ supportCutoff S (rs j * S.C.R) := by
    have h1 := supportCutoff_eq S (rs j * S.C.R)
    have h2 := voteTime_eq S (rs j * S.C.R)
    omega
  have hp : HonestThroughTime Sched (((slotStart S (rs j * S.C.R) + 1 : ℕ)) : Int)
      (S.P.proposer (rs j * S.C.R)) := by
    intro t' ht' h
    exact hSeq.honest j hj (hMono _ _ (le_trans ht' (by exact_mod_cast hcut)) h)
  exact only_block_of_unforgeability S Sched x hU (rs j * S.C.R) (slotStart S (rs j * S.C.R) + 1)
    B' B _ _ hp rfl hB' hheld hslot

/-! ## The count before the fast block's round -/

open Classical in
/-- **At most six openings before the climb's end lie outside the spans the climb places.** In the
climb's context (the execution assumptions and unforgeability, every honest validator awake in
`[tGAT, tAwakeEnd]`, fewer than a third of the validators in the adversary set up to its end,
committee sleepiness from `anchorCW S tGAT`, the honest round opening slots of the rounds `rs 0 < … < rs m`, the threshold
`H₂` attained at `T₁` with `tGAT ≤ T₁` and `T₁ + Δ` at most the start of slot `rs 0 * R − k − 1`,
every honest attestation before `aR S r ≤ tAwakeEnd` at most `H₂`, no opening's proposal colliding
with a block its proposer held): there are two spans of `δt` slots and four spans of `k + 2` slots
such that at most six honest round opening slots `i < m` with `rs i * R < r * R` have their first
slot outside all of them; the one whose round holds `r * R` is among them.

The spans: the four of `k + 2` slots start at the slots of the four times of
`fork_choice_change_kinds`; the two of `δt` slots at the slots of the entries of the waiting
openings at the heights `H₂ − 1` and `H₂`.

Why: such an opening either has a `ForkChoiceChangeAt` of a validator outside the adversary set
from the vote time of slot `rs i * R − k − 1` to before the support cutoff of slot
`min (rs (i + 1) * R) (r * R)`, or none. With one, the change is within one delay after one of the
four times; outside the span of that kind it is not in the opening's window
(`fork_choice_change_in_window_span`), so it is in its round, and two openings with a change of one
kind in their rounds would put the later one in that kind's span: at most four. With none and the
next slot at or before `r * R`, the opening is quiet with its base, and Lemma 89r
(`QuietCtx.round89r`) makes it rising or waiting; with none and the next slot after `r * R`, it is
the one whose round holds `r * R`. The rising ones and that one are at most two
(`quiet_rising_before_fast_round_le_two_cutoff`). A waiting one has its
proposal at height `H₂ − 1` or `H₂` (B11 and `hOld` bound it by `H₂`;
`quiet_waiting_next_proposal`), shares its entry with every waiting opening at that height
(`quiet_waiting_same_entry_cutoff`), and its first slot is less than `δt` slots after that
entry's: it lies in that height's wait span.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `H₂`: the threshold; `m`: the index of the last honest round opening slot; `rs`: the rounds of the honest round opening slots.

Roots name blocks until `aR S r`: `fork_choice_change_kinds` and the climb's steps read up to the
action time of round `r`. -/
theorem climb_count_before (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd T₁ r H₂ m : ℕ) (rs : ℕ → ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
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
    ∃ (waits : Fin 2 → ℕ) (w4 : Fin 4 → ℕ),
      ((Finset.range m).filter (fun i => rs i * S.C.R < r * S.C.R ∧
        OutsideSpans S rs waits S.C.δt w4 (S.C.k + 2) i)).card ≤ 6 := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  have hmono := r_lt_of_lt_of_mono rs m hSeq.mono
  obtain ⟨τ, hτ⟩ := fork_choice_change_kinds S Sched x GST tGAT tAwakeEnd T₁ r H₂ hDiv hMono hSync
    hCatch hRoots hParent hU hGST hT₁ hThird hAwake hH₂ hOld hEnd
  -- the times of an opening before the climb's end
  have h0i : ∀ i, i ≤ m → rs 0 * S.C.R ≤ rs i * S.C.R := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h | h
    · rw [h]
    · exact Nat.mul_le_mul_right _ (le_of_lt (hmono 0 i h hi))
  have h2k0 := (window_after_anchor S Sched rs m tGAT tAwakeEnd (rs 0 * S.C.R) hSeq le_rfl).1
  have hvtLow : ∀ i, i ≤ m → T₁ + Δ S ≤ voteTime S (rs i * S.C.R - S.C.k - 1) := by
    intro i hi
    have h1 := slotStart_mono S (show rs 0 * S.C.R - S.C.k - 1 ≤ rs i * S.C.R - S.C.k - 1 by
      have := h0i i hi
      omega)
    have h2 := voteTime_eq S (rs i * S.C.R - S.C.k - 1)
    omega
  have hscHigh : ∀ i, supportCutoff S (min (rs (i + 1) * S.C.R) (r * S.C.R)) < aR S r := by
    intro i
    have h1 := supportCutoff_mono S (min_le_right (rs (i + 1) * S.C.R) (r * S.C.R))
    have h2 := supportCutoff_succ_eq S (r * S.C.R)
    unfold aR
    omega
  have hss : ∀ i, i < m → rs i * S.C.R + S.C.R ≤ rs (i + 1) * S.C.R := by
    intro i hi
    have h' : (rs i + 1) * S.C.R ≤ rs (i + 1) * S.C.R :=
      Nat.mul_le_mul_right _ (hmono i (i + 1) (by omega) hi)
    rw [Nat.add_mul, Nat.one_mul] at h'
    exact h'
  -- the proposals
  have hP : ∀ i, i ≤ m → ∃ B : Block V, ProposalAt S Sched x (rs i * S.C.R) B :=
    fun i hi => opening_proposal_exists S Sched x tGAT tAwakeEnd m i rs hDiv hMono hAwake
      hSeq hi
  let Bf : ℕ → Block V := fun i =>
    if hi : i ≤ m then Classical.choose (hP i hi) else Block.genesis
  have hBf : ∀ i (hi : i ≤ m), ProposalAt S Sched x (rs i * S.C.R) (Bf i) := by
    intro i hi
    simp only [Bf, dif_pos hi]
    exact Classical.choose_spec (hP i hi)
  have hUniq : ∀ i, i ≤ m → ∀ B : Block V, ProposalAt S Sched x (rs i * S.C.R) B → B = Bf i :=
    fun i hi B hB => opening_proposal_unique S Sched x tGAT tAwakeEnd m i rs B (Bf i) hDiv hMono hU
      hSeq hi hNoCol hB (hBf i hi)
  -- no fork-choice change over an opening's window and round, and the waiting openings
  let NoCh : ℕ → Prop := fun i => ∀ (w : V) (t' : ℕ),
    voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' →
      t' < supportCutoff S (rs (i + 1) * S.C.R) → w ∉ Sched.adv (t' : Int) →
      ¬ ForkChoiceChangeAt S Sched x w t'
  -- the same, with the round read to the support cutoff of slot `min (rs (i + 1) * R) (r * R)`
  let NoChM : ℕ → Prop := fun i => ∀ (w : V) (t' : ℕ),
    voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' →
      t' < supportCutoff S (min (rs (i + 1) * S.C.R) (r * S.C.R)) → w ∉ Sched.adv (t' : Int) →
      ¬ ForkChoiceChangeAt S Sched x w t'
  have hNoChOfM : ∀ i, rs (i + 1) * S.C.R ≤ r * S.C.R → NoChM i → NoCh i :=
    fun i hir hNo w t' h1 h2 h3 => hNo w t' h1
      (lt_of_lt_of_le h2 (supportCutoff_mono S (le_of_eq (min_eq_left hir).symm))) h3
  let Wt : ℕ → Prop := fun i =>
    i < m ∧ rs (i + 1) * S.C.R ≤ r * S.C.R ∧ NoCh i ∧ ¬ RisingAt S Sched x rs i
  have hWfacts : ∀ i, Wt i →
      (∀ B' : Block V, ProposalAt S Sched x (rs (i + 1) * S.C.R) B' →
        (chainStateOf S.C B').h ≤ (chainStateOf S.C (Bf i)).h) ∧
      (chainStateOf S.C (Bf i)).h ≤ H₂ ∧ H₂ ≤ (chainStateOf S.C (Bf i)).h + 1 ∧
      InSpan (chainStateOf S.C (Bf i)).T_h.slot S.C.δt (rs i * S.C.R) := by
    intro i hWt
    obtain ⟨him, hir, hNo, hNR⟩ := hWt
    have hBi := hBf i (le_of_lt him)
    have hWait : ∀ B' : Block V, ProposalAt S Sched x (rs (i + 1) * S.C.R) B' →
        (chainStateOf S.C B').h ≤ (chainStateOf S.C (Bf i)).h := by
      intro B' hB'
      by_contra hgt
      apply hNR
      intro B₀ B₀' hB₀ hB₀'
      rw [hUniq i (le_of_lt him) B₀ hB₀, hUniq (i + 1) him B₀' hB₀', ← hUniq (i + 1) him B' hB']
      unfold Height at *
      omega
    have hTop : (chainStateOf S.C (Bf i)).h ≤ H₂ := by
      by_contra hgt
      obtain ⟨t₀, v, a, ht₀, hA, ha⟩ := quiet_top_gives_attestation_cutoff S Sched x GST tGAT
        tAwakeEnd r m i H₂ (rs (i + 1) * S.C.R) rs (Bf i) hDiv hMono hSync hCatch
        (hRoots.mono (supportCutoff_mono S (by omega))) hParent hOwner hU hGST hThird hAwake
        hCommittees hEnd hSeq him (hss i him) hir hNoCol hNo
        hBi (by unfold Height at *; omega)
      obtain ⟨j, hl, hAw, hHon, hm⟩ := hA
      have hlt : t₀ < aR S r := by
        have h1 := hss i him
        have h2 := supportCutoff_mono S (show rs i * S.C.R + 1 + 1 ≤ r * S.C.R + 1 by omega)
        have h3 := supportCutoff_succ_eq S (rs i * S.C.R + 1)
        unfold aR at ht₀ ⊢
        omega
      have := hOld j t₀ v a hl hlt hAw hHon hm
      exact absurd this (not_le.2 ha)
    obtain ⟨_B'', -, -, -, -, hlo, -⟩ := quiet_waiting_next_proposal S Sched x GST tGAT tAwakeEnd T₁
      r H₂ m i rs (Bf i) hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hT₁ hThird
      hAwake hCommittees hH₂ hOld hEnd hSeq hT₁0 him hir hNoCol hNo hSyncF hCatchF hWait hTop hBi
    obtain ⟨hs1, C⟩ := quietCtx_of S Sched x GST tGAT tAwakeEnd r m i rs hDiv hMono hSync hCatch
      (hRoots.mono (supportCutoff_mono S (by omega))) hParent hOwner hU hGST hThird hAwake
      hCommittees hEnd hSeq him
      (opening_round_step hSeq him) hir hNoCol hNo
    have hB0 : ProposalAt S Sched x (rs i * S.C.R - 1 + 1) (Bf i) := by rw [← hs1]; exact hBi
    have h89 := C.round89r rfl (Bf i) (Bf (i + 1)) hB0 (hBf (i + 1) him) hSyncF hCatchF
    have hW1 := hWait (Bf (i + 1)) (hBf (i + 1) him)
    have hdisj : (Bf (i + 1)).slot < (chainStateOf S.C (Bf i)).T_h.slot + S.C.δt := by
      rcases h89.2.1 with h' | ⟨-, h', -⟩
      · exfalso
        unfold Height at *
        omega
      · exact h'
    obtain ⟨hsl1, -⟩ := opening_proposal_held S Sched x tGAT tAwakeEnd m (i + 1) rs (Bf (i + 1))
      hDiv hMono hSeq him hNoCol (hBf (i + 1) him)
    obtain ⟨hsl0, hheld⟩ := opening_proposal_held S Sched x tGAT tAwakeEnd m i rs (Bf i)
      hDiv hMono hSeq (le_of_lt him) hNoCol hBi
    have hThs : (chainStateOf S.C (Bf i)).T_h.slot ≤ rs i * S.C.R := by
      have hTC : TreeClosed S.P S.X (stateBefore x (slotStart S (rs i * S.C.R) + 1)
          (S.P.proposer (rs i * S.C.R))).S :=
        (lem11_node_invariant S Sched x (stepBefore x (slotStart S (rs i * S.C.R) + 1)) _).1.2.2.1
      by_cases he : (chainStateOf S.C (Bf i)).T_h = Bf i
      · rw [he, hsl0]
      · have := slot_lt_of_ancestorEq_of_treeClosed hTC hheld
          (chainStateOf_T_h_spec S.C (Bf i)).1 he
        rw [hsl0] at this
        exact le_of_lt this
    have hd2 : rs (i + 1) * S.C.R < (chainStateOf S.C (Bf i)).T_h.slot + S.C.δt := by
      rw [← hsl1]
      exact hdisj
    have key : ∀ a b c d e : ℕ, a + e ≤ b → b < c + d → 2 ≤ e → a < c + d := by
      intro a b c d e h1 h2 h3
      omega
    exact ⟨hWait, hTop, hlo, hThs, key _ _ _ _ _ (hss i him) hd2 hR⟩
  -- the spans
  let waits : Fin 2 → ℕ := fun c =>
    if h : ∃ i, Wt i ∧ (chainStateOf S.C (Bf i)).h = H₂ - 1 + c.val then
      (chainStateOf S.C (Bf (Classical.choose h))).T_h.slot
    else 0
  let w4 : Fin 4 → ℕ := fun c => τ c / (4 * Δ S)
  refine ⟨waits, w4, ?_⟩
  set F := (Finset.range m).filter (fun i => rs i * S.C.R < r * S.C.R ∧
    OutsideSpans S rs waits S.C.δt w4 (S.C.k + 2) i) with hFdef
  have hmemF : ∀ i ∈ F, i < m ∧ rs i * S.C.R < r * S.C.R ∧
      OutsideSpans S rs waits S.C.δt w4 (S.C.k + 2) i := by
    intro i hi
    rw [hFdef, Finset.mem_filter, Finset.mem_range] at hi
    exact ⟨hi.1, hi.2⟩
  -- a waiting opening is in a wait span
  have hNoWait : ∀ i ∈ F, ¬ Wt i := by
    intro i hi hWt
    obtain ⟨-, -, hout⟩ := hmemF i hi
    obtain ⟨hWait, hTop, hlo, hspan⟩ := hWfacts i hWt
    have hh1 := (lem47_chain_state_heights S.C (Bf i) (Bf i)).1.1
    have key : ∀ c : Fin 2, (chainStateOf S.C (Bf i)).h = H₂ - 1 + c.val → False := by
      intro c hc
      have hex : ∃ i, Wt i ∧ (chainStateOf S.C (Bf i)).h = H₂ - 1 + c.val := ⟨i, hWt, hc⟩
      have hwc : waits c = (chainStateOf S.C (Bf (Classical.choose hex))).T_h.slot := by
        simp only [waits, dif_pos hex]
      obtain ⟨hWt₀, hc₀⟩ := Classical.choose_spec hex
      set i₀ := Classical.choose hex with hi₀
      have hEq : (chainStateOf S.C (Bf i)).T_h = (chainStateOf S.C (Bf i₀)).T_h := by
        have hhe : (chainStateOf S.C (Bf i)).h = (chainStateOf S.C (Bf i₀)).h := by
          rw [hc, hc₀]
        obtain ⟨him, hir, hNo, -⟩ := hWt
        have him₀ := hWt₀.1
        have hir₀ := hWt₀.2.1
        have hNo₀ := hWt₀.2.2.1
        rcases lt_trichotomy i i₀ with hlt | heq | hgt
        · exact quiet_waiting_same_entry_cutoff S Sched x GST tGAT tAwakeEnd T₁ r H₂ m i i₀ rs
            (Bf i) (Bf i₀) hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hT₁ hThird
            hAwake hCommittees hH₂ hOld hEnd hSeq hT₁0 hlt him₀ hir₀ hNoCol hNo hNo₀ hSyncF hCatchF
            hWait hTop (hBf i (le_of_lt him)) (hBf i₀ (le_of_lt him₀)) hhe
        · rw [heq]
        · obtain ⟨hWait₀, hTop₀, -, -⟩ := hWfacts i₀ hWt₀
          exact (quiet_waiting_same_entry_cutoff S Sched x GST tGAT tAwakeEnd T₁ r H₂ m i₀ i
            rs (Bf i₀) (Bf i) hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hT₁
            hThird hAwake hCommittees hH₂ hOld hEnd hSeq hT₁0 hgt him hir hNoCol hNo₀ hNo hSyncF
            hCatchF hWait₀ hTop₀ (hBf i₀ (le_of_lt him₀)) (hBf i (le_of_lt him)) hhe.symm).symm
      apply hout.1 c
      rw [hwc, ← hEq]
      exact hspan
    by_cases h0 : (chainStateOf S.C (Bf i)).h = H₂ - 1
    · exact key 0 (by rw [h0]; rfl)
    · exact key 1 (by
        show (chainStateOf S.C (Bf i)).h = H₂ - 1 + 1
        unfold Height at *
        omega)
  -- the openings with a fork-choice change, and the time of the change
  let Ch : ℕ → Prop := fun i => ∃ t' : ℕ, voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' ∧
    t' < supportCutoff S (min (rs (i + 1) * S.C.R) (r * S.C.R)) ∧ ∃ w : V,
      w ∉ Sched.adv (t' : Int) ∧ ForkChoiceChangeAt S Sched x w t'
  have hNoChOf : ∀ i, ¬ Ch i → NoChM i := by
    intro i h w t' h1 h2 h3 h4
    exact h ⟨t', h1, h2, w, h3, h4⟩
  let tc : ℕ → ℕ := fun i => if h : Ch i then Classical.choose h else 0
  have htc : ∀ i, Ch i → voteTime S (rs i * S.C.R - S.C.k - 1) ≤ tc i ∧
      tc i < supportCutoff S (min (rs (i + 1) * S.C.R) (r * S.C.R)) ∧
        ∃ w : V, w ∉ Sched.adv ((tc i : ℕ) : Int) ∧
        ForkChoiceChangeAt S Sched x w (tc i) := by
    intro i h
    simp only [tc, dif_pos h]
    exact Classical.choose_spec h
  let gc : ℕ → Fin 4 := fun i =>
    if h : ∃ c : Fin 4, τ c ≤ tc i ∧ tc i ≤ τ c + Δ S then Classical.choose h else 0
  have hgc : ∀ i ∈ F, Ch i → τ (gc i) ≤ tc i ∧ tc i ≤ τ (gc i) + Δ S := by
    intro i hi hch
    obtain ⟨him, -, -⟩ := hmemF i hi
    obtain ⟨h1, h2, w, hw, hchg⟩ := htc i hch
    have hex : ∃ c : Fin 4, τ c ≤ tc i ∧ tc i ≤ τ c + Δ S :=
      hτ w (tc i) (le_trans (hvtLow i (le_of_lt him)) h1)
        (lt_trans h2 (hscHigh i)) hw hchg
    simp only [gc, dif_pos hex]
    exact Classical.choose_spec hex
  -- the change is in the opening's round
  have hspanOf : ∀ i, i ≤ m → ∀ c : Fin 4, ∀ t' : ℕ, τ c ≤ t' → t' ≤ τ c + Δ S →
      voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' → t' < supportCutoff S (rs i * S.C.R) →
      InSpan (w4 c) (S.C.k + 2) (rs i * S.C.R) := by
    intro i hi c t' h1 h2 h3 h4
    obtain ⟨hσ, hσ'⟩ := slotStart_div_le S (τ c)
    have h2k := (window_after_anchor S Sched rs m tGAT tAwakeEnd (rs i * S.C.R) hSeq (h0i i hi)).1
    have hk2 := S.C.k_ge_two
    exact fork_choice_change_in_window_span S (rs i * S.C.R) (τ c / (4 * Δ S)) (τ c) t'
      (by omega) hσ hσ' h1 h2 h3 h4
  have hround : ∀ i ∈ F, Ch i → supportCutoff S (rs i * S.C.R) ≤ tc i := by
    intro i hi hch
    obtain ⟨him, -, hout⟩ := hmemF i hi
    by_contra hlt
    obtain ⟨h1, -, -⟩ := htc i hch
    obtain ⟨h3, h4⟩ := hgc i hi hch
    exact hout.2 (gc i) (hspanOf i (le_of_lt him) (gc i) (tc i) h3 h4 h1 (by omega))
  have hinj : Set.InjOn gc (F.filter Ch) := by
    -- two openings with a change of one kind in their rounds: the later one is in the kind's span
    have hone : ∀ i ∈ F.filter Ch, ∀ i' ∈ F.filter Ch, i < i' → gc i ≠ gc i' := by
      intro i hi i' hi' hlt hgeq
      rw [Finset.mem_filter] at hi hi'
      obtain ⟨him, -, -⟩ := hmemF i hi.1
      obtain ⟨him', -, hout'⟩ := hmemF i' hi'.1
      obtain ⟨-, h2, -⟩ := htc i hi.2
      obtain ⟨hτ1, -⟩ := hgc i hi.1 hi.2
      obtain ⟨-, hτ2'⟩ := hgc i' hi'.1 hi'.2
      have hr' := hround i' hi'.1 hi'.2
      rw [← hgeq] at hτ2'
      have hsc : supportCutoff S (min (rs (i + 1) * S.C.R) (r * S.C.R)) ≤
          supportCutoff S (rs i' * S.C.R) := by
        apply supportCutoff_mono
        refine le_trans (min_le_left _ _) ?_
        rcases Nat.lt_or_ge (i + 1) i' with h | h
        · exact Nat.mul_le_mul_right _ (le_of_lt (hmono (i + 1) i' h (le_of_lt him')))
        · rw [show i' = i + 1 by omega]
      have hv1 := voteTime_mono S (show rs i' * S.C.R - S.C.k - 1 ≤ rs i' * S.C.R by
        have := (window_after_anchor S Sched rs m tGAT tAwakeEnd (rs i' * S.C.R) hSeq
          (h0i i' (le_of_lt him'))).1
        omega)
      have hv2 := supportCutoff_eq S (rs i' * S.C.R)
      exact hout'.2 (gc i) (hspanOf i' (le_of_lt him') (gc i) (supportCutoff S (rs i' * S.C.R) - 1)
        (by omega) (by omega) (by omega) (by omega))
    intro i hi i' hi' hgg
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact hone i hi i' hi' hlt hgg
    · exact hone i' hi' i hi hlt hgg.symm
  have hcardCh : (F.filter Ch).card ≤ 4 := by
    have := Finset.card_le_card_of_injOn gc (fun i _ => Finset.mem_univ (gc i)) hinj
    simpa using this
  -- the openings with no change rise
  have hsubRise : F.filter (fun i => ¬ Ch i) ⊆ (Finset.range m).filter (fun i =>
      rs i * S.C.R < r * S.C.R ∧
      (∀ (w : V) (t' : ℕ), voteTime S (rs i * S.C.R - S.C.k - 1) ≤ t' →
        t' < supportCutoff S (min (rs (i + 1) * S.C.R) (r * S.C.R)) →
        w ∉ Sched.adv (t' : Int) → ¬ ForkChoiceChangeAt S Sched x w t') ∧
      (rs (i + 1) * S.C.R ≤ r * S.C.R → RisingAt S Sched x rs i)) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨him, hlt, -⟩ := hmemF i hi.1
    have hNo := hNoChOf i hi.2
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨him, hlt, hNo, fun hir => ?_⟩
    by_contra hNR
    exact hNoWait i hi.1 ⟨him, hir, hNoChOfM i hir hNo, hNR⟩
  have hcardRise := le_trans (Finset.card_le_card hsubRise)
    (quiet_rising_before_fast_round_le_two_cutoff S Sched x GST tGAT tAwakeEnd T₁ r H₂ m rs
      hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hT₁ hThird hAwake hCommittees
      hH₂ hOld hEnd hSeq hT₁0 hNoCol)
  have hsplit := Finset.card_filter_add_card_filter_not (s := F) Ch
  omega

/-! ## The climb -/

omit [RootOrder] in
/-- **Five window spans as four and one.** An honest round opening slot outside two families of
spans whose second is the four spans `w` followed by the spans `a` (`Fin.append w a`) is outside
the spans `w` and outside every span `a j`.

The variables:
- `S`: the setup; `rs`: the rounds; `waits`, `Lw`: the first family; `w`, `a`: the two parts of
  the second family, of length `L`; `i`: the honest round opening slot. -/
theorem outsideSpans_append_parts (S : Setup V) (rs : ℕ → ℕ) {nW n₁ n₂ : ℕ}
    (waits : Fin nW → ℕ) (Lw : ℕ) (w : Fin n₁ → ℕ) (a : Fin n₂ → ℕ) (L i : ℕ)
    (h : OutsideSpans S rs waits Lw (Fin.append w a) L i) :
    OutsideSpans S rs waits Lw w L i ∧ ∀ j : Fin n₂, ¬ InSpan (a j) L (rs i * S.C.R) := by
  refine ⟨⟨h.1, fun j => ?_⟩, fun j => ?_⟩
  · have := h.2 (Fin.castAdd n₂ j)
    rwa [Fin.append_left] at this
  · have := h.2 (Fin.natAdd n₁ j)
    rwa [Fin.append_right] at this


/-- **Part B's assembly, the climb to the first honest fast block, with the premise of three span
lengths and the count 9.** The proof; the audited statement is in
`Statements/Executions/Lemma89Statements.lean`.

The route: split on the collision disjunct, so that `hNoCol` holds. Take
`T₁ := slotStart S (rs 0 * R − 2k) + 3Δ` and `H₂` the greatest height of an honest attestation
before `T₁` (B1). An honest attestation above `H₂` is sent at a time from `T₁` to before
`aR S (rs (m − 1))`: otherwise every honest attestation before that time is at most `H₂`, and
`climb_count_before` at the round `rs (m − 1)` leaves at most six outside openings before it, with
only the last opening after its span: seven, against the premise's nine. B3 gives the first round
`r` with such an attestation at `aR S r`, every earlier one at most `H₂`; B4 its fast block `L` of
height `H₂ + 1`; and `T₁ ≤ aR S r` puts slot `r * R + 1` at or after the committee premise's
anchor. At `r`, the count leaves at most six outside openings `i < m` with `rs i * R < r * R`
, and the last one: at least three
outside honest round opening slots have their first slot at or after `r * R` (`after_of_before`),
hence at least `k + 2` slots after it (the span of `k + 2` slots at `r * R`); the first honest
round opening slot `j` at least `k + 2` slots after `r * R` is at or before the first of them, so
`j + 2 ≤ m`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the times;
  `m`: the index of the last honest round opening slot; `rs`: the rounds of the honest round opening slots.

Roots name blocks until `aR S (rs (m - 1))`: the count at the round `rs (m − 1)`
(`climb_count_before`), and at the first round `r` above the threshold, whose action time is before
`aR S (rs (m - 1))`. -/
theorem climb_to_fast_block (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd m : ℕ) (rs : ℕ → ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hRoots : RootsNameBlocksUntil S Sched x (aR S (rs (m - 1))))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hm : OpeningsOutsideWaitsAndWindows S rs m) :
    RootCollisionAtOpening S Sched x rs m ∨
    ∃ (r H₂ : ℕ) (v : V) (L : Block V) (A' : ACState V),
      anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1) ∧ aR S r ≤ tAwakeEnd ∧
      OldAttestationsAtMost S Sched x (aR S r) H₂ ∧
      v ∉ Sched.adv ((aR S r : ℕ) : Int) ∧
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A' ∧
      L ∈ A'.fast_blocks ∧ (chainStateOf S.C L).h = H₂ + 1 ∧
      ∃ j : ℕ, j + 2 ≤ m ∧ r * S.C.R + S.C.k + 2 ≤ rs j * S.C.R ∧
        ∀ i : ℕ, i < j → rs i * S.C.R < r * S.C.R + S.C.k + 2 := by
  classical
  by_cases hcol : RootCollisionAtOpening S Sched x rs m
  · exact Or.inl hcol
  right
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  have hmono := r_lt_of_lt_of_mono rs m hSeq.mono
  have hmle : ∀ a b : ℕ, a ≤ b → b ≤ m → rs a * S.C.R ≤ rs b * S.C.R := by
    intro a b hab hbm
    rcases Nat.lt_or_ge a b with h | h
    · exact Nat.mul_le_mul_right _ (le_of_lt (hmono a b h hbm))
    · rw [show a = b by omega]
  obtain ⟨h2k0, hA0⟩ := window_after_anchor S Sched rs m tGAT tAwakeEnd (rs 0 * S.C.R) hSeq le_rfl
  have hss0 : slotStart S (rs 0 * S.C.R - 2 * S.C.k + 1) =
      slotStart S (rs 0 * S.C.R - 2 * S.C.k) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  -- the threshold, three delays into slot `rs 0 * R − 2k`
  set T₁ := slotStart S (rs 0 * S.C.R - 2 * S.C.k) + 3 * Δ S with hT₁def
  have hT₁0 : T₁ + Δ S ≤ slotStart S (rs 0 * S.C.R - S.C.k - 1) :=
    le_trans (show T₁ + Δ S ≤ slotStart S (rs 0 * S.C.R - 2 * S.C.k + 1) by omega)
      (slotStart_mono S (by omega))
  have hT₁ : tGAT ≤ T₁ := by
    have h1 : 4 * Δ S ≤ 4 * Δ S * (S.C.k + 2) := Nat.le_mul_of_pos_right _ (by omega)
    rw [anchorCW_eq] at hA0
    omega
  obtain ⟨H₂, hH₂⟩ := exists_old_height_attained S Sched x T₁ hDiv
  have hcount : ∀ (waits : Fin 2 → ℕ) (w5 : Fin 5 → ℕ),
      9 ≤ ((Finset.range (m + 1)).filter
        (OutsideSpans S rs waits S.C.δt w5 (S.C.k + 2))).card := hm
  have hm1 : 1 ≤ m := by
    have h := hcount (fun _ => 0) (fun _ => 0)
    have := Finset.card_filter_le (Finset.range (m + 1))
      (OutsideSpans S rs (fun _ : Fin 2 => 0) S.C.δt (fun _ : Fin 5 => 0) (S.C.k + 2))
    rw [Finset.card_range] at this
    omega
  -- an honest attestation above `H₂` before the action time of opening `m − 1`'s round
  have hrm1 : rs (m - 1) * S.C.R + S.C.R ≤ rs m * S.C.R := by
    have h' : (rs (m - 1) + 1) * S.C.R ≤ rs m * S.C.R :=
      Nat.mul_le_mul_right _ (hmono (m - 1) m (by omega) le_rfl)
    rw [Nat.add_mul, Nat.one_mul] at h'
    exact h'
  have hEnd1 : aR S (rs (m - 1)) ≤ tAwakeEnd := by
    unfold aR
    exact le_trans (supportCutoff_mono S (by omega)) hSeq.last
  have hex : ∃ (t₀ : ℕ) (v₀ : V) (a₀ : Attestation V), T₁ ≤ t₀ ∧ t₀ < aR S (rs (m - 1)) ∧
      HonestAttestationAt S Sched x t₀ v₀ a₀ ∧ H₂ < a₀.h := by
    by_contra hno
    have hOld1 : OldAttestationsAtMost S Sched x (aR S (rs (m - 1))) H₂ := by
      intro i t v a hl ht hAw hHon hmem
      by_cases hlt : t < T₁
      · exact hH₂.1 i t v a hl hlt hAw hHon hmem
      · by_contra hgt
        exact hno ⟨t, v, a, Nat.le_of_not_lt hlt, ht, ⟨i, hl, hAw, hHon, hmem⟩,
          Nat.lt_of_not_le hgt⟩
    obtain ⟨waits, w4, hcnt⟩ := climb_count_before S Sched x GST tGAT tAwakeEnd T₁ (rs (m - 1))
      H₂ m rs hDiv hMono hSync hCatch hSyncF hCatchF hRoots hParent hOwner hU hGST hT₁
      hThird hAwake hCommittees hH₂ hOld1 hEnd1 hSeq hT₁0 hcol
    have h9 := hcount waits (Fin.append w4 (fun _ : Fin 1 => rs (m - 1) * S.C.R))
    have hsub : (Finset.range (m + 1)).filter
        (OutsideSpans S rs waits S.C.δt (Fin.append w4 (fun _ : Fin 1 => rs (m - 1) * S.C.R))
          (S.C.k + 2)) ⊆
        (Finset.range m).filter (fun i => rs i * S.C.R < rs (m - 1) * S.C.R ∧
          OutsideSpans S rs waits S.C.δt w4 (S.C.k + 2) i) ∪ {m} := by
      intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨hout, hnot⟩ := outsideSpans_append_parts S rs waits S.C.δt w4 _ (S.C.k + 2) i hi.2
      by_cases him : i = m
      · exact Finset.mem_union_right _ (Finset.mem_singleton.2 him)
      · apply Finset.mem_union_left
        rw [Finset.mem_filter, Finset.mem_range]
        have him' : i < m := by omega
        by_cases hi1 : i = m - 1
        · exfalso
          apply hnot 0
          rw [hi1]
          show rs (m - 1) * S.C.R ≤ rs (m - 1) * S.C.R ∧
            rs (m - 1) * S.C.R < rs (m - 1) * S.C.R + (S.C.k + 2)
          omega
        · have h1 := hmle (i + 1) (m - 1) (by omega) (by omega)
          have h2 := opening_round_step hSeq him'
          exact ⟨him', by omega, hout⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le ((Finset.range m).filter (fun i =>
      rs i * S.C.R < rs (m - 1) * S.C.R ∧ OutsideSpans S rs waits S.C.δt w4 (S.C.k + 2) i))
      ({m} : Finset ℕ)
    rw [Finset.card_singleton] at h2
    omega
  -- the first round above the threshold, and its fast block
  obtain ⟨t₀, v₀, a₀, ht₀, ht₀', hA₀, ha₀⟩ := hex
  obtain ⟨r, hTr, hrt, hOld, v, a, hA, ha⟩ := first_attestation_above_bound S Sched x T₁ H₂ t₀ v₀
    a₀ hH₂ ht₀ hA₀ ha₀
  have hEnd : aR S r ≤ tAwakeEnd := by omega
  obtain ⟨A', L, hUpd, hFast, -, hL⟩ := fast_block_at_first_round S Sched x tAwakeEnd r H₂ v a hU
    hThird hOld hEnd hA ha
  have hv : v ∉ Sched.adv ((aR S r : ℕ) : Int) := by
    obtain ⟨_, _, _, h, _⟩ := hA
    exact h
  have hAnchor : anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1) := by
    have h1 : aR S r = slotStart S (r * S.C.R + 1) + 2 * Δ S := by
      unfold aR
      have := supportCutoff_eq S (r * S.C.R + 1)
      have := voteTime_eq S (r * S.C.R + 1)
      omega
    have h2 : rs 0 * S.C.R - 2 * S.C.k + 1 ≤ r * S.C.R + 1 := by
      by_contra hlt
      have := slotStart_mono S (show r * S.C.R + 1 ≤ rs 0 * S.C.R - 2 * S.C.k by omega)
      omega
    exact le_trans hA0 (slotStart_mono S h2)
  -- the count at `r`: three outside honest round opening slots at or after `r * R`
  obtain ⟨waits, w4, hcnt⟩ := climb_count_before S Sched x GST tGAT tAwakeEnd T₁ r H₂ m rs hDiv
    hMono hSync hCatch hSyncF hCatchF (hRoots.mono (by omega)) hParent hOwner hU hGST hT₁
    hThird hAwake
    hCommittees hH₂ hOld hEnd hSeq hT₁0 hcol
  let a₃ : Fin 1 → ℕ := fun _ => r * S.C.R
  have h6 : ((Finset.range m).filter (fun i => rs i * S.C.R < r * S.C.R ∧
      OutsideSpans S rs waits S.C.δt (Fin.append w4 a₃) (S.C.k + 2) i)).card ≤ 6 := by
    refine le_trans (Finset.card_le_card ?_) hcnt
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hi.2.1,
      (outsideSpans_append_parts S rs waits S.C.δt w4 a₃ (S.C.k + 2) i hi.2.2).1⟩
  have h3 := after_of_before S rs m (r * S.C.R) 9
    (OutsideSpans S rs waits S.C.δt (Fin.append w4 a₃) (S.C.k + 2))
    (by omega) (fun i hi => hmle i m hi le_rfl) h6 (hcount waits (Fin.append w4 a₃))
  set Bs := (Finset.range (m + 1)).filter (fun i => r * S.C.R ≤ rs i * S.C.R ∧
    OutsideSpans S rs waits S.C.δt (Fin.append w4 a₃) (S.C.k + 2) i) with hBsdef
  have hBs : ∀ i ∈ Bs, i ≤ m ∧ r * S.C.R + S.C.k + 2 ≤ rs i * S.C.R := by
    intro i hi
    rw [hBsdef, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨him, hge, hO⟩ := hi
    have hnot := (outsideSpans_append_parts S rs waits S.C.δt w4 a₃ (S.C.k + 2) i hO).2
    have hn := hnot 0
    refine ⟨by omega, ?_⟩
    unfold InSpan at hn
    simp only [a₃] at hn
    omega
  have hexj : ∃ j : ℕ, r * S.C.R + S.C.k + 2 ≤ rs j * S.C.R := by
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (by omega : 0 < Bs.card)
    exact ⟨i, (hBs i hi).2⟩
  refine ⟨r, H₂, v, L, A', hAnchor, hEnd, hOld, hv, hUpd, hFast, hL, Nat.find hexj, ?_,
    Nat.find_spec hexj, fun i hi => ?_⟩
  · have hj : ∀ i ∈ Bs, Nat.find hexj ≤ i ∧ i ≤ m := fun i hi =>
      ⟨Nat.find_min' hexj (hBs i hi).2, (hBs i hi).1⟩
    have hmaps : ∀ i ∈ Bs, (fun i => i - Nat.find hexj) i ∈ Finset.range (m + 1 - Nat.find hexj) := by
      intro i hi
      have := hj i hi
      rw [Finset.mem_range]
      show i - Nat.find hexj < m + 1 - Nat.find hexj
      omega
    have hinj : Set.InjOn (fun i => i - Nat.find hexj) Bs := by
      intro i hi i' hi' he
      have h1 := hj i hi
      have h2 := hj i' hi'
      simp only at he
      omega
    have := Finset.card_le_card_of_injOn (fun i => i - Nat.find hexj) hmaps hinj
    rw [Finset.card_range] at this
    omega
  · have := Nat.find_min hexj hi
    omega

end GoldilocksCorrectness.Proofs.Executions
