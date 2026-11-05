module
public import GoldilocksCorrectness.Proofs.View.Bridges
public import GoldilocksCorrectness.Proofs.Executions.Lemma89QuietJ
public import GoldilocksCorrectness.Proofs.Executions.Sleepy
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.Node

@[expose] public section

/-! The restated B12 itself, two openings `i < i'` with no
fork-choice change over their windows and rounds, the first rising, have proposals of
different chain-state heights (`quiet_rising_heights_differ_cutoff`), and its count
(`quiet_rising_before_fast_round_le_two_cutoff`) are proved in
`Proofs/Executions/Lemma89ClimbLate.lean`.

Their route, by contradiction with both proposals at the height `h`: the next proposal `B'` after the
first opening has height at least `h + 1`. No honest validator's `head_height_floor` reaches
`h + 1` before the later opening's support cutoff (it would reach a member of the later opening
within one delay and stay, against that opening's first clause), so every honest validator holding
`B'` has `h_max = h + 1`, is not contested, and has its root on `B'`'s chain: `B'` is a viable head
at all of them. The honest votes of `B'`'s slot name `B'` (the round's base, `WinCtx.base`, the
first opening's range covering `B'`'s window), are carried on `B'`'s chain to the slot before the
later opening (`lem79_step_sets`), and the later opening's proposer then walks past `B'`: its
proposal is higher than `h`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff
  proposalWindowStart anchorCW)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_of_anchor
  dutyWindowStart_succ_le_slotStart one_le_Δ proposalWindowStart_eqJ proposal_window_start_eqJ
  slotStart_cast slotStart_eq slotStart_mono slot_eq_of_mem supportCutoff_eq supportCutoff_mono
  voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (DREBEmits DREBEmits.bind DREBEmits.ite DREBEmits.pure
  chainStateOf_height_mono)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (h_max_sub_one_le_floor mem_viable_heads_iff)

open GoldilocksCorrectness.Proofs.Routines (ac_on_tick_emits_vote)

open GoldilocksCorrectness.Proofs.Routines (tick_emits_proposalJ)

open GoldilocksCorrectness.Proofs.Routines (wake_eq)

open GoldilocksCorrectness.Proofs.Routines (anchorCW_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq ancestorEq_compatible ancestorEq_antisymm)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## No honest validator's `head_height_floor` (the least chain-state height a viable block may have) reaches above a quiet opening's proposal -/

/-- **No honest `head_height_floor` reaches one more than a quiet opening's proposal before its
support cutoff.** In the climb's context, for the opening `i'` (`QuietCtx` with `s₀'`, `s₃`) whose
proposal `B₂` has chain-state height `h` with `h + 1` equal to `H₂` or `H₂ + 1`: every validator
honest at a time `t` from `T₁ + 1` to the support cutoff of slot `s₀' + 1` has its
`head_height_floor` before `t` at most `h`.

Why: at a member of the opening, at the vote time of its first slot, `head_height_floor` is at most `B₂`'s
parent's height (the first clause), so at most `h`. A `head_height_floor` value of `h + 1` at an honest validator one
delay earlier reaches that member and stays (`ClimbCtx.spread_level_floor`,
`ClimbCtx.mono_level_floor`, or their `_succ` forms); later, up to the support cutoff, `head_height_floor`
does not rise (no fork-choice change in the opening's window).

The variables:
- `CC`: the climb's context; `C'`: the opening's context; `h`: the height; `B₂`: the proposal; `u`:
  the validator; `t`: the time. -/
theorem floor_le_before_quiet {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
    {GST tGAT tAwakeEnd T₁ r H₂ m i' : ℕ} {rs : ℕ → ℕ} {s₀' s₃ : ℕ}
    (CC : ClimbCtx S Sched x GST tGAT tAwakeEnd T₁ r H₂)
    (C' : QuietCtx S Sched x GST tGAT tAwakeEnd r m i' rs s₀' s₃)
    (hT₁ : T₁ + Δ S ≤ slotStart S (s₀' + 1 - S.C.k - 1))
    (h : ℕ) (hh : h + 1 = H₂ ∨ h = H₂) (B₂ : Block V) (hB₂ : ProposalAt S Sched x (s₀' + 1) B₂)
    (hB₂h : (chainStateOf S.C B₂).h = h) (u : V) (t : ℕ) (ht1 : T₁ + 1 ≤ t)
    (ht2 : t ≤ supportCutoff S (s₀' + 1)) (hu : u ∉ Sched.adv (t : Int)) :
    head_height_floor (stateBefore x t u).S ≤ h := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hw0 := C'.win (le_refl (s₀' + 1))
  have hsR := C'.sR
  have hEnd := C'.cut_end
  have hcut := C'.cut_le
  have hv1 := voteTime_eq S (s₀' + 1)
  have hc1 := supportCutoff_eq S (s₀' + 1)
  have hμ := voteTime_eq S (s₀' + 1 - S.C.k - 1)
  have hμs := slotStart_mono S (show s₀' + 1 - S.C.k - 1 ≤ s₀' + 1 by omega)
  have hμs' := slotStart_mono S (show s₀' + 1 - S.C.k - 1 ≤ s₀' by omega)
  have hss : slotStart S (s₀' + 1) = slotStart S s₀' + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hvtR : voteTime S (s₀' + 1) < aR S r := by
    have := supportCutoff_mono S (show s₀' + 1 ≤ s₃ by omega)
    omega
  -- a member of the opening, with its floor at most `h` at the vote time
  have hA2 : anchorCW S tGAT ≤ slotStart S (s₀' + 1 + 1) :=
    le_trans hw0.2 (slotStart_mono S (by omega))
  have hMaj := committee_majority_of_committeeSleepiness S Sched _ (s₀' + 1) C'.hCommittees hA2
  obtain ⟨w₀, hw₀⟩ : (S.P.committee (s₀' + 1) ∩ roundMembers S Sched (s₀' + 1 + 1)).Nonempty :=
    Finset.card_pos.1 (by omega)
  have hw₀H : w₀ ∈ Hon S Sched (s₀' + 1) := (Finset.mem_inter.1 hw₀).2
  have hw₀b : w₀ ∉ Sched.adv ((supportCutoff S (s₀' + 1 + 1) : ℕ) : Int) :=
    (Finset.mem_sdiff.1 hw₀H).2
  have hw₀v : w₀ ∉ Sched.adv ((voteTime S (s₀' + 1) : ℕ) : Int) :=
    fun hh' => hw₀b (C'.hMono _ _ (by exact_mod_cast (le_trans (show voteTime S (s₀' + 1) ≤
      supportCutoff S (s₀' + 1) by omega) (supportCutoff_mono S (Nat.le_succ _)))) hh')
  obtain ⟨-, hfl₀⟩ := C'.clause1 B₂ hB₂ w₀ hw₀H
  obtain ⟨iB, hlB, hsentB⟩ := hB₂
  obtain ⟨-, hBne, hBpar?, -⟩ := proposal_parent_walk_end S Sched x s₀' iB B₂ _ hlB hsentB
  have hPB := GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_parent? hBpar?
  have hpar := chainStateOf_height_mono S.C hPB
  have hfl₀' : head_height_floor (stateBefore x (voteTime S (s₀' + 1)) w₀).S ≤ h := by
    rw [← hB₂h]
    exact le_trans hfl₀ hpar
  -- the floor at a time one delay before the vote time
  have hearly : ∀ t' : ℕ, T₁ + 1 ≤ t' → t' + Δ S ≤ voteTime S (s₀' + 1) →
      u ∉ Sched.adv (t' : Int) → head_height_floor (stateBefore x t' u).S ≤ h := by
    intro t' h1 h2 hu'
    by_contra hgt
    push Not at hgt
    have hu'' : u ∉ Sched.adv ((t' - 1 : ℕ) : Int) :=
      fun hh' => hu' (C'.hMono _ _ (by exact_mod_cast (Nat.sub_le t' 1)) hh')
    have e1 : t' - 1 + 1 = t' := by omega
    rcases hh with hh | hh
    · have hL : H₂ ≤ head_height_floor (stateBefore x (t' - 1 + 1) u).S := by
        rw [e1]
        unfold Height at *
        omega
      have hsp := CC.spread_level_floor (τ := t' - 1) (t := voteTime S (s₀' + 1)) (by omega)
        hu'' hL (by omega) hvtR hw₀v
      have hm := CC.mono_level_floor (w := w₀) (t₂ := t' - 1 + 1 + Δ S)
        (t := voteTime S (s₀' + 1)) (by omega) (by omega) hvtR hw₀v hsp
      unfold Height at *
      omega
    · have hL : H₂ + 1 ≤ head_height_floor (stateBefore x (t' - 1 + 1) u).S := by
        rw [e1]
        unfold Height at *
        omega
      have hsp := CC.spread_level_floor_succ (τ := t' - 1) (t := voteTime S (s₀' + 1)) (by omega)
        hu'' hL (by omega) hvtR hw₀v
      have hm := CC.mono_level_floor_succ (w := w₀) (t₂ := t' - 1 + 1 + Δ S)
        (t := voteTime S (s₀' + 1)) (by omega) hvtR hw₀v hsp
      unfold Height at *
      omega
  by_cases htt : t + Δ S ≤ voteTime S (s₀' + 1)
  · exact hearly t ht1 htt hu
  · have hus : u ∉ Sched.adv ((voteTime S (s₀' + 1) - Δ S : ℕ) : Int) :=
      fun hh' => hu (C'.hMono _ _ (by exact_mod_cast (show voteTime S (s₀' + 1) - Δ S ≤ t by
        omega)) hh')
    have hfe := hearly (voteTime S (s₀' + 1) - Δ S) (by omega) (by omega) hus
    have hnc := floor_le_of_no_change S Sched x u (voteTime S (s₀' + 1) - Δ S) t (by omega)
      (C'.noChange u (by omega) (le_trans ht2 (supportCutoff_mono S (by omega))) hu)
    exact le_trans hnc hfe

/-! ## An honest proposer proposes (copied from `Lemma90Inclusion.lean`, which cannot be imported
beside `Lemma89Stability.lean`: both declare `get_anchor_cases`) -/

/-- `honest_proposer_proposes` of `Lemma90Inclusion.lean`, copied: when the proposer of slot `q + 2`
is awake and honest from the start of the proposal window of slot `q + 2` to its start, its tick
at the start of slot `q + 2` puts a block on the wire.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `q`: the slot is `q + 2`. -/
theorem honest_proposer_proposesJ (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (q : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hp : ∀ t : ℕ, proposalWindowStart S (q + 2) ≤ t → t ≤ slotStart S (q + 2) →
      S.P.proposer (q + 2) ∈ Sched.awake (t : Int) ∧ S.P.proposer (q + 2) ∉ Sched.adv (t : Int)) :
    ∃ (i : ℕ) (B : Block V), x.lbl i = AtomicAction.tickAllAwake (slotStart S (q + 2)) ∧
      (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent := by
  have hΔ := one_le_Δ S
  have hss : slotStart S (q + 2) = slotStart S (q + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (q + 1), show q + 2 = (q + 1) + 1 from rfl, Nat.mul_add,
      Nat.mul_one]
  have hss' : slotStart S (q + 2 + 1) = slotStart S (q + 2) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (q + 2), Nat.mul_add, Nat.mul_one]
  have hdw := dutyWindowStart_succ_le_slotStart S q
  have hsq : slotStart S q ≤ slotStart S (q + 1) := slotStart_mono S (Nat.le_succ q)
  have hslot : S.C.slot ((slotStart S (q + 2) : ℕ) : Int) = q + 2 :=
    slot_eq_of_mem S le_rfl (by omega)
  have h1 : 1 ≤ slotStart S (q + 2) := by omega
  set p := S.P.proposer (q + 2) with hpdef
  have hl := (stepBefore_spec x hDiv h1).1
  have hpw := proposalWindowStart_eqJ S q
  have hvA := (hp (slotStart S (q + 2)) (by omega) le_rfl).1
  have hHon := (hp (slotStart S (q + 2)) (by omega) le_rfl).2
  obtain ⟨n', sent, hrun, -⟩ := tick_step_outcome x hl hvA hHon
  obtain ⟨τ, hτ, hτle⟩ := awakeSince_le_dutyWindowStart_b S Sched x (q + 1) (slotStart S (q + 2))
    p hDiv hMono (by omega) (fun t' h1 h2 => (hp t' (by omega) h2).1) hHon
  have hnv : (tickInputState x (stepBefore x (slotStart S (q + 2))) (slotStart S (q + 2)) p).v =
      p := by
    have h := (lem11_node_invariant S Sched x (stepBefore x (slotStart S (q + 2))) p).2.1
    unfold tickInputState
    split <;> (try rw [wake_eq]) <;> exact h
  have hL := (tick_emits_proposalJ S.C S.P S.X _ _).of_outcome hrun
  obtain ⟨B, hB⟩ := hL (by rw [hslot]; exact Nat.succ_pos _)
    (by rw [hslot]; exact slotStart_cast S (q + 2))
    (by rw [hnv, hslot])
    (GoldilocksCorrectness.Proofs.Routines.awake_since_record_awake hτ
      (by rw [hslot, proposal_window_start_eqJ]; exact hτle))
  exact ⟨_, B, hl, step_sent_of_tick_send hl (Finset.mem_sdiff.2 ⟨hvA, hHon⟩) hrun hB⟩

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
`h_max` at least `H₂` (B2), so `H₂ ≤ h(B) + 1`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `H₂`: the threshold; `m`: the index of the last honest round opening slot; `i`: the index of an honest round opening slot; `rs`: the rounds of the honest round opening slots;
  `B`: its proposal.

Roots name blocks until `aR S r`: the climb's context `ClimbCtx` carries the premise at the action
time of round `r`; the opening's context `QuietCtx` reads up to the support cutoff of slot
`rs (i + 1) * R`, no later. -/
theorem quiet_rising_next_proposal (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd T₁ r H₂ m i : ℕ) (rs : ℕ → ℕ)
    (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
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
    (hT₁0 : T₁ ≤ slotStart S (rs 0 * S.C.R - 2 * S.C.k))
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
  obtain ⟨hs1, C⟩ := quietCtx_of S Sched x GST tGAT tAwakeEnd r m i rs hDiv hMono hSync hCatch
    (hRoots.mono (supportCutoff_mono S (by omega))) hParent hOwner hU hGST hThird hAwake
    hCommittees hEnd hSeq hi (opening_round_step hSeq hi) hir hNoCol hNo
  have hB0 : ProposalAt S Sched x (rs i * S.C.R - 1 + 1) B := by rw [← hs1]; exact hB
  have hRise' := hRise
  set s₀ := rs i * S.C.R - 1 with hs₀def
  set s'' := rs (i + 1) * S.C.R with hs''def
  clear_value s₀ s''
  have hsR := C.sR
  have hEnd' := C.cut_end
  have CC : ClimbCtx S Sched x GST tGAT tAwakeEnd T₁ r H₂ :=
    ⟨hDiv, hMono, hSync, hCatch, hRoots, hParent, hU, hGST, hT₁, hThird, hAwake, hH₂,
      hOld, hEnd⟩
  -- the times
  have hw0 := C.win (le_refl (s₀ + 1))
  have h0s : rs 0 * S.C.R ≤ s₀ + 1 := C.rs0
  have hT₁s₀ : T₁ + Δ S ≤ slotStart S (s₀ + 1 - S.C.k - 1) := by
    have h1 := slotStart_mono S (show rs 0 * S.C.R - 2 * S.C.k + 1 ≤ s₀ + 1 - S.C.k - 1 by
      have := hw0.1
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
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tGAT`, `tAwakeEnd`: the phase; `m`:
  the index of the last honest round opening slot; `j`: the index of an honest round opening slot; `rs`: the rounds of the honest round opening slots. -/
theorem opening_proposal_exists (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (tGAT tAwakeEnd m j : ℕ) (rs : ℕ → ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hj : j ≤ m) :
    ∃ B : Block V, ProposalAt S Sched x (rs j * S.C.R) B := by
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
  have hEnd' : supportCutoff S (rs j * S.C.R) ≤ tAwakeEnd :=
    le_trans (supportCutoff_mono S hjm) hSeq.last
  obtain ⟨h2k, hA⟩ := window_after_anchor S Sched rs m tGAT tAwakeEnd (rs j * S.C.R) hSeq h0j
  have hqH := hSeq.honest j hj
  set s'' := rs j * S.C.R with hs''def
  clear_value s''
  have hssA := slotStart_mono S (show s'' - 2 * S.C.k + 1 ≤ s'' by omega)
  have hcs'' := supportCutoff_eq S s''
  have hvs'' := voteTime_eq S s''
  have hqAH : ∀ t : ℕ, tGAT ≤ t → t ≤ supportCutoff S s'' →
      S.P.proposer s'' ∈ Sched.awake (t : Int) ∧ S.P.proposer s'' ∉ Sched.adv (t : Int) := by
    intro t h1 h2
    have hq' : S.P.proposer s'' ∉ Sched.adv (t : Int) :=
      fun hh => hqH (hMono _ _ (by exact_mod_cast h2) hh)
    exact ⟨hAwake t h1 (le_trans h2 hEnd') _ hq', hq'⟩
  have hs''2 : s'' - 2 + 2 = s'' := by omega
  have hpw := proposalWindowStart_eqJ S (s'' - 2)
  have hA21 : anchorCW S tGAT ≤ slotStart S (s'' - 2 + 1 + 1) := by
    rw [show s'' - 2 + 1 + 1 = s'' by omega]
    exact le_trans hA hssA
  have hdwA := dutyWindowStart_of_anchor S tGAT (s'' - 2 + 1) hA21
  obtain ⟨iB', B', hl', hsent'⟩ := honest_proposer_proposesJ S Sched x (s'' - 2) hDiv hMono
    (by
      intro t h1 h2
      rw [hpw] at h1
      rw [hs''2] at h2 ⊢
      exact hqAH t (le_trans (le_trans (Nat.le_add_right _ _) hdwA) h1) (by omega))
  rw [hs''2] at hl' hsent'
  exact ⟨B', iB', hl', hsent'⟩

end GoldilocksCorrectness.Proofs.Executions
