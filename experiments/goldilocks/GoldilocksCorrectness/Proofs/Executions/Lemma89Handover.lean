module
public import GoldilocksCorrectness.Proofs.View.Bridges
public import GoldilocksCorrectness.Proofs.Executions.Lemma89HealedRound
public import GoldilocksCorrectness.Proofs.Executions.Lemma89rTargets
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Climb5
public import GoldilocksCorrectness.Proofs.Executions.FinalityLivenessKit
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOfCertified

@[expose] public section

/-!

- C5 `round_justified_of_spacing3`: the routine fact behind the carrier;
- C8 `exists_handover_step`: some step is at the vote time of the last opening's slot;
- the kit on part A's line invariant: `PartAHyps.attestation_entry` (an honest attestation from the
  action time of round `r` on names the entry of a line source at its height) and
  `PartAHyps.attestation_target` (such an attestation at a height greater than `H₂` is a target);
- C7 `frames_at_phase_slots`, C4, C6 and the hand-over.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  proposalWindowStart anchorCW)
open GoldilocksCorrectness.Proofs.Routines (delivery_of_round dutyWindowStart_le_voteTime one_le_Δ
  round_slot_le_of_lt slotStart_mono slot_mono slot_mono_int supportCutoff_eq supportCutoff_lt
  supportCutoff_mono times_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_J_spec chainStateOf_T_h_spec
  chainStateOf_genesis_h chainStateOf_height_mono lem47_chain_state_heights
  round_justified_of_spacing3)
open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree mem_viable_heads_iff)

open GoldilocksCorrectness.Proofs.Routines (block_admissible_of mem_T_receive_block
  slot_lt_of_ancestorEq_of_treeClosed)
open GoldilocksCorrectness.Statements.Routines (TreeClosed)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks RootsNameBlocksIn CountedVotes
  ProgressCertOn JustificationCertOn FrameShape lem49_tick_attests RecordConsistent)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_compatible
  ancestorEq_antisymm compatible_iff compatible_of_ancestorEq_compatible ancestorEq_of_parent?
  ancestorEq_node_iff create_attestation_timeout state_transition_cases)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## C5 and C8 -/

/-- **C8, the hand-over step exists.** The proof; the audited statement is in
`Statements/Executions/Lemma89Statements.lean`. Why: the tick at the vote time of slot `s_m`
(`exists_lbl_tickAllAwake`, the time being at least `Δ ≥ 1`) ends at that time
(`time_of_lbl_tickAllAwake`). -/
theorem exists_handover_step (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s_m : ℕ) (hDiv : TimeDiverges x.toTrace) :
    ∃ i₁ : ℕ, x[i₁].time = voteTime S s_m := by
  have h1 : 1 ≤ voteTime S s_m := by
    have := voteTime_eq S s_m
    have := one_le_Δ S
    omega
  obtain ⟨i, hi⟩ := exists_lbl_tickAllAwake x hDiv h1
  exact ⟨i + 1, (time_of_lbl_tickAllAwake x hi).2⟩

/-- **C9, every honest round opening slot has a proposal (a copy for the slots from `2` on).** The proof; the
audited statement is in `Statements/Executions/Lemma89Statements.lean`. Why: the proposer is awake
and honest from the proposal window's start of slot `s` to its start, so its tick then proposes
(`honest_proposer_proposesJ`). -/
theorem opening_proposal_exists_of_window (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (tGAT tAwakeEnd s : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hs2 : 2 ≤ s) (hWindow : tGAT ≤ proposalWindowStart S s) (hEnd : slotStart S s ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ Sched.adv ((supportCutoff S s : ℕ) : Int)) :
    ∃ B : Block V, ProposalAt S Sched x s B := by
  obtain ⟨q, rfl⟩ : ∃ q, s = q + 2 := ⟨s - 2, by omega⟩
  have hsc : slotStart S (q + 2) ≤ supportCutoff S (q + 2) := by
    have := supportCutoff_eq S (q + 2)
    have := voteTime_eq S (q + 2)
    omega
  have hnt : ∀ t : ℕ, t ≤ slotStart S (q + 2) → S.P.proposer (q + 2) ∉ Sched.adv (t : Int) :=
    fun t ht h => hp (hMono _ _ (by exact_mod_cast le_trans ht hsc) h)
  obtain ⟨i, B, hl, hsent⟩ := honest_proposer_proposesJ S Sched x q hDiv hMono
    (fun t h1 h2 => ⟨hAwake t (le_trans hWindow h1) (le_trans h2 hEnd) _ (hnt t h2), hnt t h2⟩)
  exact ⟨B, i, hl, hsent⟩

/-! ## The honest attestations after the fast block's round are targets -/

namespace PartAHyps

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {A' : ACState V}

/-- **An honest attestation from the fast block's round on names a line source's entry.** An
attestation `a` that `u`, awake and outside the adversary set at `t`, put on the wire at the tick of
step `i` at a time `t` from the action time of round `r` to `tAwakeEnd`, was sent at the action
time of a round `r' ≥ r`, and names, at its height, the root of an entry block `E` that is a line
source of slot `r' * R`: `E` is the `T_h` of the fast block of `u`'s update then
(`fast_source_of_attestation`), a line source by `source_later`. -/
theorem attestation_entry (P : PartAHyps S Sched x GST tGAT tAwakeEnd r H₂ v L A') {i t : ℕ}
    {u : V} {a : Attestation V} (hl : x.lbl i = AtomicAction.tickAllAwake t) (ht : aR S r ≤ t)
    (htE : t ≤ tAwakeEnd) (hAw : u ∈ Sched.awake (t : Int)) (hHon : u ∉ Sched.adv (t : Int))
    (hSent : (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent) :
    ∃ (r' : ℕ) (E : Block V), r ≤ r' ∧ t = aR S r' ∧
      LineSource S Sched x r H₂ (r' * S.C.R) E ∧ IsEntry S.C E ∧
      (chainStateOf S.C E).h = a.h ∧ a.T = E.root := by
  obtain ⟨r', rfl⟩ := attest_time_round S Sched x hl hSent
  have hR := S.C.R_ge_two
  have hrr : r ≤ r' := by
    by_contra h
    have hlt : r' * S.C.R < r * S.C.R := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    have := supportCutoff_lt S (show r' * S.C.R + 1 < r * S.C.R + 1 by omega)
    unfold aR at ht
    omega
  obtain ⟨A₀, X, hU, hXf, -, hXh, hXT⟩ :=
    fast_source_of_attestation S Sched x r' u a ⟨i, hl, hAw, hHon, hSent⟩
  have hsrc := P.source_later hrr hHon hU hXf htE
  refine ⟨r', (chainStateOf S.C X).T_h, hrr, rfl,
    hsrc.anc (chainStateOf_T_h_spec S.C X).1, ?_, ?_, hXT.symm⟩
  · unfold IsEntry
    exact chainStateOf_T_h_T_h S.C X
  · rw [(chainStateOf_T_h_spec S.C X).2, hXh]

/-- **After the fast block's round, honest attestations at heights greater than `H₂` are
targets.** An attestation `a` that `u`, awake and outside the adversary set at `t ≤ tAwakeEnd`,
put on the wire at the tick of step `i` at `t`, with `a.h > H₂`, is a target.

Why (the induction of `no_honest_timeout_after_healing`, with the line's entries in place of
Lemma 82's honest chain): `create_attestation` builds a timeout only behind a recorded timeout or a
recorded target at the source's height naming another block (`create_attestation_timeout`), which
`u` sent earlier, at a tick (`record_content_sent_step`); sent before the action time of round `r`
its height would be at most `H₂` (`hOld`); a timeout sent later is excluded by the induction; a
target sent later names the entry of a line source at the height, as `a` does
(`attestation_entry`), and two line sources are compatible (`sources_compatible`), so two entries
at one height are one block. -/
theorem attestation_target (P : PartAHyps S Sched x GST tGAT tAwakeEnd r H₂ v L A') {i t : ℕ}
    {u : V} {a : Attestation V} (hl : x.lbl i = AtomicAction.tickAllAwake t)
    (htE : t ≤ tAwakeEnd) (hAw : u ∈ Sched.awake (t : Int)) (hHon : u ∉ Sched.adv (t : Int))
    (hSent : (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent)
    (hH : H₂ < a.h) : a.τ = false := by
  induction i using Nat.strong_induction_on generalizing t a with
  | _ i ih =>
  have ht : aR S r ≤ t := by
    by_contra hlt
    have := P.hOld i t u a hl (by omega) hAw hHon hSent
    unfold Height at *
    omega
  by_contra hτ
  have hτ' : a.τ = true := by simpa using hτ
  obtain ⟨-, n', sent, hrun, ha⟩ := tick_send_of_honestSendAt hl hSent
  obtain ⟨-, fi, source, -, -, hca, -⟩ := lem49_tick_attests S.C S.P S.X _ n' _ sent a hrun ha
  obtain ⟨hah, haT, hcase⟩ := create_attestation_timeout _ _ _ _ _ _ _ a hca hτ'
  rw [tickInputState_Λ] at hcase
  have hΛ : RecordConsistent (x[i][u].st).Λ := recordConsistent_of_exec S Sched x i u
  -- the earlier send is at a time at most `t`
  have htime : ∀ j t', j < i → x.lbl j = AtomicAction.tickAllAwake t' → t' ≤ t := by
    intro j t' hj hl'
    have h1 := (time_of_lbl_tickAllAwake x hl').2
    have h2 := (time_of_lbl_tickAllAwake x hl).2
    have := time_mono x (show j + 1 ≤ i + 1 by omega)
    omega
  rcases hcase with htimeout | ⟨T', htarget, hne⟩
  · obtain ⟨c, hc, hch, hcτ⟩ := (hΛ.timeoutRec _).1 htimeout
    obtain ⟨j, t', a', hj, hl', hAw', hHon', hsent', -, hcont, -⟩ :=
      record_content_sent_step S Sched x u i c hc
    have hh' : a'.h = a.h := by
      rw [hah, ← hch]; exact congrArg AttestationContent.h hcont
    have hτa' : a'.τ = true := by
      rw [← hcτ]; exact congrArg AttestationContent.τ hcont
    have := ih j hj hl' (le_trans (htime j t' hj hl') htE) hAw' hHon' hsent'
      (by rw [hh']; exact hH)
    rw [hτa'] at this
    cases this
  · obtain ⟨c, hc, hch, hcτ, hcT⟩ := (hΛ.targetRec _ _).1 htarget
    obtain ⟨j, t', a', hj, hl', hAw', hHon', hsent', -, hcont, -⟩ :=
      record_content_sent_step S Sched x u i c hc
    have hh' : a'.h = a.h := by
      rw [hah, ← hch]; exact congrArg AttestationContent.h hcont
    have hT' : a'.T = T' := by
      rw [← hcT]; exact congrArg AttestationContent.T hcont
    have ht't := htime j t' hj hl'
    have ht' : aR S r ≤ t' := by
      by_contra hlt
      have := P.hOld j t' u a' hl' (by omega) hAw' hHon' hsent'
      unfold Height at *
      omega
    obtain ⟨r₁, E, -, ht₁, hE, hEe, hEh, hEr⟩ := P.attestation_entry hl ht htE hAw hHon hSent
    obtain ⟨r₂, E', -, ht₂, hE', hEe', hEh', hEr'⟩ :=
      P.attestation_entry hl' ht' (le_trans ht't htE) hAw' hHon' hsent'
    -- the two sources are compatible
    have hσ : supportCutoff S (max (r₁ * S.C.R) (r₂ * S.C.R) + 1) ≤ tAwakeEnd := by
      rcases le_total (r₁ * S.C.R) (r₂ * S.C.R) with h | h
      · rw [max_eq_right h]
        have : t' = supportCutoff S (r₂ * S.C.R + 1) := ht₂
        omega
      · rw [max_eq_left h]
        have : t = supportCutoff S (r₁ * S.C.R + 1) := ht₁
        omega
    have hcomp := P.sources_compatible (fun σ' h' => P.lineInv_all σ'
        (le_trans (supportCutoff_mono S (by omega)) hσ)) hσ hE hE'
      (le_max_left _ _) (le_max_right _ _)
    have hEE : E = E' := by
      have hheq : (chainStateOf S.C E).h = (chainStateOf S.C E').h := by rw [hEh, hEh', hh']
      rcases (compatible_iff E E').1 hcomp with h | h
      · have := (lem47_chain_state_heights S.C E E').2.2.2.2 h hheq
        unfold IsEntry at hEe hEe'
        rw [hEe, hEe'] at this
        exact this
      · have := (lem47_chain_state_heights S.C E' E).2.2.2.2 h hheq.symm
        unfold IsEntry at hEe hEe'
        rw [hEe, hEe'] at this
        exact this.symm
    apply hne
    rw [← hT', hEr', ← hEE, ← hEr, haT]

end PartAHyps

/-! ## Small facts -/

/-- A proposal of slot `s ≥ 1` has the slot `s`, and its parent is an ancestor of it
(`proposal_parent_walk_end`). -/
theorem proposal_slot_parent (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) {s : ℕ} {B : Block V} (hs : 1 ≤ s)
    (hB : ProposalAt S Sched x s B) : B.slot = s ∧ B.parent.AncestorEq B := by
  obtain ⟨s₀, rfl⟩ : ∃ s₀, s = s₀ + 1 := ⟨s - 1, by omega⟩
  obtain ⟨i, hl, hsent⟩ := hB
  obtain ⟨h1, -, h3, -⟩ := proposal_parent_walk_end S Sched x s₀ i B _ hl hsent
  exact ⟨h1, ancestorEq_of_parent? h3⟩

omit [RootOrder] in
/-- The member sets shrink: a member of slot `σ + 1` is a member of slot `σ`. -/
theorem hon_succ_subset (S : Setup V) (Sched : Schedule V) (hMono : Sched.MonotoneCorruption)
    (σ : ℕ) : Hon S Sched (σ + 1) ⊆ Hon S Sched σ := by
  intro u hu
  unfold Hon roundMembers at hu ⊢
  obtain ⟨-, hu'⟩ := Finset.mem_sdiff.1 hu
  exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun h => hu' (hMono _ _
    (by exact_mod_cast supportCutoff_mono S (show σ + 1 ≤ σ + 1 + 1 by omega)) h)⟩

omit [RootOrder] in
/-- A validator outside the adversary set at the support cutoff of slot `σ + 1` is a member of
`Hon S Sched σ`. -/
theorem mem_hon_of_honest (S : Setup V) (Sched : Schedule V) {σ : ℕ} {u : V}
    (hu : u ∉ Sched.adv ((supportCutoff S (σ + 1) : ℕ) : Int)) : u ∈ Hon S Sched σ := by
  unfold Hon roundMembers
  exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hu⟩

omit [RootOrder] in
/-- A member of `Hon S Sched σ` is outside the adversary set at the support cutoff of slot
`σ + 1`. -/
theorem honest_of_mem_hon (S : Setup V) (Sched : Schedule V) {σ : ℕ} {u : V}
    (hu : u ∈ Hon S Sched σ) : u ∉ Sched.adv ((supportCutoff S (σ + 1) : ℕ) : Int) := by
  unfold Hon roundMembers at hu
  exact (Finset.mem_sdiff.1 hu).2

omit [RootOrder] in
/-- An updater of slot `σ` is a member of `Hon S Sched σ`. -/
theorem hon_of_updater (S : Setup V) (Sched : Schedule V) {σ : ℕ} {u : V}
    (hu : u ∈ updaterAt S Sched σ) : u ∈ Hon S Sched σ := by
  unfold updaterAt at hu
  exact mem_hon_of_honest S Sched (Finset.mem_sdiff.1 hu).2

/-! ## C7, the frames at the slots of the phase -/

/-- **C7, Lemma 89's frame clauses from the line invariant.** The proof; the audited statement is
in `Statements/Executions/Lemma89Statements.lean`. Why: a block on the honest chain before `s`
from `s₀` is on an updater's confirmation of a slot `s'` with `s₀ ≤ s' < s`; the updater is a
member of `Hon s'`, so the block is a line source of slot `s'` (`source_conf`, `s₀ ≥ r * R + k`);
`stepFrame_source` at slot `s − 1` gives `StepFrameAt` relative to it at every member of `Hon s`,
whose conjuncts are the two clauses.

Roots name blocks until `supportCutoff S s_m`: the bundle `PartAHyps` is built with its end time
`supportCutoff S s_m`, the latest time its kit reads here. -/
theorem frames_at_phase_slots (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r H₂ s₀ s_m : ℕ) (v : V) (L : Block V)
    (A' : ACState V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s_m))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hAnchor : anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hv : v ∉ Sched.adv ((aR S r : ℕ) : Int))
    (hL : (chainStateOf S.C L).h = H₂ + 1)
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A')
    (hFast : L ∈ A'.fast_blocks)
    (hs₀ : r * S.C.R + S.C.k + 2 ≤ s₀) (hEnd : supportCutoff S s_m ≤ tAwakeEnd) :
    ∀ s : ℕ, s₀ < s → s < s_m → ∀ w ∈ Hon S Sched s,
      VoterFrameOnChainAt S Sched x s₀ s w ∧ UpdaterFinalizedOnChainAt S Sched x s₀ s w := by
  -- the bundle with its end time `supportCutoff S s_m`
  have P : PartAHyps S Sched x GST tGAT (supportCutoff S s_m) r H₂ v L A' := ⟨hDiv, hMono,
    hSync, hCatch, hRoots, hParent, hOwner, hU, hGST,
    adversaryFewerThanThirdUntil_of_le (by exact_mod_cast hEnd) hThird,
    fun t' h1 h2 => hAwake t' h1 (le_trans h2 hEnd), hCommittees, hAnchor, hOld, hv, hUpdate,
    hFast, hL⟩
  have hEnd : supportCutoff S s_m ≤ supportCutoff S s_m := le_rfl
  have hk := S.C.k_ge_two
  intro s hs1 hs2 w hw
  obtain ⟨σ, rfl⟩ : ∃ σ, s = σ + 1 := ⟨s - 1, by omega⟩
  have hEnd' : supportCutoff S (σ + 2) ≤ supportCutoff S s_m :=
    le_trans (supportCutoff_mono S (by omega)) hEnd
  have hG := P.lineInv_upto hEnd'
  have hwadv : w ∉ Sched.adv ((supportCutoff S (σ + 2) : ℕ) : Int) := honest_of_mem_hon S Sched hw
  have key : ∀ B : Block V, OnHonestChainBefore S Sched x s₀ (σ + 1) B →
      StepFrameAt S Sched x B σ w := by
    rintro B ⟨s', hs', hs₀', u, hu, C, hC, hBC⟩
    have hsrc := P.source_conf (show r * S.C.R + S.C.k ≤ s' by omega) (hon_of_updater S Sched hu)
      (le_trans (supportCutoff_mono S (by omega)) hEnd) hC hBC
    exact P.stepFrame_source hG (by omega) hEnd' hwadv hsrc (by omega)
  refine ⟨fun B hB => ?_, fun B hB => (key B hB).2.2⟩
  obtain ⟨h1, h2, -⟩ := key B hB
  exact ⟨h1, h2⟩

/-! ## C4, consecutive openings after the fast block rise -/

/-- **C4, consecutive openings after the fast block rise (copy with the round's first slot).** The
proof; the audited statement is in `Statements/Executions/Lemma89Statements.lean`. Why: with no
root collision at `B`, `lem89r_quiet_round_targets` at the round of slot `s`, with the family of
the line sources of the slots `μ` with `μ + 2 ≤ s` (the line invariant at slot `s − 1` for the
chain invariant, `late_locks_on_sources` for the locks, `anchor_source` for the
proposer's anchor, `frame_source_at` and `frame_has_viable_head` for the proposer's viable heads),
its quiet round from `quiet_round_after_fast_block_opening`; its targets premise holds since
`B`'s height is greater than `H₂` (`B.parent` extends `L`, `parent_extends_sources`) and every
honest attestation at such a height from the fast block's round on is a target
(`PartAHyps.attestation_target`).

Roots name blocks until `supportCutoff S s''`: the bundle `PartAHyps` is built with its end time
`supportCutoff S s''`, the latest time its kit reads here; C2 reads up to the same time, Lemma 89r
up to `supportCutoff S (s'' - 1)`. -/
theorem opening_rises_after_fast_block_opening (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r H₂ s s'' : ℕ) (v : V)
    (L B B' : Block V) (A' : ACState V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s''))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hAnchor : anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hv : v ∉ Sched.adv ((aR S r : ℕ) : Int))
    (hL : (chainStateOf S.C L).h = H₂ + 1)
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A')
    (hFast : L ∈ A'.fast_blocks)
    (hs : r * S.C.R + S.C.k + 2 ≤ s) (hsR : S.C.R ∣ s) (hs'' : s + S.C.R ≤ s'')
    (hEnd : supportCutoff S s'' ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ Sched.adv ((supportCutoff S s : ℕ) : Int))
    (hq : S.P.proposer s'' ∉ Sched.adv ((supportCutoff S s'' : ℕ) : Int))
    (hB : ProposalAt S Sched x s B) (hB' : ProposalAt S Sched x s'' B') :
    RootCollisionAtProposal S Sched x s B ∨
    (B.AncestorEq B' ∧ (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∧
      ((chainStateOf S.C B'.parent).h = (chainStateOf S.C B).h →
        (chainStateOf S.C B').J = (chainStateOf S.C B).T_h) ∧
      ∀ u ∈ Hon S Sched s,
        (stateBefore x (supportCutoff S (s + 1) + 1) u).A.saved_confirmation s = some B) := by
  by_cases hCol : RootCollisionAtProposal S Sched x s B
  · exact Or.inl hCol
  right
  -- the bundle with its end time `supportCutoff S s''`
  have P : PartAHyps S Sched x GST tGAT (supportCutoff S s'') r H₂ v L A' := ⟨hDiv, hMono,
    hSync, hCatch, hRoots, hParent, hOwner, hU, hGST,
    adversaryFewerThanThirdUntil_of_le (by exact_mod_cast hEnd) hThird,
    fun t' h1 h2 => hAwake t' h1 (le_trans h2 hEnd), hCommittees, hAnchor, hOld, hv, hUpdate,
    hFast, hL⟩
  have hk := S.C.k_ge_two
  have hR := S.C.R_ge_two
  have hEndM : ∀ σ : ℕ, σ ≤ s'' → supportCutoff S σ ≤ tAwakeEnd := fun σ h =>
    le_trans (supportCutoff_mono S h) hEnd
  have hEndP : ∀ σ : ℕ, σ ≤ s'' → supportCutoff S σ ≤ supportCutoff S s'' := fun σ h =>
    supportCutoff_mono S h
  have hQuiet := quiet_round_after_fast_block_opening S Sched x GST tGAT tAwakeEnd r H₂ s s'' v L B
    A' hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hThird hAwake hCommittees
    hAnchor hOld hv hL hUpdate hFast hs hsR hs'' hEnd hp hq hB hCol
  obtain ⟨rs, hrs⟩ : ∃ c : ℕ, s = c * S.C.R := by
    obtain ⟨c, hc⟩ := hsR
    exact ⟨c, by rw [hc, Nat.mul_comm]⟩
  -- the slots: `s = σ₂ + 2`
  obtain ⟨σ₂, hσ₂⟩ : ∃ σ₂, s = σ₂ + 2 := ⟨s - 2, by omega⟩
  obtain ⟨hvs, hcs, hfs, hss, hΔ⟩ := times_eq S s
  obtain ⟨hvs1, hcs1, -, hss1, -⟩ := times_eq S (s - 1)
  rw [show s - 1 + 1 = s by omega] at hss1
  have hEnd2 : supportCutoff S (σ₂ + 2) ≤ supportCutoff S s'' := by
    rw [← hσ₂]; exact hEndP s (by omega)
  have hG : ∀ σ', σ' ≤ σ₂ → LineInv S Sched x r H₂ σ' := P.lineInv_upto hEnd2
  have hGs1 : LineInv S Sched x r H₂ (s - 1) :=
    P.lineInv_all (s - 1) (by rw [show s - 1 + 1 = s by omega]; exact hEndP s (by omega))
  -- the family: the line sources of the slots `μ` with `μ + 2 ≤ s`
  let 𝓒 : Block V → Prop := fun C => ∃ μ : ℕ, μ + 2 ≤ s ∧ LineSource S Sched x r H₂ μ C
  have hChain : ChainInvFor S Sched x (Hon S Sched (s - 1)) 𝓒 (s - 1) := by
    rintro C ⟨μ, hμ, hC⟩
    exact hGs1 μ C hC (by omega)
  have hFamLocks : ∀ w ∈ Hon S Sched (s - 1), LiveLocksOnFamilyAt S Sched x 𝓒 (s - 1) w := by
    intro w hw A₁ hRv e he hl
    have hvE : voteTime S (s - 1 + 1) ≤ supportCutoff S s'' := by
      rw [show s - 1 + 1 = s by omega]
      exact le_trans (by omega) (hEndP s (by omega))
    obtain ⟨D, ⟨μ, hμ, hsrc⟩, heD⟩ := P.late_locks_on_sources
      (show r * S.C.R + S.C.k ≤ s - 1 by omega) hvE hw A₁ hRv e he hl
    exact ⟨D, ⟨μ, by omega, hsrc⟩, heD⟩
  obtain ⟨μA, hμA, hAsrc⟩ := P.anchor_source (show r * S.C.R + S.C.k + 2 ≤ s by omega)
    (hEndP s (by omega)) hp
  have hpt : S.P.proposer s ∉ Sched.adv ((slotStart S s : ℕ) : Int) :=
    fun h => hp (hMono _ _ (by exact_mod_cast (show slotStart S s ≤ supportCutoff S s by omega)) h)
  have hFrameP : ∀ C : Block V, 𝓒 C →
      ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S s) (S.P.proposer s)).S).tree,
        W ∈ (fg_to_ac (stateBefore x (slotStart S s) (S.P.proposer s)).S).viable_heads ∧
        C.AncestorEq W := by
    rintro C ⟨μ, hμ, hC⟩
    obtain ⟨h1, h2, -⟩ := P.frame_source_at (σ := σ₂) (t := slotStart S s) hG (by omega) hEnd2
      (by rw [show σ₂ + 1 = s - 1 by omega]; omega) (by rw [← hσ₂]; omega) hpt hC (by omega)
    rcases (compatible_iff _ _).1 h1 with hRC | hCR
    · exact h2 hRC
    · obtain ⟨W, hW⟩ := frame_has_viable_head S Sched x (slotStart S s) (S.P.proposer s)
      obtain ⟨hWT, hFW, hRW, -⟩ := (mem_viable_heads_iff _ _).1 hW
      exact ⟨W, (mem_fg_to_ac_tree _ _).2 ⟨hWT, hFW⟩, hW, ancestorEq_trans hCR hRW⟩
  -- the proposer's and the next proposer's windows
  have hdw := P.dws (show r * S.C.R ≤ s - 1 by omega)
  have hdwv := dutyWindowStart_le_voteTime S (s - 1)
  have hpAwake : ∀ t : ℕ, voteTime S (s - 1) ≤ t → t ≤ slotStart S s →
      S.P.proposer s ∈ Sched.awake (t : Int) := fun t h1 h2 =>
    (P.window hp (hEndP s (by omega)) t (by omega) (by omega)).1
  have hpHon : HonestThroughTime Sched ((voteTime S s : ℕ) : Int) (S.P.proposer s) :=
    fun t' ht' h => hp (hMono _ _ (le_trans ht' (by exact_mod_cast (show voteTime S s ≤
      supportCutoff S s by omega))) h)
  have hqH : S.P.proposer s'' ∈ Hon S Sched (s'' - 1) := by
    apply mem_hon_of_honest
    rw [show s'' - 1 + 1 = s'' by omega]
    exact hq
  have hHonSup : Finset.univ \ Sched.adv (tAwakeEnd : Int) ⊆ Hon S Sched s := by
    intro u hu
    apply mem_hon_of_honest
    have hle : supportCutoff S (s + 1) ≤ tAwakeEnd := hEndM (s + 1) (by omega)
    exact fun h => (Finset.mem_sdiff.1 hu).2 (hMono _ _ (by exact_mod_cast hle) h)
  have h89 := lem89r_quiet_round_targets S Sched x GST rs s s'' (Hon S Sched) 𝓒 B B'
    (S.P.proposer s) (S.P.proposer s'') hDiv hMono hSync hCatch hSyncF hCatchF
    (hRoots.mono (supportCutoff_mono S (by omega))) hParent hOwner hU hrs (by omega)
    (delivery_of_round S hs'') (P.gst (show r * S.C.R ≤ s - 1 by omega)).2.1
    (adversaryFewerThanThirdUntil_of_le (by exact_mod_cast hEndM (s + 1) (by omega)) hThird)
    (fun s' _ _ => hon_succ_subset S Sched hMono s')
    (fun s' h1 h2 w hw t ht1 ht2 => P.member0 (by omega) hw (hEndP _ (by omega)) t ht1 ht2)
    (quorum_le_of_phase_set Sched tAwakeEnd _ hThird hHonSup) (fun s' h1 _ => P.committee (by omega)) hpAwake hpHon hqH rfl
    rfl hB hB' hQuiet hChain hFamLocks ⟨μA, hμA, hAsrc⟩ hFrameP
  rcases h89 with hcol | ⟨hBB', -, h3, hsaved, -, -⟩
  · exact absurd hcol hCol
  -- `B`'s height is greater than `H₂`
  obtain ⟨-, hPB⟩ := proposal_slot_parent S Sched x (show 1 ≤ s by omega) hB
  have hLP := P.parent_extends_sources (show r * S.C.R + S.C.k + 2 ≤ s by omega)
    (hEndP s (by omega)) hp hB (r * S.C.R) L (P.source_L (hEndP _ (by omega))) (by omega)
  have hHB : H₂ < (chainStateOf S.C B).h := by
    have h1 := chainStateOf_height_mono S.C (ancestorEq_trans hLP hPB)
    rw [hL] at h1
    unfold Height at *
    omega
  obtain ⟨hrise, hjust⟩ := h3 (fun u _ j t' a hl ht' hawk hadv hsent hah =>
    P.attestation_target hl (le_trans ht' (hEndP (s + 1) (by omega))) hawk hadv hsent
      (by rw [hah]; exact hHB))
  exact ⟨hBB', hrise, hjust, hsaved⟩

/-! ## The kit of C6: delivery, the justification cache, the honest chain -/

section Delivery

/-- **A block held early is in the tree at a later step.** When `p`, honest at `t ≥ 1`, holds `B`
before `t ≤ τ + 1`, the network is synchronous from `GST ≤ τ`, `w` is awake and honest from `τ` to
`τ + Δ`, and `w`'s finalized block before `τ + Δ` is an ancestor of `B` or `B`, then `w` holds `B`
at every step `i₁` at a time at least `τ + Δ`. The proof is `mem_T_before_add_delay`'s, with the
delivery read from the send's own time (at most `τ`) and the result at the step `i₁`.

Roots name blocks until `τ + Δ S`: the delivery to `w`, before `τ + Δ`, against `p`'s block held
before `t ≤ τ + 1`. -/
theorem mem_T_at_step_of_held {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
    (hdiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption) {GST : ℕ}
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    {τ : ℕ}
    (hRoots : RootsNameBlocksUntil S Sched x (τ + Δ S))
    (hParent : ParentHeldAtDelivery S Sched x)
    {t i₁ : ℕ} {p w : V} {B : Block V}
    (ht : 1 ≤ t) (htτ : t ≤ τ + 1) (hGST : GST ≤ τ)
    (hp : p ∉ Sched.adv (t : Int)) (hB : B ∈ (stateBefore x t p).S.T)
    (hw : ∀ t' : ℕ, τ ≤ t' → t' ≤ τ + Δ S →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    (hF : (stateBefore x (τ + Δ S) w).S.F.AncestorEq B)
    (hi₁ : τ + Δ S ≤ x[i₁].time) :
    B ∈ (x[i₁][w].st).S.T := by
  have hΔ := one_le_Δ S
  by_cases hg : B = Block.genesis
  · subst hg
    exact genesis_mem_T_of_exec S Sched x _ w
  obtain ⟨i, hi, hsend, hhon, hslot⟩ := tree_block_relayed_before hMono hB hg
  have hit : x[i + 1].time ≤ τ := by
    have h1 := (lt_stepBefore_iff x hdiv).1 hi
    omega
  obtain ⟨d, hid, hl, hd⟩ := delivered_before_stepBefore_of_honest_send x hdiv hSync hCatch
    hMono (sm := ⟨p, NamedObject.block B⟩) ⟨hsend, hhon hp⟩ trivial hit hGST hw
  have hdi₁ : stepBefore x (τ + Δ S) < i₁ := stepBefore_lt_of_le_time x hdiv (by omega) hi₁
  obtain ⟨-, hwh, hstep⟩ := deliver_step_state x hl
  suffices h : B ∈ (x[d + 1][w].st).S.T from mem_T_mono x w (by omega) h
  by_cases hheld : B ∈ (x[d][w].st).S.T
  · exact mem_T_mono x w (Nat.le_succ d) hheld
  rw [hstep]
  apply mem_T_receive_block
  right
  have hInvU := (lem11_node_invariant S Sched x (stepBefore x t) p).1
  obtain ⟨hparU, hwf, hprop, hps⟩ := hInvU.2.2.1.2 B hB hg
  have hTu : x[stepBefore x t].time + 1 = t := (stepBefore_spec x hdiv ht).2.1
  have huh : p ∉ Sched.adv (x[stepBefore x t].time : Int) := fun h =>
    hp (hMono _ _ (by omega) h)
  have hFd : (x[d][w].st).S.F.AncestorEq B :=
    ancestorEq_trans (F_ancestorEq_of_le x w (le_of_lt hd)) hF
  have hpar : B.parent ∈ (x[d][w].st).S.T :=
    hParent d w _ B hl rfl hg ((compatible_iff _ _).2 (Or.inl hFd))
  have hInvW := (lem11_node_invariant S Sched x d w).1
  refine block_admissible_of _ _ _ _ _ hwf ?_ ?_ hpar hFd hprop hps ?_
  · rw [(slot_current_at_delivery hl).1]
    calc B.slot ≤ S.C.slot ((x[i + 1][p].st).t) := hslot
      _ ≤ S.C.slot ((x[i + 1].time : ℕ) : Int) := slot_mono_int S (clock_le_time x (i + 1) p)
      _ ≤ S.C.slot ((x[d].time : ℕ) : Int) := slot_mono S (time_mono x hid)
  · intro B' hB' hr
    have hdt : x[d].time ≤ τ + Δ S :=
      le_of_lt (lt_of_le_of_lt (time_le_succ x d) ((lt_stepBefore_iff x hdiv).1 hd))
    have hBB : B' = B := hRoots B' B ⟨d, w, hwh, hdt, hB'⟩
      ⟨stepBefore x t, p, huh, by omega, hB⟩ hr
    exact hheld (hBB ▸ hB')
  · intro a ha
    have h1 := hInvU.2.2.2.2.2.2.1 B hB hg a ha
    rw [hInvU.2.2.2.2.2.1 B.parent hparU] at h1
    rw [hInvW.2.2.2.2.2.1 B.parent hpar]
    exact h1

end Delivery

/-- **The justification cache bounds a held block's justification height.** At a step `i` at a
time at most `tEnd`, with fewer than a third of the validators in the adversary set up to `tEnd`,
an honest `w` holding `B` has `h_j(B)` at most its cache `h_j`: when `w`'s finalized block, the
finalized block of a held block `D`'s chain state, is an ancestor of `B` (Lemma 68, when `h_F(D)` is
less than `B`'s height), by Lemma 57; otherwise `h_j(B) < h(B) ≤ h_F(D) ≤ h_j(D) ≤ h_j`.

Roots name blocks until `tR`, at least `x[i].time`: Lemma 68 at the step `i`. -/
theorem h_j_ge_of_held_exec (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) {tR : ℕ} (hRoots : RootsNameBlocksUntil S Sched x tR) (tEnd i : ℕ)
    (w : V) (B : Block V) (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tEnd : Int))
    (hi : x[i].time ≤ tEnd) (hw : w ∉ Sched.adv (x[i].time : Int))
    (hB : B ∈ (x[i][w].st).S.T)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : x[i].time ≤ tR) :
    (chainStateOf S.C B).h_j ≤ (x[i][w].st).S.h_j := by
  obtain ⟨D, hD, hF⟩ := finalizedFromChain_of_exec S Sched x i w
  have hσ : ∀ X ∈ (x[i][w].st).S.T, (x[i][w].st).S.σ X = chainStateOf S.C X :=
    fun X hX => (lem11_node_invariant S Sched x i w).1.2.2.2.2.2.1 X hX
  have hT : AdversaryFewerThanThirdUntil Sched (validator_count V) (max (x[i].time : Int) (x[i].time : Int)) := by
    rw [max_self]
    exact adversaryFewerThanThirdUntil_of_le (by exact_mod_cast hi) hThird
  by_cases hlt : (chainStateOf S.C D).h_F < (chainStateOf S.C B).h
  · have hFB := lem68_honest_past_finalized S Sched x hU hRoots i i w w D B hT hw hw hD hB hlt
      (max_le htR htR)
    have := h_j_of_mem_T_of_exec S Sched x i w B hB (by rw [hF]; exact hFB)
    rw [hσ B hB] at this
    exact this
  · have hFD : (x[i][w].st).S.F.AncestorEq D := by
      rw [hF]
      by_cases h0 : (chainStateOf S.C D).h_F = 0
      · rw [GoldilocksCorrectness.Proofs.Routines.chainStateOf_F_genesis S.C D h0]
        exact GoldilocksCorrectness.Proofs.Routines.genesis_ancestorEq D
      · exact ((GoldilocksCorrectness.Statements.Routines.lem66_chain_state_certified S.C D).2.2
          (Nat.one_le_iff_ne_zero.mpr h0)).2.2.1
    have hjD := h_j_of_mem_T_of_exec S Sched x i w D hD hFD
    rw [hσ D hD] at hjD
    have h1 := (lem47_chain_state_heights S.C B B).1.2.1
    have h2 := (lem47_chain_state_heights S.C D D).1.2.2
    unfold Height at *
    omega

namespace PartAHyps

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {A' : ACState V}

/-- **An honest finalized block before a proposal's vote time is an ancestor of the proposal.** For
the honest proposal `B` of a slot `s ≥ r * R + k + 2` whose support cutoff is in the phase, the
finalized block of every validator honest at the vote time of slot `s`, before that time, is an
ancestor of `B`: it is an ancestor of its root (Lemma 46), a line source of a round's first slot
`μ` with `μ + 2 ≤ s` (`root_source`), and `B`'s parent extends every such source
(`parent_extends_sources`). -/
theorem F_before_vote_ancestor_proposal (P : PartAHyps S Sched x GST tGAT tAwakeEnd r H₂ v L A')
    {s : ℕ} {B : Block V} {u : V} (hs : r * S.C.R + S.C.k + 2 ≤ s)
    (hEnd : supportCutoff S s ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ Sched.adv ((supportCutoff S s : ℕ) : Int))
    (hB : ProposalAt S Sched x s B) (hu : u ∉ Sched.adv ((voteTime S s : ℕ) : Int)) :
    (stateBefore x (voteTime S s) u).S.F.AncestorEq B := by
  have hk := S.C.k_ge_two
  obtain ⟨σ, rfl⟩ : ∃ σ, s = σ + 2 := ⟨s - 2, by omega⟩
  obtain ⟨hvs, hcs, -, hss, hΔ⟩ := times_eq S (σ + 2)
  have hG := P.lineInv_upto hEnd
  have haR : aR S r < voteTime S (σ + 2) := by
    have : aR S r = supportCutoff S (r * S.C.R + 1) := rfl
    have := supportCutoff_mono S (show r * S.C.R + 1 ≤ σ + 1 by omega)
    obtain ⟨-, hc1, -, hs1, -⟩ := times_eq S (σ + 1)
    rw [show σ + 1 + 1 = σ + 2 from rfl] at hs1
    omega
  obtain ⟨r', -, hcut, hsrc⟩ := P.root_source hG (show r * S.C.R ≤ σ by omega) hEnd haR
    (by omega) hu
  have hr' : r' * S.C.R + 2 ≤ σ + 2 := by
    by_contra h
    have := supportCutoff_mono S (show σ + 2 ≤ r' * S.C.R + 1 by omega)
    omega
  obtain ⟨-, hPB⟩ := proposal_slot_parent S Sched x (show 1 ≤ σ + 2 by omega) hB
  exact ancestorEq_trans (F_ancestorEq_fc_root_of_stateBefore S Sched x _ u)
    (ancestorEq_trans (P.parent_extends_sources hs hEnd hp hB _ _ hsrc hr') hPB)

/-- **The old attestations at an opening after the fast block.** For the honest proposal `B` of a
round's first slot `s ≥ r * R + k + 2` whose support cutoff of slot `s + 1` is in the phase, every
honest attestation sent before that support cutoff has a height at most `B`'s: before the action
time of round `r` at most `H₂ < h(B)`; from then on, it names a line source's entry of a round's
first slot `μ` with `μ + 2 ≤ s` at its height (`attestation_entry`, `round_slot_le_of_lt`), an
ancestor of `B`'s parent (`parent_extends_sources`). -/
theorem old_attestations_at_opening (P : PartAHyps S Sched x GST tGAT tAwakeEnd r H₂ v L A')
    {s : ℕ} {B : Block V} (hs : r * S.C.R + S.C.k + 2 ≤ s) (hsR : S.C.R ∣ s)
    (hEnd : supportCutoff S (s + 1) ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ Sched.adv ((supportCutoff S s : ℕ) : Int))
    (hB : ProposalAt S Sched x s B) :
    OldAttestationsAtMost S Sched x (supportCutoff S (s + 1)) (chainStateOf S.C B).h := by
  have hk := S.C.k_ge_two
  have hEnd0 : supportCutoff S s ≤ tAwakeEnd := le_trans (supportCutoff_mono S (by omega)) hEnd
  obtain ⟨-, hPB⟩ := proposal_slot_parent S Sched x (show 1 ≤ s by omega) hB
  have hPar := P.parent_extends_sources hs hEnd0 hp hB
  have hLB : (chainStateOf S.C L).h ≤ (chainStateOf S.C B).h :=
    chainStateOf_height_mono S.C (ancestorEq_trans (hPar (r * S.C.R) L
      (P.source_L (le_trans (supportCutoff_mono S (by omega)) hEnd)) (by omega)) hPB)
  intro i t u a hl ht hAw hHon hSent
  by_cases htr : aR S r ≤ t
  · obtain ⟨r', E, -, rfl, hE, -, hEh, -⟩ :=
      P.attestation_entry hl htr (by omega) hAw hHon hSent
    have h2 := round_slot_le_of_lt S hsR ht
    rw [← hEh]
    exact chainStateOf_height_mono S.C (ancestorEq_trans (hPar _ E hE h2) hPB)
  · have := P.hOld i t u a hl (by omega) hAw hHon hSent
    rw [P.hL] at hLB
    unfold Height at *
    omega

end PartAHyps

/-! ## C6, the caches at the hand-over step -/

/-- **C6, the caches at the hand-over step (copy with the proposal held and the finalized blocks
on it).** The proof; the audited statement is in `Statements/Executions/Lemma89Statements.lean`.
Why: `B₃` reaches every validator `u` honest at `x[i₁].time` by the vote time of slot `s₃`
(`mem_T_at_step_of_held`, `u`'s finalized block before that time an ancestor of `B₃` by
hypothesis), so `h_j(B₃) ≤ u`'s cache (`h_j_ge_of_held_exec`), greater than `H`; `u`'s justified
block is that of a held block `D`'s chain state with its cache (`cachesWitnessed_of_exec`), carried
by a justification certificate on `D`'s chain at that height (Lemma 66), so `hCerts` gives an
entry `E` on the honest chain with its root, and `E` is the justified block (roots name blocks); the
finalized block is an ancestor of the justified one (Lemma 46).

Roots name blocks until `x[i₁].time`: the justified block `u` holds at the step `i₁` against the
entry `hCerts` names, at a slot whose update ran by `x[i₁].time`; `B₃` reaches `u` by the vote time
of slot `s₃`, before it. -/
theorem caches_at_handover_of_held (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd s₀ H s₃ s_m i₁ : ℕ) (B₃ : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (x[i₁].time))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hs₃ : s₃ ≤ s_m) (htGAT : tGAT ≤ slotStart S s₃)
    (hEnd : supportCutoff S s_m ≤ tAwakeEnd)
    (hp : S.P.proposer s₃ ∉ Sched.adv ((supportCutoff S s₃ : ℕ) : Int))
    -- the proposer holds `B₃` right after its proposal
    (hHeld : B₃ ∈ (stateBefore x (slotStart S s₃ + 1) (S.P.proposer s₃)).S.T)
    -- every validator honest at the vote time of slot `s₃` has its finalized block before that
    -- time `B₃` or an ancestor of `B₃`
    (hF₃ : ∀ u : V, u ∉ Sched.adv ((voteTime S s₃ : ℕ) : Int) →
      (stateBefore x (voteTime S s₃) u).S.F.AncestorEq B₃)
    (hJ : H < (chainStateOf S.C B₃).h_j)
    -- every justified block an honest validator holds at the step `i₁` at a height greater than
    -- `H` is on the chain, at a slot whose update ran by `x[i₁].time`
    (hCerts : ∀ (w : V) (D T : Block V) (h : Height),
      D ∈ (x[i₁][w].st).S.T → JustificationCertOn D h T → H < h →
      ∃ (s_a : ℕ) (E : Block V), supportCutoff S (s_a + 1) ≤ x[i₁].time ∧
        OnHonestChainAt S Sched x s₀ s_a E ∧ IsEntry S.C E ∧
        (chainStateOf S.C E).h = h ∧ T.root = E.root)
    (hi₁ : x[i₁].time = voteTime S s_m) :
    ∀ u : V, u ∉ Sched.adv (x[i₁].time : Int) → CachesOnChain S Sched x s₀ H (x[i₁][u].st) := by
  intro u hu
  have hΔ := one_le_Δ S
  obtain ⟨hvs3, hcs3, -, -, -⟩ := times_eq S s₃
  obtain ⟨hvsm, hcsm, -, -, -⟩ := times_eq S s_m
  have hss := slotStart_mono S hs₃
  have hti : x[i₁].time ≤ tAwakeEnd := by omega
  have hut : ∀ t : ℕ, t ≤ x[i₁].time → u ∉ Sched.adv (t : Int) := fun t ht h =>
    hu (hMono _ _ (by exact_mod_cast ht) h)
  -- `B₃` is held at the step `i₁`
  have hp1 : S.P.proposer s₃ ∉ Sched.adv (((slotStart S s₃ + 1 : ℕ)) : Int) :=
    fun h => hp (hMono _ _ (by exact_mod_cast (show slotStart S s₃ + 1 ≤ supportCutoff S s₃ by
      omega)) h)
  have hB₃ : B₃ ∈ (x[i₁][u].st).S.T := by
    refine mem_T_at_step_of_held hDiv hMono hSync hCatch (hRoots.mono (by omega)) hParent
      (t := slotStart S s₃ + 1)
      (τ := slotStart S s₃) (by omega) le_rfl (le_trans hGST htGAT) hp1 hHeld
      (fun t' h1 h2 => ⟨hAwake t' (by omega) (by omega) u (hut t' (by omega)),
        hut t' (by omega)⟩) ?_ (by omega)
    rw [← hvs3]
    exact hF₃ u (hut _ (by omega))
  have hhj := h_j_ge_of_held_exec S Sched x hU hRoots tAwakeEnd i₁ u B₃ hThird hti hu hB₃ le_rfl
  -- the justified block is a held block's, with its certificate
  obtain ⟨⟨D, hD, hJD, hjD⟩, -, -⟩ := cachesWitnessed_of_exec S Sched x i₁ u
  have hH : H < (x[i₁][u].st).S.h_j := lt_of_lt_of_le hJ hhj
  have h1 : 1 ≤ (chainStateOf S.C D).h_j := by rw [← hjD]; unfold Height at *; omega
  obtain ⟨hcert, hJDD, hJh⟩ :=
    (GoldilocksCorrectness.Statements.Routines.lem66_chain_state_certified S.C D).1 h1
  obtain ⟨s_a, E, hcut, hE, hEe, hEh, hEr⟩ := hCerts u D _ _ hD hcert (by rw [← hjD]; exact hH)
  have hJT : (chainStateOf S.C D).J ∈ (x[i₁][u].st).S.T :=
    ancestors_mem_T_of_exec S Sched x i₁ u D _ hD hJDD
  have hJE : (chainStateOf S.C D).J = E :=
    hRoots _ _ ⟨i₁, u, hu, le_rfl, hJT⟩
      (onHonestChainAt_inHonestTreeBy S Sched x hMono s₀ s_a _ E hE hcut) hEr
  refine ⟨hH, ?_, ?_, ?_, F_ancestorEq_J_of_exec S Sched x i₁ u⟩
  · rw [hJD, hJE]; exact ⟨s_a, hE⟩
  · rw [hJD, hJE]; exact hEe
  · rw [hJD, hjD]; exact hJh

/-! ## The hand-over -/

/-- **The hand-over after the fast block (part C's assembly).** The proof; the audited statement
is in `Statements/Executions/Lemma89Statements.lean`. Why: with no root collision at an honest
round opening slot, every honest round opening slot has its proposal `B_i`, of its slot and held
by its proposer (`opening_proposal_exists`, `opening_proposal_held`); `s₀ := s_j`, `B₀ := B_j`; C1
and C3 (their copies) at `j` give the base, the saved `B₀` and `B₀.slot = s₀`; the old
attestations are at most `h(B₀)` (`old_attestations_at_opening`), passed on as they are; C7 gives
the frames for `s₀ < s < s_m`; C4 (its copy) at `j` and `j + 1` gives `B_j ⪯ B_{j+1} ⪯ B_{j+2}`,
each one height higher, and the justification clause at `j + 1`; `B_{j+1}`'s entry is a strict
descendant of `B_j`, so `HonestOpeningSeq.spacing` at `j` and the tree's slot order give C5's
hypotheses, and `h_j(B_{j+2}) ≥ h(B_{j+1}) ≥ h(B₀) + 1`; C8 gives `i₁`; C6 (its copy) the caches at
the threshold `h(B₀)`, its certificates on the honest chain from `s₀`, at a slot
whose update ran by `x[i₁].time`, by `cert_entry_at_slot` (Lemma 83's route with Lemma 82 (b), the
old attestations at most `h(B₀)` before the support cutoff of slot `s₀ + 1`), the finalized blocks
on `B_{j+2}` by
`F_before_vote_ancestor_proposal`.

Roots name blocks until `supportCutoff S (rs m * S.C.R)`: the bundle `PartAHyps` is built with its
end time `supportCutoff S (rs m * S.C.R)`; C4 at the honest round opening slots `j` and `j + 1`, C1,
C3, C6 and C7 read up to that time. -/
theorem handover_after_fast_block (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd m r H₂ : ℕ) (rs : ℕ → ℕ) (v : V)
    (L : Block V) (A' : ACState V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (rs m * S.C.R)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    -- the climb's output
    (hAnchor : anchorCW S tGAT ≤ slotStart S (r * S.C.R + 1))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hv : v ∉ Sched.adv ((aR S r : ℕ) : Int))
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A')
    (hFast : L ∈ A'.fast_blocks) (hL : (chainStateOf S.C L).h = H₂ + 1)
    (j : ℕ) (hj2 : j + 2 ≤ m) (hsj : r * S.C.R + S.C.k + 2 ≤ rs j * S.C.R) :
    RootCollisionAtOpening S Sched x rs m ∨
    (∃ (j' s₀ i₁ : ℕ) (B₀ : Block V),
      j' < m ∧ s₀ = rs j' * S.C.R ∧ x[i₁].time = voteTime S (rs m * S.C.R) ∧
      HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀ ∧
      (∀ u ∈ updaterAt S Sched s₀,
        (stateBefore x (supportCutoff S (s₀ + 1) + 1) u).A.saved_confirmation s₀ = some B₀) ∧
      B₀.slot = s₀ ∧
      OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) (chainStateOf S.C B₀).h ∧
      (∀ s : ℕ, s₀ < s → s < rs m * S.C.R →
        ∀ w ∈ roundMembers S Sched (s + 1),
          VoterFrameOnChainAt S Sched x s₀ s w ∧ UpdaterFinalizedOnChainAt S Sched x s₀ s w) ∧
      (∀ u : V, u ∉ Sched.adv (x[i₁].time : Int) →
        CachesOnChain S Sched x s₀ (chainStateOf S.C B₀).h (x[i₁][u].st))) := by
  classical
  by_cases hNoCol : RootCollisionAtOpening S Sched x rs m
  · exact Or.inl hNoCol
  right
  -- the bundle with its end time `supportCutoff S (rs m * S.C.R)`
  have P : PartAHyps S Sched x GST tGAT (supportCutoff S (rs m * S.C.R)) r H₂ v L A' := ⟨hDiv,
    hMono, hSync, hCatch, hRoots, hParent, hOwner, hU, hGST,
    adversaryFewerThanThirdUntil_of_le (by exact_mod_cast hSeq.last) hThird,
    fun t' h1 h2 => hAwake t' h1 (le_trans h2 hSeq.last), hCommittees, hAnchor, hOld, hv,
    hUpdate, hFast, hL⟩
  have hk := S.C.k_ge_two
  have hR := S.C.R_ge_two
  have hΔ := one_le_Δ S
  have hmono := r_lt_of_lt_of_mono rs m hSeq.mono
  have hle : ∀ a b : ℕ, a ≤ b → b ≤ m → rs a * S.C.R ≤ rs b * S.C.R := by
    intro a b hab hbm
    rcases Nat.lt_or_ge a b with h | h
    · exact Nat.mul_le_mul_right _ (le_of_lt (hmono a b h hbm))
    · rw [show a = b by omega]
  have hss : ∀ i, i < m → rs i * S.C.R + S.C.R ≤ rs (i + 1) * S.C.R := by
    intro i hi
    have h' : (rs i + 1) * S.C.R ≤ rs (i + 1) * S.C.R :=
      Nat.mul_le_mul_right _ (hmono i (i + 1) (by omega) hi)
    rw [Nat.add_mul, Nat.one_mul] at h'
    exact h'
  have hEndO : ∀ i, i ≤ m → supportCutoff S (rs i * S.C.R) ≤ tAwakeEnd := fun i hi =>
    le_trans (supportCutoff_mono S (hle i m hi le_rfl)) hSeq.last
  have hEndP : ∀ i, i ≤ m → supportCutoff S (rs i * S.C.R) ≤ supportCutoff S (rs m * S.C.R) :=
    fun i hi => supportCutoff_mono S (hle i m hi le_rfl)
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
  have hnc : ∀ i, i ≤ m → ¬ RootCollisionAtProposal S Sched x (rs i * S.C.R) (Bf i) :=
    fun i hi h => hNoCol ((GoldilocksCorrectness.Proofs.View.rootCollisionAtOpening_unfold x rs m).2
      ⟨i, hi, Bf i, hBf i hi, h⟩)
  have hheld : ∀ i (hi : i ≤ m), (Bf i).slot = rs i * S.C.R ∧
      Bf i ∈ (stateBefore x (slotStart S (rs i * S.C.R) + 1) (S.P.proposer (rs i * S.C.R))).S.T :=
    fun i hi => opening_proposal_held S Sched x tGAT tAwakeEnd m i rs (Bf i) hDiv hMono hSeq hi
      hNoCol (hBf i hi)
  have hTC : ∀ i, TreeClosed S.P S.X (stateBefore x (slotStart S (rs i * S.C.R) + 1)
      (S.P.proposer (rs i * S.C.R))).S := fun i =>
    (lem11_node_invariant S Sched x (stepBefore x (slotStart S (rs i * S.C.R) + 1)) _).1.2.2.1
  -- C4 at the openings `j`, `j + 1`, `j + 2`
  have hC4 : ∀ i, j ≤ i → i + 1 ≤ m →
      (Bf i).AncestorEq (Bf (i + 1)) ∧
      (chainStateOf S.C (Bf i)).h + 1 ≤ (chainStateOf S.C (Bf (i + 1))).h ∧
      ((chainStateOf S.C (Bf (i + 1)).parent).h = (chainStateOf S.C (Bf i)).h →
        (chainStateOf S.C (Bf (i + 1))).J = (chainStateOf S.C (Bf i)).T_h) ∧
      ∀ u ∈ Hon S Sched (rs i * S.C.R),
        (stateBefore x (supportCutoff S (rs i * S.C.R + 1) + 1) u).A.saved_confirmation
          (rs i * S.C.R) = some (Bf i) := by
    intro i hji him
    rcases opening_rises_after_fast_block_opening S Sched x GST tGAT tAwakeEnd r H₂ (rs i * S.C.R)
        (rs (i + 1) * S.C.R) v L (Bf i) (Bf (i + 1)) A' hDiv hMono hSync hCatch hSyncF hCatchF
        (hRoots.mono (hEndP (i + 1) him)) hParent hOwner hU hGST hThird hAwake hCommittees
        hAnchor hOld hv hL hUpdate
        hFast (le_trans hsj (hle j i hji (by omega))) (Dvd.intro_left _ rfl) (hss i (by omega))
        (hEndO (i + 1) him) (hSeq.honest i (by omega)) (hSeq.honest (i + 1) him)
        (hBf i (by omega)) (hBf (i + 1) him) with h | h
    · exact absurd h (hnc i (by omega))
    · exact h
  obtain ⟨h01, h01h, -, -⟩ := hC4 j le_rfl (by omega)
  obtain ⟨h12, h12h, h12J, -⟩ := hC4 (j + 1) (by omega) (by omega)
  rw [show j + 1 + 1 = j + 2 from rfl] at h12 h12h h12J
  have h0 := (lem47_chain_state_heights S.C (Bf j) (Bf j)).1.1
  -- C5 at the openings `j + 1` and `j + 2`
  have hT1 := chainStateOf_T_h_spec S.C (Bf (j + 1))
  have hB0T : (Bf j).AncestorEq (chainStateOf S.C (Bf (j + 1))).T_h := by
    rcases ancestorEq_compatible hT1.1 h01 with h | h
    · exfalso
      have := chainStateOf_height_mono S.C h
      rw [hT1.2] at this
      unfold Height at *
      omega
    · exact h
  have hB0ne : Bf j ≠ (chainStateOf S.C (Bf (j + 1))).T_h := by
    intro h
    have h' := hT1.2
    rw [← h] at h'
    unfold Height at *
    omega
  have hTmem : (chainStateOf S.C (Bf (j + 1))).T_h ∈ (stateBefore x
      (slotStart S (rs (j + 1) * S.C.R) + 1) (S.P.proposer (rs (j + 1) * S.C.R))).S.T :=
    ancestors_mem_T_of_exec S Sched x _ _ _ _ (hheld (j + 1) (by omega)).2 hT1.1
  have hslotT := slot_lt_of_ancestorEq_of_treeClosed (hTC (j + 1)) hTmem hB0T hB0ne
  rw [(hheld j (by omega)).1] at hslotT
  have hsp := hSeq.spacing j hj2
  have hJ2 : (chainStateOf S.C (Bf (j + 1))).h ≤ (chainStateOf S.C (Bf (j + 2))).h_j := by
    refine round_justified_of_spacing3 S.C (Bf (j + 1)) (Bf (j + 2)) h12 h12h ?_ ?_ ?_
    · rw [(hheld (j + 2) hj2).1]
      unfold Slot at *
      omega
    · intro Y hY hne
      exact slot_lt_of_ancestorEq_of_treeClosed (hTC (j + 2)) (hheld (j + 2) hj2).2 hY hne
    · intro hpar
      have hJ := h12J hpar
      refine ⟨?_, hJ⟩
      have hspec := chainStateOf_J_spec S.C (Bf (j + 2))
      by_cases hz : (chainStateOf S.C (Bf (j + 2))).h_j = 0
      · exfalso
        have hg := hspec.2.1 hz
        rw [hJ] at hg
        have h' := hT1.2
        rw [hg] at h'
        have hg1 : (chainStateOf S.C (Block.genesis : Block V)).h = 1 := chainStateOf_genesis_h S.C
        rw [hg1] at h'
        unfold Height at *
        omega
      · have h' := hspec.2.2 (Nat.one_le_iff_ne_zero.mpr hz)
        rw [hJ, hT1.2] at h'
        exact h'.symm
  -- the base facts at the healed round `s₀ := s_j`
  have hs₀ := hsj
  have hsj1 := hss j (by omega)
  have hEnd₀ : supportCutoff S (rs j * S.C.R + 2) ≤ tAwakeEnd :=
    le_trans (supportCutoff_mono S (by omega)) (hEndO (j + 1) (by omega))
  have hp₀ := hSeq.honest j (by omega)
  have hBase := round_base_after_fast_block_opening S Sched x GST tGAT tAwakeEnd r H₂ (rs j * S.C.R)
    v L (Bf j) A' hDiv hMono hSync hCatch
    (hRoots.mono (le_trans (supportCutoff_mono S (by omega)) (hEndP (j + 1) (by omega)))) hParent
    hOwner hU hGST hThird hAwake hCommittees hAnchor hOld hv hL hUpdate hFast hs₀
    (Dvd.intro_left _ rfl) hEnd₀ hp₀
    (hBf j (by omega))
  obtain ⟨μA, hμA, hAsrc⟩ := P.anchor_source (show r * S.C.R + S.C.k + 2 ≤ rs j * S.C.R by omega)
    (hEndP j (by omega)) hp₀
  have hGs1 : LineInv S Sched x r H₂ (rs j * S.C.R - 1) :=
    P.lineInv_all _ (by
      rw [show rs j * S.C.R - 1 + 1 = rs j * S.C.R by omega]
      exact hEndP j (by omega))
  obtain ⟨hHCE, hSaved, hslot₀, -⟩ := healed_round_base_of_prev_votes S Sched x GST tGAT tAwakeEnd
    (rs j * S.C.R) (Bf j) hDiv hMono hSync hCatch
    (hRoots.mono (le_trans (supportCutoff_mono S (by omega)) (hEndP (j + 1) (by omega)))) hParent
    hOwner hU hGST hThird hAwake hCommittees (by omega)
    (le_trans hAnchor (slotStart_mono S (by omega)))
    (le_trans hAnchor (slotStart_mono S (by omega))) hEnd₀ hp₀ (hBf j (by omega)) hBase (hnc j (by omega))
    (fun u hu vote hvote => (hGs1 μA _ hAsrc (by omega)).1 u (Finset.mem_inter.1 hu).2 vote hvote)
  -- the old attestations
  have hOA := P.old_attestations_at_opening (show r * S.C.R + S.C.k + 2 ≤ rs j * S.C.R by omega)
    (Dvd.intro_left _ rfl) (le_trans (supportCutoff_mono S (by omega)) (hEndP (j + 1) (by omega)))
    hp₀
    (hBf j (by omega))
  -- `B₀`'s height is greater than `H₂`
  have hHB₀ : H₂ < (chainStateOf S.C (Bf j)).h := by
    obtain ⟨-, hPB⟩ := proposal_slot_parent S Sched x (show 1 ≤ rs j * S.C.R by omega)
      (hBf j (by omega))
    have hLP := P.parent_extends_sources (show r * S.C.R + S.C.k + 2 ≤ rs j * S.C.R by omega)
      (hEndP j (by omega)) hp₀ (hBf j (by omega)) (r * S.C.R) L
      (P.source_L (le_trans (supportCutoff_mono S (by omega)) (hEndP j (by omega)))) (by omega)
    have h1 := chainStateOf_height_mono S.C (ancestorEq_trans hLP hPB)
    rw [hL] at h1
    unfold Height at *
    omega
  -- the frames
  have hFrames := frames_at_phase_slots S Sched x GST tGAT tAwakeEnd r H₂ (rs j * S.C.R)
    (rs m * S.C.R) v L A' hDiv hMono hSync hCatch hRoots hParent hOwner hU hGST hThird hAwake
    hCommittees hAnchor hOld hv hL hUpdate hFast hs₀ hSeq.last
  -- the step at the vote time of the last opening's slot, and the caches
  obtain ⟨i₁, hi₁⟩ := exists_handover_step S Sched x (rs m * S.C.R) hDiv
  have hm2 := hle (j + 2) m hj2 le_rfl
  have hsm1 : rs j * S.C.R + 1 ≤ rs m * S.C.R := by
    have := hle (j + 1) m (by omega) le_rfl
    omega
  have htGAT : tGAT ≤ slotStart S (rs (j + 2) * S.C.R) := by
    have h1 := hSeq.first
    have h2 := slotStart_mono S (hle 0 (j + 2) (by omega) hj2)
    omega
  have hCaches := caches_at_handover_of_held S Sched x GST tGAT tAwakeEnd (rs j * S.C.R)
    (chainStateOf S.C (Bf j)).h (rs (j + 2) * S.C.R) (rs m * S.C.R) i₁ (Bf (j + 2)) hDiv
    hMono hSync hCatch (hRoots.mono (by
      rw [hi₁]
      have := voteTime_eq S (rs m * S.C.R)
      have := supportCutoff_eq S (rs m * S.C.R)
      omega)) hParent hU hGST hThird hAwake hm2 htGAT hSeq.last
    (hSeq.honest (j + 2) hj2) (hheld (j + 2) hj2).2
    (fun u hu => P.F_before_vote_ancestor_proposal
      (show r * S.C.R + S.C.k + 2 ≤ rs (j + 2) * S.C.R by
        have := hle j (j + 2) (by omega) hj2
        omega)
      (hEndP (j + 2) hj2) (hSeq.honest (j + 2) hj2) (hBf (j + 2) hj2) hu)
    (by unfold Height at *; omega)
    (by
      intro w D T h hD hJc hh
      have hti : x[i₁].time ≤ tAwakeEnd := by
        rw [hi₁]
        have := hSeq.last
        have := voteTime_eq S (rs m * S.C.R)
        have := supportCutoff_eq S (rs m * S.C.R)
        omega
      have hPc : ProgressCertOn D h T := by
        obtain ⟨A, hA, hAv⟩ := hJc
        exact ⟨A, hA, fun u hu => by
          obtain ⟨a, h1, h2, h3, -, h5⟩ := hAv u hu
          exact ⟨a, h1, h2, h3, h5⟩⟩
      exact cert_entry_at_slot S Sched x (rs j * S.C.R) (chainStateOf S.C (Bf j)).h i₁ w D T h
        hDiv hMono hU (fewerThanQuorum_of_fewerThanThird Sched _
          (adversaryFewerThanThirdUntil_of_le (by exact_mod_cast hti) hThird)) hOA hD hPc hh)
    hi₁
  exact ⟨j, rs j * S.C.R, i₁, Bf j, by omega, rfl, hi₁, hHCE, hSaved, hslot₀, hOA,
    fun s h1 h2 w hw => hFrames s h1 h2 w hw, hCaches⟩

end GoldilocksCorrectness.Proofs.Executions
