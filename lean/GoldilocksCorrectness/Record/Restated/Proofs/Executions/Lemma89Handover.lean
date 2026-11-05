module
public import GoldilocksCorrectness.Record.Restated.Proofs.View.Bridges
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89HealedRound
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89rTargets
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89Climb5
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.FinalityLivenessKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOfCertified
public import GoldilocksCorrectness.Proofs.View.Bridges
public import GoldilocksCorrectness.Proofs.Executions.Lemma89HealedRound
public import GoldilocksCorrectness.Proofs.Executions.Lemma89rTargets
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Climb5
public import GoldilocksCorrectness.Proofs.Executions.FinalityLivenessKit
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOfCertified
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89Handover, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89Handover.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: part C of Lemma 89 on the
fast-confirmation route, namely the hand-over step, an honest round opening slot's proposal from its
window, the honest attestations from the fast block's round on (entries of line sources, and targets
at heights greater than `H₂`), the member sets, the frame clauses at the slots of the phase,
consecutive honest round opening slots after the fast block rising, a block held early in a later
tree, the justification cache, the finalized blocks and the old attestations at an honest round
opening slot, the caches at the hand-over step, and the hand-over itself. The page's routine-level
theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  proposalWindowStart anchorCW)
open GoldilocksCorrectness.Proofs.Routines (delivery_of_round dutyWindowStart_le_voteTime one_le_Δ
  round_slot_le_of_lt slotStart_mono slot_mono slot_mono_int supportCutoff_eq supportCutoff_lt
  supportCutoff_mono times_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (block_admissible_of mem_T_receive_block
  slot_lt_of_ancestorEq_of_treeClosed)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Proofs.Executions (quorum_le_of_phase_set r_lt_of_lt_of_mono)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

open GoldilocksCorrectness.Record.Statements.Routines (JustificationCertOn ProgressCertOn
  RecordConsistent TreeClosed)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject fgObject
  healFrontSlots)
open GoldilocksCorrectness.Statements.Routines (expireLocks RootsNameBlocksIn)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_compatible
  ancestorEq_antisymm compatible_iff compatible_of_ancestorEq_compatible ancestorEq_of_parent?
  ancestorEq_node_iff state_transition_cases)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## C5 -/

/-- **C9, every honest round opening slot has a proposal (a copy for the slots from `2` on).** The proof; the
audited statement is in `Statements/Executions/Lemma89Statements.lean`. Why: the proposer is active
through its own window from the proposal window's start of slot `s` to its tick to the slot's start
, so that tick proposes (`honest_proposer_proposesJ`).

The variables:
- `M`: the model; `F`: its facts.

Read aloud: an honest proposer awake through its proposal window proposes. -/
theorem opening_proposal_exists_of_window (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (tGAT tAwakeEnd s : ℕ)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hs2 : 2 ≤ s)
    (hp : S.P.proposer s ∈ A.activeThroughoutToTick x (proposal_window_start S.C s) (M.slotStart S.C s)) :
    ∃ B : Block V, ProposalAt M S x s B := by
  obtain ⟨q, rfl⟩ : ∃ q, s = q + 2 := ⟨s - 2, by omega⟩
  obtain ⟨i, B, hl, hsent⟩ := (honest_proposer_proposesJ M F U) S A x R q E hp
  exact ⟨B, i, hl, hsent⟩

/-! ## The honest attestations after the fast block's round are targets -/

namespace PartAHyps
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {n' : M.N}

/-- **An honest attestation from the fast block's round on names a line source's entry.** An
attestation `a` that `u`, awake and outside the adversary set at `t`, put on the wire at the tick of
step `i` at a time `t` from the action time of round `r` to `tAwakeEnd`, was sent at the action
time of a round `r' ≥ r`, and names, at its height, the root of an entry block `E` that is a line
source of slot `r' * R`: `E` is the `T_h` of the fast block of `u`'s update then
(`fast_source_of_attestation`), a line source by `source_later`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: an attestation an honest awake validator sends at a time from the action time of round
`r` to the phase's end is sent at the action time of a round `r' ≥ r`, and names, at its height, the
root of an entry block that is a line source of slot `r' * R`. -/
theorem attestation_entry (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {i t : ℕ}
    {u : V} {a : Attestation V} (hl : x.lbl i = Event.tick u t) (ht : aR M S r ≤ t)
    -- when `t` is the action time of round `r'`, the support cutoff of slot `r' * R + 2` is in the phase
    (htE : ∀ r' : ℕ, t = aR M S r' → M.supportCutoff S.C (r' * S.C.R + 2) ≤ tAwakeEnd)
    (hHon : u ∉ A.corruptedAtTime x t)
    (hSent : (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i) :
    ∃ (r' : ℕ) (E : Block V), r ≤ r' ∧ t = aR M S r' ∧
      LineSource M S A x r H₂ (r' * S.C.R) E ∧ IsEntry M S.C E ∧
      (M.chainStateOf S.C E).h = a.h ∧ a.T = E.root := by
  obtain ⟨r', rfl⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.attest_time_round M F U) S A x R E hl hSent
  have hR := S.C.R_ge_two
  have hrr : r ≤ r' := by
    by_contra h
    have hlt : r' * S.C.R < r * S.C.R := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_lt M.toSlotLayout F.sched) S (show r' * S.C.R + 1 < r * S.C.R + 1 by omega)
    unfold aR at ht
    omega
  have hE2 := htE r' rfl
  have hEnd1 : M.supportCutoff S.C (r' * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ _)) hE2
  obtain ⟨A₀, X, hU, hXf, -, hXh, hXT⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Executions.fast_source_of_attestation M F U) S A x R E r' u a ⟨i, hl, hSent⟩
  have hsrc := P.source_later_of_tick_in_phase M F R U Fx hrr hHon hU hXf hEnd1 (fun k hk => by
    rw [E.tick_unique k i u _ hk hl]
    exact (time_le_of_tick_supportCutoff M F U) E hSkew (μ := r' * S.C.R) hE2 hl)
  refine ⟨r', (M.chainStateOf S.C X).T_h, hrr, rfl,
    hsrc.anc M F ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_T_h_spec M F) S.C X).1, ?_, ?_, hXT.symm⟩
  · unfold IsEntry
    exact (GoldilocksCorrectness.Record.Proofs.Executions.chainStateOf_T_h_T_h M F) S.C X
  · rw [((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_T_h_spec M F) S.C X).2, hXh]

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
at one height are one block.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: an attestation an honest awake validator sends at a time up to the phase's end, at a
height greater than `H₂`, is a target. -/
theorem attestation_target (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {i t : ℕ}
    {u : V} {a : Attestation V} (hl : x.lbl i = Event.tick u t)
    -- when `t` is the action time of round `r'`, the support cutoff of slot `r' * R + 2` is in the phase
    (htE : ∀ r' : ℕ, t = aR M S r' → M.supportCutoff S.C (r' * S.C.R + 2) ≤ tAwakeEnd)
    (hHon : u ∉ A.corruptedAtTime x t)
    -- `u` is honest at the action time of round `r` (item 3's `hOld` reads the senders honest then)
    (hHonR : u ∉ A.corruptedAtTime x (aR M S r))
    (hSent : (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i)
    (hH : H₂ < a.h) : a.τ = false := by
  induction i using Nat.strong_induction_on generalizing t a with
  | _ i ih =>
  obtain ⟨r₁, rfl⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.attest_time_round M F U) S A x R E hl hSent
  have hR := S.C.R_ge_two
  have hui : u ∉ A.corrupted i := E.not_mem_corrupted_of_tick hl
  -- `t` is at least the action time of round `r` (`hOld` bounds the earlier heights by `H₂`)
  have ht : aR M S r ≤ aR M S r₁ := by
    by_contra hlt
    have := P.hOld i _ u a hl (by exact_mod_cast (not_le.1 hlt)) hHonR hSent
    unfold Height at *
    omega
  by_contra hτ
  have hτ' : a.τ = true := by simpa using hτ
  obtain ⟨-, n₁, sent, hrun, ha⟩ := (tick_send_of_honestSendAt M F R E) hl hSent
  -- the tick's input state satisfies the node invariant
  have hTIi : x.tickInput u (aR M S r₁) = x.st i u := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput u (aR M S r₁)) := by
    rw [hTIi]
    exact (lem11_node_invariant M F S A x R E i u hui).1
  obtain ⟨-, -, source, head, -, -, hca, -⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem49_tick_attests F) S.C S.P S.X _ n₁ _ sent a hrun hInvT ha
  obtain ⟨hah, haT, hcase⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.create_attestation_timeout M F) _ _ _ _ _ _ _ a hca hτ'
  rw [hTIi] at hcase
  simp only [GoldilocksModel.N.sentTimeout, GoldilocksModel.N.sentTarget] at hcase
  have hΛ : RecordConsistent M (x.st i u) :=
    (GoldilocksCorrectness.Record.Statements.Executions.recordConsistent_of_exec M F) S A x R E i u
  -- the action times of two rounds are ordered as the rounds
  have hround : ∀ r₂ r₃ : ℕ, aR M S r₂ ≤ aR M S r₃ → r₂ ≤ r₃ := by
    intro r₂ r₃ hle
    by_contra hc
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_lt M.toSlotLayout F.sched) S
      (show r₃ * S.C.R + 1 < r₂ * S.C.R + 1 by
        have : r₃ * S.C.R < r₂ * S.C.R := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
        omega)
    unfold aR at hle
    omega
  -- an earlier send of `u`, at its tick to `t'` at a step `j < i`: `t' ≤ aR M S r₁`, the support cutoff after it in
  -- the phase, `u` honest at `t'`
  have hprev : ∀ j t' : ℕ, j < i → x.lbl j = Event.tick u t' →
      t' ≤ aR M S r₁ ∧ (∀ r'' : ℕ, t' = aR M S r'' → M.supportCutoff S.C (r'' * S.C.R + 2) ≤ tAwakeEnd) ∧
      u ∉ A.corruptedAtTime x t' := by
    intro j t' hj hl'
    have htt : t' ≤ aR M S r₁ := E.clock_mono j i u t' _ hj hui (Or.inl hl') (Or.inl hl)
    refine ⟨htt, fun r'' hr'' => ?_, (not_mem_corruptedAtTime_of_le M) x R E htt hHon⟩
    have hrr : r'' ≤ r₁ := hround r'' r₁ (hr'' ▸ htt)
    exact le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show r'' * S.C.R + 2 ≤ r₁ * S.C.R + 2 by have := Nat.mul_le_mul_right S.C.R hrr; omega)) (htE r₁ rfl)
  rcases hcase with htimeout | ⟨T', htarget, hne⟩
  · obtain ⟨c, hc, hch, hcτ⟩ := (hΛ.timeoutRec _).1 htimeout
    obtain ⟨j, t', a', hj, hl', -, hsent', -, hcont, -⟩ :=
      (GoldilocksCorrectness.Record.Proofs.Executions.record_content_sent_step M F) S A x R E u i c hc
    obtain ⟨-, hEnd', hHon'⟩ := hprev j t' hj hl'
    have hh' : a'.h = a.h := by
      rw [hah, ← hch]; exact congrArg AttestationContent.h hcont
    have hτa' : a'.τ = true := by
      rw [← hcτ]; exact congrArg AttestationContent.τ hcont
    have := ih j hj hl' hEnd' hHon' hsent' (by rw [hh']; exact hH)
    rw [hτa'] at this
    cases this
  · obtain ⟨c, hc, hch, hcτ, hcT⟩ := (hΛ.targetRec _ _).1 htarget
    obtain ⟨j, t', a', hj, hl', -, hsent', -, hcont, -⟩ :=
      (GoldilocksCorrectness.Record.Proofs.Executions.record_content_sent_step M F) S A x R E u i c hc
    obtain ⟨htt, hEnd', hHon'⟩ := hprev j t' hj hl'
    have hh' : a'.h = a.h := by
      rw [hah, ← hch]; exact congrArg AttestationContent.h hcont
    have hT' : a'.T = T' := by
      rw [← hcT]; exact congrArg AttestationContent.T hcont
    have ht' : aR M S r ≤ t' := by
      by_contra hlt
      have := P.hOld j t' u a' hl' (by exact_mod_cast (not_le.1 hlt)) hHonR hsent'
      unfold Height at *
      omega
    obtain ⟨r₁', Eb, -, ht₁, hE, hEe, hEh, hEr⟩ :=
      P.attestation_entry M F R E hNet hSkew hRedeliver Sy hΔs U Fx hl ht htE hHon hSent
    obtain ⟨r₂, E', -, ht₂, hE', hEe', hEh', hEr'⟩ :=
      P.attestation_entry M F R E hNet hSkew hRedeliver Sy hΔs U Fx hl' ht' hEnd' hHon' hsent'
    -- the two sources are compatible: both of slots at most `r₁' * R`, the support cutoff of slot `r₁' * R + 2` in the phase
    have hr₂ : r₂ * S.C.R ≤ r₁' * S.C.R := Nat.mul_le_mul_right _ (hround r₂ r₁' (by rw [← ht₂, ← ht₁]; exact htt))
    have hEnd₁ := htE r₁' ht₁
    have hcomp := P.sources_compatible M F R U (σ := r₁' * S.C.R)
      (fun σ' h' => P.lineInv_all M F R E hNet hSkew hRedeliver Sy hΔs U Fx σ'
        (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))
          hEnd₁)) hEnd₁ hE hE' le_rfl hr₂
    have hEE : Eb = E' := by
      have hheq : (M.chainStateOf S.C Eb).h = (M.chainStateOf S.C E').h := by rw [hEh, hEh', hh']
      rcases (compatible_iff Eb E').1 hcomp with h | h
      · have := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Eb E').2.2.2.2 h hheq
        unfold IsEntry at hEe hEe'
        rw [hEe, hEe'] at this
        exact this
      · have := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C E' Eb).2.2.2.2 h hheq.symm
        unfold IsEntry at hEe hEe'
        rw [hEe, hEe'] at this
        exact this.symm
    apply hne
    rw [← hT', hEr', ← hEE, ← hEr, haT]

end PartAHyps

/-! ## Small facts -/

/-- A proposal of slot `s ≥ 1` has the slot `s`, and its parent is an ancestor of it
(`proposal_parent_walk_end`).

The variables:
- `M`: the model; `F`: its facts.

Read aloud: a proposal of slot `s ≥ 1` has the slot `s`, and its parent is an ancestor of it. -/
theorem proposal_slot_parent (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {s : ℕ} {B : Block V} (hs : 1 ≤ s)
    (hB : ProposalAt M S x s B) : B.slot = s ∧ B.parent.AncestorEq B := by
  obtain ⟨s₀, rfl⟩ : ∃ s₀, s = s₀ + 1 := ⟨s - 1, by omega⟩
  obtain ⟨i, hl, hsent⟩ := hB
  obtain ⟨h1, -, h3, -⟩ := (proposal_parent_walk_end M F U) S A x R E s₀ i B _ hl hsent
  exact ⟨h1, ancestorEq_of_parent? h3⟩

/-- The member sets shrink: a member of slot `σ + 1` is a member of slot `σ`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: every member of `Hon S Sched (σ + 1)` is a member of `Hon S Sched σ`. -/
theorem hon_succ_subset (S : Setup V) (A : Activity V) {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (σ : ℕ) : Hon M S A x (σ + 1) ⊆ Hon M S A x σ := by
  intro u hu
  unfold Hon roundMembers at hu ⊢
  obtain ⟨-, hu'⟩ := Finset.mem_sdiff.1 hu
  exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, (not_mem_corruptedAtTime_of_le M) x R E ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show σ + 1 ≤ σ + 1 + 1 by omega)) hu'⟩

omit [RootOrder] in
/-- A validator outside the adversary set at the support cutoff of slot `σ + 1` is a member of
`Hon M S Sched σ`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: a validator outside the adversary set at the support cutoff of slot `σ + 1` is a member
of `Hon S Sched σ`. -/
theorem mem_hon_of_honest (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) {σ : ℕ} {u : V}
    (hu : u ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 1))) : u ∈ Hon M S A x σ := by
  unfold Hon roundMembers
  exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hu⟩

omit [RootOrder] in
/-- A member of `Hon M S Sched σ` is outside the adversary set at the support cutoff of slot
`σ + 1`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: a member of `Hon S Sched σ` is outside the adversary set at the support cutoff of slot
`σ + 1`. -/
theorem honest_of_mem_hon (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) {σ : ℕ} {u : V}
    (hu : u ∈ Hon M S A x σ) : u ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 1)) := by
  unfold Hon roundMembers at hu
  exact (Finset.mem_sdiff.1 hu).2

/-! ## C7, the frames at the slots of the phase -/

/-! ## The voter frame at the voter's tick (the kit of `voterFrame_at_last_opening` and C7) -/

namespace PartAHyps
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {n' : M.N}

/-- **A block on an updater's confirmation is a line source.** `source_conf` with its member premise
`u ∈ Hon M S A x σ` replaced by the updater premise `u ∈ updaterAt M S A x σ` its proof reads (`memberU` turns the
first into the second): a block on the confirmation an updater of a slot `σ ≥ r * R + k` saved at its tick to the
support cutoff of slot `σ + 1` is a line source of slot `σ`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: a block on an updater's confirmation of a slot `k` or more past the round's first is a line source of
that slot. -/
theorem source_conf_of_updater (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout)
    {σ : ℕ} {u : V}
    {C X : Block V} (hσ : r * S.C.R + S.C.k ≤ σ) (huU : u ∈ updaterAt M S A x σ)
    (hC : (x.tickOutput u (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C)
    (hXC : X.AncestorEq C) : LineSource M S A x r H₂ σ X := by
  obtain ⟨n₀, sent, hrun, hAw, hS⟩ := (update_of_saved_confirmation_of_updater M F U) S A x R σ u C E
    huU hC
  exact ⟨u, huU, n₀, C, C, (confirmationUpdated_of_cutoff_tickInput M F U) x R σ u n₀ sent hrun hAw, hS, hC,
    hXC, ancestorEq_refl C, Or.inr (Or.inr hσ)⟩

/-- **`F_compat_vf` at a step.** Under `F_compat_vf`'s hypotheses, at a step `j` in the phase at which `w` is outside
the adversary set and whose real time is less than the earliest real time of a tick to the support cutoff of slot
`σ + 2` (that cutoff less `ΔClockAhead`), `w`'s finalized block at `j` is compatible with every line source `X` of a
slot at most `σ`. The body is `F_compat_vf`'s, read at `j`: a certificate `w`'s finalized block carries comes from an
update at a tick before `j`, so of a slot at most `σ`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `j`: the step.
- `hEndA`: every tick to the action time of a round whose first slot is at most `σ` is in the phase.

Read aloud: at a step before any tick to the support cutoff of slot `σ + 2`, an honest validator's finalized block is
compatible with every line source of a slot at most `σ`. -/
theorem F_compat_vf_st (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ j : ℕ} {w : V}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd) (hjE : x.time j ≤ tAwakeEnd)
    (hEndA : ∀ r'' : ℕ, r'' * S.C.R ≤ σ → ∀ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r'') →
      x.time k ≤ tAwakeEnd)
    (hw' : w ∉ A.corrupted j)
    (hjc : x.time j < ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) - ΔClockAhead) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ) :
    (x.st j w).finalized.compatible X = true := by
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd1
  obtain ⟨D, hD, hFD⟩ :=
    (GoldilocksCorrectness.Record.Statements.Executions.finalizedFromChain_of_exec M F) S A x R E
      j w
  rw [hFD]
  by_cases hle : (M.chainStateOf S.C D).h_F ≤ H₂
  · -- `v` held `L` at its tick to the action time of round `r` (`L_held_v`), honest there, in the phase
    have hv' : v ∉ A.corrupted (x.tickStep v (aR M S r)) := E.not_mem_corrupted_of_tick P.hk₀
    have hT : A.AdversaryFewerThanThirdUntil x (validator_count V)
        (max (x.time j) (x.time (x.tickStep v (aR M S r)))) :=
      P.hThird.mono (max_le hjE P.hEndStep)
    have hLv : L ∈ (x.st (x.tickStep v (aR M S r)) v).tree := (P.L_held_v M F R E U hEndR).2
    have hFL := (GoldilocksCorrectness.Record.Proofs.Executions.lem68_honest_past_finalized M F Fx) S A x R E P.hRoots j
      (x.tickStep v (aR M S r)) w v D L hT hw' hv' hD hLv
      (by rw [P.hL]; exact Nat.lt_succ_of_le hle) (max_le hjE P.hEndStep)
    -- `L` is a line source of slot `r * R`: two slots compared by `sources_compatible_lt`, one slot (a round's
    -- first slot, `hEndA` at `r`) by `sources_compatible_eq`
    have hLX : L.compatible X = true := by
      rcases Nat.lt_or_eq_of_le (hX.slot_ge M F) with h | h
      · exact PartAHyps.sources_compatible_lt M F hG (P.source_L M F R U hEndR) hX h hμ
      · subst h
        exact P.sources_compatible_eq M F R U (hEndA r hσ) (P.source_L M F R U hEndR) hX
    exact compatible_of_ancestorEq_compatible hFL hLX
  · have hlt : H₂ < (M.chainStateOf S.C D).h_F := Nat.lt_of_not_le hle
    obtain ⟨hJC, -, hFanc, -⟩ :=
      ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).2.2
        (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
    have hFT : (M.chainStateOf S.C D).F ∈ (x.st j w).tree :=
      (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w D _ hD hFanc
    obtain ⟨r', Eb, u, kc, hkc, hkcj, -, hE, -, -, hEr, -⟩ :=
      P.cert_source_fast_round M F R E U Fx hjE hD
        ((GoldilocksCorrectness.Record.Proofs.Executions.progressCertOn_of_justificationCertOn M F) hJC) hlt
    have hFE : (M.chainStateOf S.C D).F = Eb :=
      P.hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := j) (v := w) hw' hjE hFT)
        ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_mono M) x
          (le_trans ((time_mono M) x R hkcj.le) hjE) (P.source_inHonestTreeBy_tick M F R E U hE hkc)) hEr
    rw [hFE]
    -- the update of slot `r' * R` ran at a tick before `j`, so `r' * R ≤ σ`: a tick to the support cutoff of slot
    -- `σ + 2` or later is at a real time at least that cutoff minus `ΔClockAhead`, later than `j` (`hjc`)
    have hμ'σ : r' * S.C.R ≤ σ := by
      by_contra h
      have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (show σ + 2 ≤ r' * S.C.R + 1 by omega)
      have hle2 : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (r' * S.C.R + 1) : ℕ) : ℝ) := by
        exact_mod_cast hmono
      have hkt := (E.tick_active _ _ _ hkc).2.1
      have hkk := (time_mono M) x R hkcj.le
      linarith
    rcases lt_trichotomy (r' * S.C.R) μ with h | h | h
    · exact PartAHyps.sources_compatible_lt M F hG hE hX h hμ
    · subst h
      exact P.sources_compatible_eq M F R U (hEndA r' hμ) hE hX
    · exact GoldilocksCorrectness.Proofs.Routines.compatible_symm' (PartAHyps.sources_compatible_lt M F hG hX hE h hμ'σ)

/-- **`root_compat_vf_of_L` at a step.** Under its hypotheses, at a step `j` in the phase at which `w` is outside the
adversary set and whose real time is less than the earliest real time of a tick to the support cutoff of slot `σ + 2`
(that cutoff less `ΔClockAhead`), when `w` holds `L` at `j` at a greatest chain-state height at least `H₂ + 1`, the root
of `w`'s fork choice at `j` is compatible with every line source `X` of a slot at most `σ`. The body is
`root_compat_vf_of_L`'s, read at `j` (`F_compat_vf_st` for the finalized block).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `j`: the step.
- `hEndA`: every tick to the action time of a round whose first slot is at most `σ` is in the phase.
- `hLT`, `hM`: `w` holds `L` at `j`, at a greatest chain-state height at least `H₂ + 1`.

Read aloud: at a step before any tick to the support cutoff of slot `σ + 2`, when an honest validator holds `L` at a
greatest chain-state height at least `H₂ + 1`, its fork-choice root is compatible with every line source of a slot at
most `σ`. -/
theorem root_compat_vf_of_L_st (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ j : ℕ} {w : V}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd) (hjE : x.time j ≤ tAwakeEnd)
    (hEndA : ∀ r'' : ℕ, r'' * S.C.R ≤ σ → ∀ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r'') →
      x.time k ≤ tAwakeEnd)
    (hw' : w ∉ A.corrupted j)
    (hjc : x.time j < ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) - ΔClockAhead) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    (hLT : L ∈ (x.st j w).tree) (hM : H₂ + 1 ≤ hMax M S.C (x.st j w)) :
    (M.get_fc_root (x.st j w)).compatible X = true := by
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd1
  have hwj : w ∉ A.corrupted j := hw'
  have hInv : M.nodeInv S.C S.P S.X (x.st j w) :=
    ((GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariant M F S A x R E
      j w) hwj).1
  by_cases hR : M.get_fc_root (x.st j w) = (x.st j w).finalized
  · rw [hR]
    exact P.F_compat_vf_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd1 hjE hEndA hw' hjc hX hμ
  have key : hMax M S.C (x.st j w) = (x.st j w).justifiedHeight + 1 ∧
      M.get_fc_root (x.st j w) = (x.st j w).justified := by
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X (x.st j w) hInv
      with ⟨hJ, hm, -⟩ | ⟨hF, -⟩
    · exact ⟨hm, hJ⟩
    · exact absurd hF hR
  obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_exec M F) S A x R E j w
  rw [key.2]
  by_cases hlt : H₂ < (x.st j w).justifiedHeight
  · rw [hhjD] at hlt
    obtain ⟨hJC, hJanc, -⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F)
      S.C D).1 (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
    have hD' : D ∈ (x.st j w).tree := hD
    have hJT : (M.chainStateOf S.C D).J ∈ (x.st j w).tree :=
      (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w D _ hD' hJanc
    obtain ⟨r', Eb, u, kc, hkc, hkcj, -, hE, -, -, hEr, -⟩ :=
      P.cert_source_fast_round M F R E U Fx hjE hD'
        ((GoldilocksCorrectness.Record.Proofs.Executions.progressCertOn_of_justificationCertOn M F) hJC) hlt
    have hJE : (M.chainStateOf S.C D).J = Eb :=
      P.hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := j) (v := w) hwj hjE hJT)
        ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_mono M) x
          (le_trans ((time_mono M) x R hkcj.le) hjE) (P.source_inHonestTreeBy_tick M F R E U hE hkc)) hEr
    rw [hJD, hJE]
    -- the update of slot `r' * R` ran at a tick before `j`, so `r' * R ≤ σ` (`hjc`), as in `F_compat_vf_st`
    have hμ'σ : r' * S.C.R ≤ σ := by
      by_contra h
      have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (show σ + 2 ≤ r' * S.C.R + 1 by omega)
      have hle2 : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (r' * S.C.R + 1) : ℕ) : ℝ) := by
        exact_mod_cast hmono
      have hkt := (E.tick_active _ _ _ hkc).2.1
      have hkk := (time_mono M) x R hkcj.le
      linarith
    rcases lt_trichotomy (r' * S.C.R) μ with h | h | h
    · exact PartAHyps.sources_compatible_lt M F hG hE hX h hμ
    · subst h
      exact P.sources_compatible_eq M F R U (hEndA r' hμ) hE hX
    · exact GoldilocksCorrectness.Proofs.Routines.compatible_symm' (PartAHyps.sources_compatible_lt M F hG hX hE h hμ'σ)
  · have hhj : (x.st j w).justifiedHeight = H₂ := by
      have := key.1
      have h1 : (x.st j w).justifiedHeight ≤ H₂ := Nat.le_of_not_lt hlt
      unfold Height at *
      omega
    -- `L` is a line source of slot `r * R`, compared with `X` as in `F_compat_vf_st`
    have hLX : L.compatible X = true := by
      rcases Nat.lt_or_eq_of_le (hX.slot_ge M F) with h | h
      · exact PartAHyps.sources_compatible_lt M F hG (P.source_L M F R U hEndR) hX h hμ
      · subst h
        exact P.sources_compatible_eq M F R U (hEndA r hσ) (P.source_L M F R U hEndR) hX
    by_cases h0 : (M.chainStateOf S.C D).h_j = 0
    · have hg := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).2.1 h0
      rw [hJD, hg]
      exact (compatible_iff _ _).2 (Or.inl (GoldilocksCorrectness.Proofs.Routines.genesis_ancestorEq X))
    · have hJh := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).2.2 (Nat.one_le_iff_ne_zero.2 h0)
      have hFJ : (x.st j w).finalized.AncestorEq (x.st j w).justified := by
        have := (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E j w
        rw [key.2] at this
        exact this
      -- the finalized block is an ancestor of `L`: at a finalization height at most `H₂` by Lemma 89a; at a
      -- greater one it is a line source taller than the justified block, its descendant, which cannot be
      have hFL : (x.st j w).finalized.AncestorEq L := by
        obtain ⟨DF, hDF, hFDF⟩ :=
          (GoldilocksCorrectness.Record.Statements.Executions.finalizedFromChain_of_exec M F) S A x R E
            j w
        have hFDF' : (x.st j w).finalized = (M.chainStateOf S.C DF).F := hFDF
        rw [hFDF']
        by_cases hle : (M.chainStateOf S.C DF).h_F ≤ H₂
        · have hv' : v ∉ A.corrupted (x.tickStep v (aR M S r)) := E.not_mem_corrupted_of_tick P.hk₀
          have hT : A.AdversaryFewerThanThirdUntil x (validator_count V)
              (max (x.time j) (x.time (x.tickStep v (aR M S r)))) :=
            P.hThird.mono (max_le hjE P.hEndStep)
          have hLv : L ∈ (x.st (x.tickStep v (aR M S r)) v).tree := (P.L_held_v M F R E U hEndR).2
          exact (GoldilocksCorrectness.Record.Proofs.Executions.lem68_honest_past_finalized M F Fx) S A x R E P.hRoots
            j (x.tickStep v (aR M S r)) w v DF L hT hwj hv' hDF hLv
            (by rw [P.hL]; exact Nat.lt_succ_of_le hle) (max_le hjE P.hEndStep)
        · exfalso
          have hlt2 : H₂ < (M.chainStateOf S.C DF).h_F := Nat.lt_of_not_le hle
          obtain ⟨hFC, -, hFanc, -⟩ :=
            ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C DF).2.2
              (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt2))
          have hFT : (M.chainStateOf S.C DF).F ∈ (x.st j w).tree :=
            (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w DF _ hDF hFanc
          obtain ⟨μ₂, Eb₂, u₂, kc₂, hkc₂, hkcj₂, -, hE₂, -, hEh₂, hEr₂⟩ :=
            P.cert_source M F R E U Fx hjE hDF
              ((GoldilocksCorrectness.Record.Proofs.Executions.progressCertOn_of_justificationCertOn M F) hFC) hlt2
          have hFE : (M.chainStateOf S.C DF).F = Eb₂ :=
            P.hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := j) (v := w) hwj hjE hFT)
              ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_mono M) x
                (le_trans ((time_mono M) x R hkcj₂.le) hjE) (P.source_inHonestTreeBy_tick M F R E U hE₂ hkc₂)) hEr₂
          rw [hFDF', hFE, hJD] at hFJ
          have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C hFJ
          rw [hEh₂, hJh, ← hhjD, hhj] at h1
          unfold Height at *
          omega
      have hRL := (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_ancestorEq_of_tall M F) S.C S.P S.X
        (x.st j w) hInv L hLT hFL (by rw [P.hL, key.1, hhj])
      rw [key.2] at hRL
      exact compatible_of_ancestorEq_compatible hRL hLX

/-- **`root_compat_vf` at a step.** From the start of slot `r * R + 1` on, at a step `j` in the phase at which `w` is
outside the adversary set and whose real time is less than the earliest real time of a tick to the support cutoff of
slot `σ + 2` (that cutoff less `ΔClockAhead`), when the invariant holds at every slot up to `σ`, the root of `w`'s fork
choice at `j` is compatible with every line source of a slot at most `σ`. The body is `root_compat_vf`'s, read at `j`
(`L_tall_st`, then `root_compat_vf_of_L_st`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `j`: the step.
- `hEndA`: every tick to the action time of a round whose first slot is at most `σ` is in the phase.

Read aloud: at a step from the start of slot `r * R + 1` and before any tick to the support cutoff of slot `σ + 2`, an
honest validator's fork-choice root is compatible with every line source of a slot at most `σ`. -/
theorem root_compat_vf_st (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ j : ℕ} {w : V}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd) (hjE : x.time j ≤ tAwakeEnd)
    (hEndA : ∀ r'' : ℕ, r'' * S.C.R ≤ σ → ∀ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r'') →
      x.time k ≤ tAwakeEnd)
    (hj0 : ((M.slotStart S.C (r * S.C.R + 1) : ℕ) : ℝ) ≤ x.time j) (hw' : w ∉ A.corrupted j)
    (hjc : x.time j < ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) - ΔClockAhead) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ) :
    (M.get_fc_root (x.st j w)).compatible X = true := by
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd1
  obtain ⟨hLT, hM⟩ := P.L_tall_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hEndR hj0 hjE hw'
  exact P.root_compat_vf_of_L_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd1 hjE hEndA hw' hjc hX hμ hLT hM

/-- **`viable_candidate_vf_of_held` at a step.** At a step `j` in the phase at which `w` is outside the adversary set
and whose real time is less than the earliest real time of a tick to the support cutoff of slot `σ + 2` (that cutoff
less `ΔClockAhead`), when the line sources on `X`'s chain and `L` are in a node state `nH`'s tree, some block `W` of
`nH`'s tree, `X` or a descendant of `X`, has a chain-state height at least `w`'s `head_height_floor` at `j`. The body
is `viable_candidate_vf_of_held`'s, read at `j` (`tall_entry_round_st`): every line source read here comes from a tick
before `j`, so of a slot at most `σ`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `j`: the step.
- `hEndA`: every tick to the action time of a round whose first slot is at most `σ` is in the phase.
- `nH`: the node state in which the sources are held; `hheld`, `hLH`: the held sources and `L`.

Read aloud: at a step before any tick to the support cutoff of slot `σ + 2`, when the line sources on a line source's
chain and `L` are in a node state's tree, some block of that tree, that source or a descendant of it, is viable for the
validator at that step. -/
theorem viable_candidate_vf_of_held_st (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    {Δs : ℕ} (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ j : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd) (hjE : x.time j ≤ tAwakeEnd)
    (hEndA : ∀ r'' : ℕ, r'' * S.C.R ≤ σ → ∀ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r'') →
      x.time k ≤ tAwakeEnd)
    (hw' : w ∉ A.corrupted j)
    (hjc : x.time j < ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) - ΔClockAhead) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    {nH : M.N}
    (hheld : ∀ {μ₁ : ℕ} {X₁ : Block V}, LineSource M S A x r H₂ μ₁ X₁ → μ₁ ≤ σ →
      X.AncestorEq X₁ → X₁ ∈ nH.tree)
    (hLH : L ∈ nH.tree) :
    ∃ W : Block V, X.AncestorEq W ∧ W ∈ nH.tree ∧
      M.head_height_floor (x.st j w) ≤ (M.chainStateOf S.C W).h := by
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd1
  have hwj : w ∉ A.corrupted j := hw'
  have hInv : M.nodeInv S.C S.P S.X (x.st j w) :=
    ((GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariant M F S A x R E
      j w) hwj).1
  -- a slot whose update ran at a tick before `j` is at most `σ`: a tick to the support cutoff of slot `σ + 2` or
  -- later is at a real time at least that cutoff minus `ΔClockAhead`, later than `j` (`hjc`)
  have hslot : ∀ (μ' : ℕ) (u : V) (k : ℕ), x.lbl k = Event.tick u (M.supportCutoff S.C (μ' + 1)) →
      k < j → μ' ≤ σ := by
    intro μ' u k hk hkj
    by_contra h
    have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show σ + 2 ≤ μ' + 1 by omega)
    have hkt := (E.tick_active _ _ _ hk).2.1
    have hkk := (time_mono M) x R hkj.le
    have h4 : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (μ' + 1) : ℕ) : ℝ) := by
      exact_mod_cast hmono
    linarith
  -- two line sources, one at a round's first slot `r₁ * R ≤ σ`, compared on their slots
  have hcmp : ∀ {r₁ μ₂ : ℕ} {X₁ X₂ : Block V}, LineSource M S A x r H₂ (r₁ * S.C.R) X₁ →
      LineSource M S A x r H₂ μ₂ X₂ → r₁ * S.C.R ≤ σ → μ₂ ≤ σ → X₁.compatible X₂ = true := by
    intro r₁ μ₂ X₁ X₂ h₁ h₂ hr₁ hμ₂
    rcases lt_trichotomy (r₁ * S.C.R) μ₂ with h | h | h
    · exact PartAHyps.sources_compatible_lt M F hG h₁ h₂ h hμ₂
    · rw [← h] at h₂
      exact P.sources_compatible_eq M F R U (hEndA r₁ hr₁) h₁ h₂
    · exact GoldilocksCorrectness.Proofs.Routines.compatible_symm' (PartAHyps.sources_compatible_lt M F hG h₂ h₁ h hr₁)
  have hXh := hheld hX hμ (ancestorEq_refl X)
  by_cases hMle : hMax M S.C (x.st j w) ≤ H₂ + 1
  · have hfl := (GoldilocksCorrectness.Record.Proofs.Routines.floor_le_h_max M F) S.C S.P S.X (x.st j w) hInv
    rcases (compatible_iff _ _).1 (hcmp (r₁ := r) (P.source_L M F R U hEndR) hX hσ hμ)
      with h | h
    · refine ⟨X, ancestorEq_refl X, hXh, ?_⟩
      have := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C h
      rw [P.hL] at this
      unfold Height at *
      omega
    · refine ⟨L, h, hLH, ?_⟩
      rw [P.hL]
      unfold Height at *
      omega
  · have hM2 : H₂ + 2 ≤ hMax M S.C (x.st j w) := by unfold Height at *; omega
    obtain ⟨-, ⟨Y, hY, hYh⟩, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_exec M F) S A x R E j w
    obtain ⟨r', Eb, -, ⟨u', k', hk', hkj', -⟩, hE, hEe, hEh, hEY⟩ :=
      P.tall_entry_round_st M F R E U Fx hjE hw' hY (by rw [hYh]; exact hM2)
    have hμ' : r' * S.C.R ≤ σ := hslot (r' * S.C.R) u' k' hk' hkj'
    rw [hYh] at hEh
    -- the state is not contested
    have hnc : M.fg_contest (x.st j w) = false := by
      cases hcs : M.fg_contest (x.st j w)
      · rfl
      exfalso
      obtain ⟨hbox, B, hBT, -, hBh, hJB⟩ :=
        (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_spec M F) S.C S.P S.X (x.st j w) hInv hcs
      obtain ⟨rB, EB, -, ⟨uB, kB, hkB, hkjB, -⟩, hEB, hEBe, hEBh, hEBB⟩ :=
        P.tall_entry_round_st M F R E U Fx hjE hw' hBT (by rw [hBh]; exact hM2)
      have hμB : rB * S.C.R ≤ σ := hslot (rB * S.C.R) uB kB hkB hkjB
      obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_exec M F) S A x R E j w
      have hlt : H₂ < (M.chainStateOf S.C D).h_j := by
        rw [← hhjD]
        unfold Height at *
        omega
      obtain ⟨hJC, hJanc, hJh⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F)
        S.C D).1 (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
      have hD' : D ∈ (x.st j w).tree := hD
      have hJT : (M.chainStateOf S.C D).J ∈ (x.st j w).tree :=
        (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w D _ hD' hJanc
      obtain ⟨rJ, EJ, uJ, kJ, -, hkJ, hkjJ, -, hEJ, hEJe, hEJh, hEJr⟩ := P.cert_source_round M F R E U Fx hjE hD'
        ((GoldilocksCorrectness.Record.Proofs.Executions.progressCertOn_of_justificationCertOn M F) hJC) hlt
      have hμJ : rJ * S.C.R ≤ σ := hslot (rJ * S.C.R) uJ kJ hkJ hkjJ
      have hJE : (M.chainStateOf S.C D).J = EJ :=
        P.hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := j) (v := w) hwj hjE hJT)
          ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_mono M) x
            (le_trans ((time_mono M) x R hkjJ.le) hjE) (P.source_inHonestTreeBy_tick M F R E U hEJ hkJ)) hEJr
      have hEE : EJ = EB := (GoldilocksCorrectness.Record.Proofs.Routines.entry_eq_of_compatible M F) S.C hEJe hEBe (by
          rw [hEJh, hEBh, ← hhjD, hBh, hbox]
          unfold Height at *
          omega)
        (hcmp hEJ hEB hμJ hμB)
      apply hJB
      rw [hJD, hJE, hEE]
      exact hEBB
    have hfloor : M.head_height_floor (x.st j w) = hMax M S.C (x.st j w) - 1 :=
      (GoldilocksCorrectness.Record.Proofs.Routines.head_height_floor_of_not_contested M F) S.C S.P S.X
        (x.st j w) hInv hnc
    rcases (compatible_iff _ _).1 (GoldilocksCorrectness.Proofs.Routines.compatible_symm' (hcmp hE hX hμ' hμ)) with h | h
    · exact ⟨Eb, h, hheld hE hμ' h, by rw [hfloor, hEh]⟩
    · refine ⟨X, ancestorEq_refl X, hXh, ?_⟩
      have := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C h
      rw [hfloor, ← hEh]
      exact this

/-- **`viable_candidate_vf` at a step.** At a step `j` in the phase at which `w` is outside the adversary set, at
least one delay after the view freeze of slot `σ` and before the earliest real time of a tick to the support cutoff of
slot `σ + 2` (that cutoff less `ΔClockAhead`), when the invariant holds at every slot up to `σ` and `w`'s root at `j` is
a line source `X` of a slot at most `σ` or an ancestor of it, some block `W`, `X` or a descendant of `X`, held by `w` at
its tick to the view freeze of slot `σ`, has a chain-state height at least `w`'s `head_height_floor` at `j`. The body
is `viable_candidate_st`'s with `viable_candidate_vf_of_held_st` in place of `viable_candidate_of_held_st`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `j`: the step.
- `hEndA`: every tick to the action time of a round whose first slot is at most `σ` is in the phase.

Read aloud: at a step between the view freeze of slot `σ` and the first tick to the support cutoff of slot `σ + 2`,
when an honest validator's root is a line source `X` or an ancestor of it, some block `W`, `X` or a descendant of `X`,
held at its tick to the view freeze of slot `σ`, has a chain-state height at least the validator's
`head_height_floor`. -/
theorem viable_candidate_vf_st (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ j : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd) (hjE : x.time j ≤ tAwakeEnd)
    (hEndA : ∀ r'' : ℕ, r'' * S.C.R ≤ σ → ∀ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r'') →
      x.time k ≤ tAwakeEnd)
    (hw' : w ∉ A.corrupted j)
    (hjv : ((M.viewFreeze S.C σ : ℕ) : ℝ) + Δ S ≤ x.time j)
    (hjc : x.time j < ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) - ΔClockAhead) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    (hRX : (M.get_fc_root (x.st j w)).AncestorEq X) :
    ∃ W : Block V, X.AncestorEq W ∧ W ∈ (x.tickInput w (M.viewFreeze S.C σ)).tree ∧
      M.head_height_floor (x.st j w) ≤ (M.chainStateOf S.C W).h := by
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd1
  have hA0 := P.E.ahead_nonneg
  have hB0 := P.E.behind_nonneg
  have hsk := P.hSkew
  -- `w` ticks to the view freeze of every slot `μ₁` from `r * R` to `σ` before `j`
  have htick : ∀ μ₁ : ℕ, r * S.C.R ≤ μ₁ → μ₁ ≤ σ →
      ∃ k : ℕ, x.lbl k = Event.tick w (M.viewFreeze S.C μ₁) ∧ k ≤ j := by
    intro μ₁ h1 h2
    obtain ⟨hv₁, -, hf₁, hs₁, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S μ₁
    obtain ⟨-, -, hfσ, hsσ, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
    obtain ⟨hG1, -, -⟩ := P.gstSync M F U h1
    have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S h2
    have hvv : ((M.viewFreeze S.C μ₁ : ℕ) : ℝ) ≤ ((M.viewFreeze S.C σ : ℕ) : ℝ) := by
      exact_mod_cast (show M.viewFreeze S.C μ₁ ≤ M.viewFreeze S.C σ by omega)
    obtain ⟨k, hk, hkj⟩ := P.tick_before_st M F (c := M.viewFreeze S.C μ₁) (by omega) (by linarith) hjE hw'
    exact ⟨k, hk, hkj.le⟩
  obtain ⟨kσ, hkσ, hkσt⟩ := htick σ hσ le_rfl
  have hkσR : x.tickStep w (M.viewFreeze S.C σ) = kσ := (tickStep_eq_of_lbl M) x P.E hkσ
  have hTIσ : x.tickInput w (M.viewFreeze S.C σ) = x.st kσ w := by
    show x.st (x.tickStep w (M.viewFreeze S.C σ)) w = x.st kσ w; rw [hkσR]
  -- a tree read at `w`'s tick to the view freeze of a slot `μ₁ ≤ σ` grows to its tick to the one of `σ`
  have hgrow : ∀ μ₁ : ℕ, μ₁ ≤ σ → ∀ k₁ : ℕ, x.lbl k₁ = Event.tick w (M.viewFreeze S.C μ₁) →
      ∀ B : Block V, B ∈ (x.st k₁ w).tree → B ∈ (x.st kσ w).tree := by
    intro μ₁ h2 k₁ hk₁ B hB
    refine (mem_T_mono M F) x R P.E w ?_ hB
    rcases Nat.lt_or_eq_of_le h2 with hlt | heq
    · obtain ⟨-, -, hf₁, hs₁, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S μ₁
      have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
        (show μ₁ + 1 ≤ σ by omega)
      obtain ⟨-, -, hfσ, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
      have h1 := (P.E.tick_active _ w _ hk₁).2.2
      have h2' := (P.E.tick_active _ w _ hkσ).2.1
      have h4 : ((M.viewFreeze S.C μ₁ : ℕ) : ℝ) + Δ S ≤ ((M.viewFreeze S.C σ : ℕ) : ℝ) := by
        exact_mod_cast (show M.viewFreeze S.C μ₁ + Δ S ≤ M.viewFreeze S.C σ by omega)
      exact ((lt_of_time_lt M) x R (by linarith)).le
    · subst heq
      exact (P.E.tick_unique _ _ w _ hk₁ hkσ).le
  -- `w`'s finalized block at a step up to `j` is an ancestor of `X`
  have hFX : ∀ k₁ : ℕ, k₁ ≤ j → (x.st k₁ w).finalized.AncestorEq X := fun k₁ hk₁ =>
    ancestorEq_trans ((F_ancestorEq_of_le M F) x R P.E w hk₁)
      (ancestorEq_trans ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R P.E j w) hRX)
  -- a line source of a slot at most `σ` on `X`'s chain is held at `w`'s tick to the view freeze of `σ`
  have hheld : ∀ {μ₁ : ℕ} {X₁ : Block V}, LineSource M S A x r H₂ μ₁ X₁ → μ₁ ≤ σ →
      X.AncestorEq X₁ → X₁ ∈ (x.tickInput w (M.viewFreeze S.C σ)).tree := by
    intro μ₁ X₁ hX₁ hμ₁ hXX₁
    obtain ⟨k₁, hk₁, hk₁t⟩ := htick μ₁ (hX₁.slot_ge M F) hμ₁
    have hk₁R : x.tickStep w (M.viewFreeze S.C μ₁) = k₁ := (tickStep_eq_of_lbl M) x P.E hk₁
    have hTI₁ : x.tickInput w (M.viewFreeze S.C μ₁) = x.st k₁ w := by
      show x.st (x.tickStep w (M.viewFreeze S.C μ₁)) w = x.st k₁ w; rw [hk₁R]
    have hE₁ : M.supportCutoff S.C (μ₁ + 1) ≤ tAwakeEnd :=
      le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd1
    have h := P.source_held M F R E hNet hSkew hRedeliver Sy hΔs U hX₁ hE₁ hk₁ (by
      rw [hTI₁]
      exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans (hFX k₁ hk₁t) hXX₁)))
    rw [hTI₁] at h
    rw [hTIσ]
    exact hgrow μ₁ hμ₁ k₁ hk₁ X₁ h
  have hLH : L ∈ (x.tickInput w (M.viewFreeze S.C σ)).tree := by
    obtain ⟨kL, hkL, -⟩ := htick (r * S.C.R) le_rfl hσ
    have hkLR : x.tickStep w (M.viewFreeze S.C (r * S.C.R)) = kL := (tickStep_eq_of_lbl M) x P.E hkL
    have h := P.L_held M F R E hNet hSkew hRedeliver Sy hΔs U Fx hEndR hkL
    rw [show x.tickInput w (M.viewFreeze S.C (r * S.C.R)) = x.st kL w by
      show x.st (x.tickStep w (M.viewFreeze S.C (r * S.C.R))) w = x.st kL w; rw [hkLR]] at h
    rw [hTIσ]
    exact hgrow (r * S.C.R) hσ kL hkL L h
  exact P.viable_candidate_vf_of_held_st M F R E hSkew U Fx hG hσ hEnd1 hjE hEndA hw' hjc hX hμ hheld hLH

/-- **The voter half of the frame conditions at the voter's tick, with the end at slot `σ + 1`.** `voterFrame_source_vf`
read at `w`'s tick `k` to the vote time of slot `σ + 1` in place of the state before that time: when the invariant
holds at every slot up to `σ`, for every line source `X` of a slot at most `σ`, the root of `w`'s fork choice on the
state its tick `k` starts from is compatible with `X`, and, when that root is `X` or an ancestor of `X`, some block of
`w`'s voter tree of slot `σ + 1` that is `X` or a descendant of `X` is a viable head.

Why: `w` is outside the adversary set at its tick `k`, whose real time is within `ΔClockAhead` before and
`ΔClockBehind` after the vote time of slot `σ + 1`, so less than its support cutoff, at most `tAwakeEnd`, and more than
`ΔClockAhead` before the support cutoff of slot `σ + 2` (`hSkew`). The root by `root_compat_vf_st` at `k`; the viable
head by `viable_candidate_vf_st` at `k` and `proposal_viable_head_at_tick_st` at `k`, as `stepFrame_vote_source`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `k`: `w`'s tick to
  the vote time of slot `σ + 1`.
- `hEndA`: every tick to the action time of a round whose first slot is at most `σ` is in the phase.

Read aloud: with the phase running at least to the support cutoff of slot `σ + 1` and the line invariant at every slot
up to `σ`, the frame conditions of `w`'s vote of slot `σ + 1`, read at its tick, hold relative to every line source of a
slot at most `σ`. -/
theorem voterFrame_source_vf_st (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd)
    (hEndA : ∀ r'' : ℕ, r'' * S.C.R ≤ σ → ∀ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r'') →
      x.time k ≤ tAwakeEnd)
    {k : ℕ} (hk : x.lbl k = Event.tick w (M.voteTime S.C (σ + 1))) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ) :
    (M.fg_to_ac (x.st k w)).fc_root.compatible X = true ∧
    ((M.fg_to_ac (x.st k w)).fc_root.AncestorEq X →
      ∃ W, VoterTreeAt M (x.st k w) (S.C.t_ ((σ + 1) - 1) + 3 * S.C.Δ) (σ + 1) W ∧
          W ∈ (M.fg_to_ac (x.st k w)).viable_heads ∧
        X.AncestorEq W) := by
  obtain ⟨hvσ, -, hfσ, hsσ, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
  obtain ⟨hvσ1, hcσ1, -, hsσ1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  obtain ⟨hv2, hcσ2, -, hs2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
  have hv1c5 : M.voteTime S.C (σ + 1) + 5 * Δ S = M.supportCutoff S.C (σ + 2) := by
    rw [show σ + 2 = σ + 1 + 1 by omega] at hcσ2 hs2 hv2 ⊢
    omega
  have hv1c1 : M.voteTime S.C (σ + 1) + Δ S = M.supportCutoff S.C (σ + 1) := by omega
  -- `w` is honest at its tick `k`, whose real time is within the clock bounds of the vote time
  have hwk : w ∉ A.corrupted k := P.E.not_mem_corrupted_of_tick hk
  have hk1 := (P.E.tick_active _ w _ hk).2.1
  have hk2 := (P.E.tick_active _ w _ hk).2.2
  have hA0 := P.E.ahead_nonneg
  have hB0 := P.E.behind_nonneg
  have hsk := P.hSkew
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have h5 : ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) + 5 * Δ S = ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) := by
    exact_mod_cast hv1c5
  have h1 : ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) + Δ S = ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) := by
    exact_mod_cast hv1c1
  have hER : ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) ≤ ((tAwakeEnd : ℕ) : ℝ) := by exact_mod_cast hEnd1
  have hkE : x.time k ≤ tAwakeEnd := by linarith
  have hkc : x.time k < ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) - ΔClockAhead := by linarith
  have hfR : ((M.slotStart S.C (r * S.C.R + 1) : ℕ) : ℝ) ≤ x.time k := by
    have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (show r * S.C.R + 1 ≤ σ + 1 by omega)
    have h : ((M.slotStart S.C (r * S.C.R + 1) + Δ S : ℕ) : ℝ) ≤ ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.slotStart S.C (r * S.C.R + 1) + Δ S ≤ M.voteTime S.C (σ + 1) by omega)
    push_cast at h
    linarith
  refine ⟨by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
      exact P.root_compat_vf_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd1 hkE hEndA hfR hwk hkc hX hμ,
    fun hR => ?_⟩
  -- the viable head: `viable_candidate_vf_st` at `k`, then `proposal_viable_head_at_tick_st` at `k`
  have hR' : (M.get_fc_root (x.st k w)).AncestorEq X := by
    rw [← (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]; exact hR
  have hjv : ((M.viewFreeze S.C σ : ℕ) : ℝ) + Δ S ≤ x.time k := by
    have h : ((M.viewFreeze S.C σ + 2 * Δ S : ℕ) : ℝ) ≤ ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.viewFreeze S.C σ + 2 * Δ S ≤ M.voteTime S.C (σ + 1) by omega)
    push_cast at h
    linarith
  obtain ⟨W, hXW, hWT, hφ⟩ := P.viable_candidate_vf_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd1 hkE hEndA hwk hjv
    hkc hX hμ hR'
  obtain ⟨hG1, -, -⟩ := P.gstSync M F U hσ
  obtain ⟨kσ, hkσ, hkσk⟩ := P.tick_before_st M F (c := M.viewFreeze S.C σ) (by omega) hjv hkE hwk
  -- `w`'s clock is less than the view freeze of slot `σ` before its tick to it (it is active from `ΔClockAhead` before
  -- that view freeze, `clockValue_lt_of_tick_of_active`)
  have hcG : tGAT + Δ S ≤ M.viewFreeze S.C σ := by omega
  have hwkσ : w ∉ A.corrupted kσ := P.E.not_mem_corrupted_of_tick hkσ
  have hlt := (clockValue_lt_of_tick_of_active M F) P.E hkσ (by omega) (fun j hj hjk => by
    have hjt : x.time j ≤ x.time k := (time_mono M) x R (le_trans hjk hkσk.le)
    have hj1 : x.time j ≤ x.time (j + 1) := (time_mono M) x R (Nat.le_succ j)
    have hcGR : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.viewFreeze S.C σ : ℕ) : ℝ) := by exact_mod_cast hcG
    have hjc : w ∉ A.corrupted j := fun h => hwkσ (P.E.corrupted_mono j kσ hjk h)
    exact Activity.mem_active.2 ⟨P.hAwake j w (by linarith) (by linarith) hjc, hjc⟩)
  obtain ⟨hWt, hWv⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.proposal_viable_head_at_tick_st M F U) S A x R
    (M.viewFreeze S.C σ) (σ + 1) w W _ _ P.E kσ k hkσ hlt hkσk.le hwk hWT (by rw [Nat.add_sub_cancel]) ⟨rfl, rfl⟩
    (ancestorEq_trans hR' hXW) hφ
  exact ⟨W, (GoldilocksCorrectness.Record.Statements.Routines.mem_voter_block_tree_iff_at S.C _ (σ + 1) W).1
    hWt, hWv, hXW⟩

end PartAHyps

/-- **C7, Lemma 89's frame clauses from the line invariant.** The proof; the audited statement is
in `Statements/Executions/Lemma89Statements.lean`. The update of `v` at the action time is an
outcome `(n', sent)` of `v`'s tick there with `L` among the fast blocks of `n'` (template A2),
without A2's hypothesis that `v` has been awake since the duty window's start of slot `r * R + 1`:
`hAwake`, `hAnchor` and `hv` give it, as for `fast_block_base`'s twin. Why: a block on the honest
chain before `s` from `s₀` is on an updater's confirmation of a slot `s'` with `s₀ ≤ s' < s`; the
updater is a member of `Hon M s'`, so the block is a line source of slot `s'` (`source_conf`,
`s₀ ≥ r * R + k`); `stepFrame_source` at slot `s − 1` gives `StepFrameAt` relative to it at every
member of `Hon M s`, whose conjuncts are the two clauses.

Roots name blocks until `M.supportCutoff S.C s_m`: the bundle `PartAHyps` is built with its end time
`M.supportCutoff S.C s_m`, the latest time its kit reads here.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: after the healed round every member's frame follows the honest chain so far. -/
theorem frames_at_phase_slots (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ s₀ s_m : ℕ) (v : V)
      (L : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C s_m))
    -- roots name blocks up to the real time of every tick to a clock value at most the support cutoff of slot
    -- `s_m` ('s row)
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s_m →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hs₀ : r * S.C.R + S.C.k + 2 ≤ s₀) (hEnd : M.supportCutoff S.C s_m ≤ tAwakeEnd)
    -- every tick to a clock value at most the support cutoff of slot `s_m` is at a real time at most `tAwakeEnd`
    -- ('s row)
    (hEndTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s_m →
      x.time k ≤ tAwakeEnd) :
    ∀ s : ℕ, s₀ < s → s < s_m →
      (∀ w ∈ Hon M S A x s, VoterFrameOnChainAt M S A x s₀ s w) ∧
      (∀ v ∈ updaterAt M S A x s, UpdaterFinalizedOnChainAt M S A x s₀ s v) := by
  have hk2 := S.C.k_ge_two
  intro s hs1 hs2
  have hrs : r * S.C.R + 2 ≤ s_m := by omega
  -- the bundle with the phase's end at the support cutoff of slot `s_m`
  have P := (PartAHyps.of_tick M F U) (tAwakeEnd := M.supportCutoff S.C s_m) R E hNet hSkew hRedeliver Sy
    hΔs hRoots hParent hGST (hThird.mono (by exact_mod_cast hEnd))
    (fun i u hi => hAwake i u (le_trans hi (by exact_mod_cast hEnd)))
    (fun s h1 h2 => hActive s h1 (le_trans h2 hEnd)) (hCommittees.mono M hEnd) hAnchor hOld hv hUpdate hFast hL
    ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S hrs)
  obtain ⟨σ, rfl⟩ : ∃ σ, s = σ + 1 := ⟨s - 1, by omega⟩
  have hσ : r * S.C.R ≤ σ := by omega
  have hEnd1 : M.supportCutoff S.C (σ + 1) ≤ M.supportCutoff S.C s_m :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  have hEnd2 : M.supportCutoff S.C (σ + 2) ≤ M.supportCutoff S.C s_m :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  -- the line invariant at every slot up to `σ`, whose updates run at ticks before the support cutoff of slot `s_m`
  have hG := P.lineInv_upto M F R E hNet hSkew hRedeliver Sy hΔs U Fx hEnd2
  -- every tick to the action time of a round whose first slot is at most `σ` is before the support cutoff of slot
  -- `σ + 2`, inside the phase
  have hEndA : ∀ r'' : ℕ, r'' * S.C.R ≤ σ → ∀ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r'') →
      x.time k ≤ ((M.supportCutoff S.C s_m : ℕ) : ℝ) := fun r'' h u k hk =>
    (time_le_of_tick_supportCutoff M F U) P.E P.hSkew (μ := r'' * S.C.R)
      (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (show r'' * S.C.R + 2 ≤ σ + 2 by omega)) hEnd2) hk
  -- a block on the honest chain before slot `σ + 1` is a line source of a slot at most `σ`
  have hsrc : ∀ B : Block V, OnHonestChainBefore M S A x s₀ (σ + 1) B →
      ∃ μ, μ ≤ σ ∧ LineSource M S A x r H₂ μ B := by
    rintro B ⟨s', hs', hs₀', u, hu, C, hC, hBC⟩
    exact ⟨s', by omega, PartAHyps.source_conf_of_updater M F (H₂ := H₂) R E U
      (show r * S.C.R + S.C.k ≤ s' by omega) hu hC hBC⟩
  refine ⟨fun w _ B hB k hk => ?_, fun u hu B hB => ?_⟩
  · -- clause 1: the voter frame at `w`'s tick to the vote time of slot `σ + 1`
    obtain ⟨μ, hμ, hX⟩ := hsrc B hB
    exact P.voterFrame_source_vf_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd1 hEndA hk hX hμ
  · -- clause 2: the finalized block of `u`'s tick input to the support cutoff of slot `σ + 2`
    obtain ⟨μ, hμ, hX⟩ := hsrc B hB
    obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 hu
    have hks : x.tickStep u (M.supportCutoff S.C (σ + 1 + 1)) = k := (tickStep_eq_of_lbl M) x E hk
    show (x.st (x.tickStep u (M.supportCutoff S.C (σ + 1 + 1))) u).finalized.compatible B = true
    rw [hks]
    rcases Nat.lt_or_ge (σ + 2) s_m with hlt | hge
    · -- the tick is at a real time at most the support cutoff of slot `σ + 2` plus `ΔClockBehind`, inside the phase
      -- and earlier than any tick to the support cutoff of slot `σ + 3`
      have hkE : x.time k ≤ ((M.supportCutoff S.C s_m : ℕ) : ℝ) :=
        (time_le_of_tick_supportCutoff M F U) P.E P.hSkew (μ := σ + 1)
          ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
            (show σ + 1 + 2 ≤ s_m by omega)) hk
      have hjc : x.time k < ((M.supportCutoff S.C (σ + 3) : ℕ) : ℝ) - ΔClockAhead := by
        have hkt := (E.tick_active _ _ _ hk).2.2
        have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S (σ + 2)
        rw [show σ + 2 + 1 = σ + 3 from rfl] at h1
        have hΔ := one_le_Δ S
        rw [show σ + 1 + 1 = σ + 2 from rfl] at hkt
        have hc : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (σ + 3) : ℕ) : ℝ) := by
          exact_mod_cast (show M.supportCutoff S.C (σ + 2) + Δ S ≤ M.supportCutoff S.C (σ + 3) by omega)
        have hsk := hSkew
        have hA0 := E.ahead_nonneg
        linarith
      exact P.F_compat_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd2 hkE (E.not_mem_corrupted_of_tick hk) hjc
        hX hμ (fun _ => P.votes_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd2 hX hμ)
    · -- the slot `s_m - 1`: `u`'s tick to the support cutoff of slot `s_m` may be past the bundle's end; it is read
      -- through the rows `TickRows`, from `hRootsTick` and `hEndTick` and the phase's premises
      have hsm : σ + 2 = s_m := by omega
      have TR : TickRows M S A x tGAT (M.supportCutoff S.C s_m) tAwakeEnd (M.supportCutoff S.C s_m) :=
        ⟨hEnd, hThird, hAwake, hCommittees, hRootsTick, hEndTick⟩
      have hc₀ : M.supportCutoff S.C (σ + 1 + 1) ≤ M.supportCutoff S.C s_m := by rw [show σ + 1 + 1 = s_m by omega]
      have hjc : x.time k < ((M.supportCutoff S.C (σ + 3) : ℕ) : ℝ) - ΔClockAhead := by
        have hkt := (E.tick_active _ _ _ hk).2.2
        have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S (σ + 2)
        rw [show σ + 2 + 1 = σ + 3 from rfl] at h1
        have hΔ := one_le_Δ S
        rw [show σ + 1 + 1 = σ + 2 from rfl] at hkt
        have hc : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (σ + 3) : ℕ) : ℝ) := by
          exact_mod_cast (show M.supportCutoff S.C (σ + 2) + Δ S ≤ M.supportCutoff S.C (σ + 3) by omega)
        have hsk := hSkew
        have hA0 := E.ahead_nonneg
        linarith
      exact P.F_compat_st_past M F R E hNet hSkew hRedeliver Sy hΔs U Fx TR hG hσ hEnd2 (hEndTick k u _ hk hc₀)
        (hRootsTick k u _ hk hc₀) (E.not_mem_corrupted_of_tick hk) hjc hX hμ
        (fun _ => P.votes_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd2 hX hμ)

/-- **The proposer's reader start, before Lemma 12's read time of the slot before an honest round opening slot.** With
the anchor of the committee premise at or before the start of slot `r * R + 1` and `r * R + k + 2 ≤ s`, the clock
value `tGAT + Δ` plus both clock bounds is less than the support cutoff of slot `s − 1` less the larger of `2Δ` and
the sync delay `Δs`.

Why: the anchor is `tGAT + 4Δ(k + 2)`, slot `s − 1` starts at least `k` slots after slot `r * R + 1`, and the
attestations' sync bound `max Δ Δs + 3Δ + ΔClockAhead + ΔClockBehind < 4Δk` (C4's row `htStart` for
`lem89r_quiet_round_targets`, moved out of C4's body to keep that body within the elaboration budget).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `tGAT`: the phase's start; `r`: the fast block's round; `s`: the honest round opening slot.

Read aloud: the proposer's reader start is more than both clock bounds before the read time Lemma 12 uses for the
slot before the opening. -/
theorem tStart_lt_readTime_of_anchor (U : UniformSchedule M.toSlotLayout) (S : Setup V) {tGAT r s Δs : ℕ}
    {ΔClockAhead ΔClockBehind : ℝ} (hA0 : 0 ≤ ΔClockAhead) (hB0 : 0 ≤ ΔClockBehind)
    (hsk : ΔClockAhead + ΔClockBehind < Δ S)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1)) (hs : r * S.C.R + S.C.k + 2 ≤ s) :
    ((((tGAT + Δ S : ℕ) : ℤ)) : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) := by
  have hk2 := S.C.k_ge_two
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hA := hAnchor
  rw [GoldilocksCorrectness.Proofs.Routines.anchorCW_eq] at hA
  have hsm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
    (show r * S.C.R + 1 ≤ s - 1 by omega)
  obtain ⟨-, hcm1, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s - 1)
  have hcut : tGAT + 4 * Δ S * (S.C.k + 2) + 2 * Δ S ≤ M.supportCutoff S.C (s - 1) := by omega
  have hcutR : ((tGAT : ℕ) : ℝ) + 4 * (Δ S : ℝ) * ((S.C.k : ℝ) + 2) + 2 * Δ S ≤
      ((M.supportCutoff S.C (s - 1) : ℕ) : ℝ) := by exact_mod_cast hcut
  have hDk : (0 : ℝ) ≤ (Δ S : ℝ) * S.C.k := by positivity
  have hΔsR : (Δs : ℝ) ≤ (max (Δ S) Δs : ℝ) := by exact_mod_cast le_max_right (Δ S) Δs
  have hT0 : (0 : ℝ) ≤ (tGAT : ℝ) := by positivity
  have h1 : (tGAT : ℝ) + Δ S + ΔClockAhead + ΔClockBehind + 2 * Δ S <
      ((M.supportCutoff S.C (s - 1) : ℕ) : ℝ) := by nlinarith
  have h2 : (tGAT : ℝ) + Δ S + ΔClockAhead + ΔClockBehind + Δs <
      ((M.supportCutoff S.C (s - 1) : ℕ) : ℝ) := by nlinarith
  have hm : max (2 * Δ S) Δs ≤ M.supportCutoff S.C (s - 1) := by
    have : ((max (2 * Δ S) Δs : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (s - 1) : ℕ) : ℝ) := by
      push_cast
      exact max_le (by linarith) (by linarith)
    exact_mod_cast this
  rw [Nat.cast_sub hm]
  push_cast
  have := max_lt (show (2 * (Δ S : ℝ)) < (M.supportCutoff S.C (s - 1) : ℝ) - ((tGAT : ℝ) + Δ S) - ΔClockAhead -
    ΔClockBehind by linarith) (show (Δs : ℝ) < (M.supportCutoff S.C (s - 1) : ℝ) - ((tGAT : ℝ) + Δ S) - ΔClockAhead -
    ΔClockBehind by linarith)
  linarith

/-! ## C4, consecutive openings after the fast block rise -/

/-- **C4, consecutive openings after the fast block rise (copy with the round's first slot).** The
proof; the audited statement is in `Statements/Executions/Lemma89Statements.lean`. The update of `v`
at the action time is an outcome `(n', sent)` of `v`'s tick there with `L` among the fast blocks of
`n'` (template A2), without A2's hypothesis that `v` has been awake since the duty window's start of
slot `r * R + 1`: `hAwake`, `hAnchor` and `hv` give it, as for `fast_block_base`'s twin. Why: with
no root collision at `B`, `lem89r_quiet_round_targets` at the round of slot `s`, with the family of
the line sources of the slots `μ` with `μ + 2 ≤ s` (the line invariant at slot `s − 1` for the chain
invariant, `late_locks_on_sources` for the locks, `anchor_source` for the proposer's anchor,
`frame_source_at` and `frame_has_viable_head` for the proposer's viable heads), its quiet round from
`quiet_round_after_fast_block_opening`; its targets premise holds since `B`'s height is greater than
`H₂` (`B.parent` extends `L`, `parent_extends_sources`) and every honest attestation at such a
height from the fast block's round on is a target
(`(GoldilocksCorrectness.Record.Proofs.Executions.PartAHyps.attestation_target M F U Fx)`).

Roots name blocks until `M.supportCutoff S.C s''`: the bundle `PartAHyps` is built with its end time
`M.supportCutoff S.C s''`, the latest time its kit reads here; C2 reads up to the same time, Lemma
89r up to `M.supportCutoff S.C (s'' - 1)`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: after the fast block, every honest round opening slot's proposal is extended by the next one's, one
height higher, which carries its justification. -/
theorem opening_rises_after_fast_block_opening (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ s s'' : ℕ) (v : V)
    (L B B' : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- the members of slot `s`'s round are active through the attestations' sync delay after the later of the slot's
    -- duty window's start and `GST`, where Lemma 89r reads the attestations' sync fact
    (hHoldF : ∀ w ∈ Hon M S A x s, w ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ)
      (((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) + Δs_F))
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C s''))
    -- roots name blocks up to the real time of every tick to a clock value at most the support cutoff of slot
    -- `s''` (, stops_recheck_85)
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s'' →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hs : r * S.C.R + S.C.k + 2 ≤ s) (hsR : S.C.R ∣ s) (hs'' : s + S.C.R ≤ s'')
    (hEnd : M.supportCutoff S.C s'' ≤ tAwakeEnd)
    -- every tick to a clock value at most the support cutoff of slot `s''` is at a real time at most
    -- `tAwakeEnd` (, stops_recheck_85)
    (hEndTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s'' →
      x.time k ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C s))
    (hq : S.P.proposer s'' ∉ A.corruptedAtTime x (M.supportCutoff S.C s''))
    (hB : ProposalAt M S x s B) (hB' : ProposalAt M S x s'' B') :
    RootCollisionAtProposal M S A x s B ∨
    (B.AncestorEq B' ∧ (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∧
      ((M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h →
        (M.chainStateOf S.C B').J = (M.chainStateOf S.C B).T_h) ∧
      ∀ u ∈ Hon M S A x s,
        (x.tickOutput u (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B) := by
  by_cases hCol : RootCollisionAtProposal M S A x s B
  · exact Or.inl hCol
  right
  have hk2 := S.C.k_ge_two
  have hR2 := S.C.R_ge_two
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hsk := hSkew
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hcm : ∀ a b : ℕ, a ≤ b → M.supportCutoff S.C a ≤ M.supportCutoff S.C b := fun a b h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h
  have hs2 : s + 2 ≤ s'' := by omega
  -- the bundle with its end at the support cutoff of slot `s''` (as C2's)
  have P := (PartAHyps.of_tick M F U) (tAwakeEnd := M.supportCutoff S.C s'') R E hNet hSkew hRedeliver Sy
    hΔs hRoots hParent hGST (hThird.mono (by exact_mod_cast hEnd))
    (fun i u hi => hAwake i u (le_trans hi (by exact_mod_cast hEnd)))
    (fun s h1 h2 => hActive s h1 (le_trans h2 hEnd)) (hCommittees.mono M hEnd) hAnchor hOld hv hUpdate hFast hL
    (hcm _ _ (by omega))
  have hEndM : ∀ σ : ℕ, σ ≤ s'' → M.supportCutoff S.C σ ≤ M.supportCutoff S.C s'' := fun σ h => hcm _ _ h
  have hEndA : ∀ σ : ℕ, σ ≤ s'' → M.supportCutoff S.C σ ≤ tAwakeEnd := fun σ h => le_trans (hEndM σ h) hEnd
  -- the slot times (`4Δ` per slot: the start, the vote time `+ Δ`, the support cutoff `+ 2Δ`)
  obtain ⟨hvs, hcs, -, hss, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s
  obtain ⟨hvs1, hcs1, -, hss1, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s - 1)
  rw [show s - 1 + 1 = s by omega] at hss1
  have hcsucc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S (s + 1)
  rw [show s + 1 + 1 = s + 2 from rfl] at hcsucc
  have hc01 := hcm s (s + 1) (Nat.le_succ s)
  have hcs2 : M.supportCutoff S.C (s + 2) ≤ tAwakeEnd := hEndA _ hs2
  -- C2 (a gap, called under): the round is quiet relative to its own confirmations
  have hQuiet := (quiet_round_after_fast_block_opening M F U Fx) S A x R GST tGAT tAwakeEnd r H₂ s s'' v L B
    E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent hGST hThird hAwake hActive hCommittees hAnchor hOld hv
    hL n' sent hUpdate hFast hs hsR hs'' hEnd hEndTick hp hq hB hCol
  obtain ⟨rs₀, hrs⟩ : ∃ c : ℕ, s = c * S.C.R := by
    obtain ⟨c, hc⟩ := hsR
    exact ⟨c, by rw [hc, Nat.mul_comm]⟩
  have hG : ∀ σ', σ' ≤ s → LineInv M S A x r H₂ σ' :=
    P.lineInv_upto M F R E hNet hSkew hRedeliver Sy hΔs U Fx (hEndM _ hs2)
  -- the family: the line sources of the slots `μ` with `μ + 2 ≤ s`
  let 𝓒 : Block V → Prop := fun C => ∃ μ : ℕ, μ + 2 ≤ s ∧ LineSource M S A x r H₂ μ C
  have hChain : ChainInvFor M S A x (Hon M S A x (s - 1)) 𝓒 (s - 1) := by
    rintro C ⟨μ, hμ, hC⟩
    exact (hG (s - 1) (by omega) μ C hC (by omega)).1
  have hFamLocks : ∀ w ∈ Hon M S A x (s - 1), LiveLocksOnFamilyAt M S A x 𝓒 (s - 1) w := by
    intro w hw n₁ sent₁ hrun₁ hAw₁ e he hlive
    have hvE : M.voteTime S.C (s - 1 + 1) ≤ M.supportCutoff S.C s'' := by
      rw [show s - 1 + 1 = s by omega]
      exact le_trans (by omega) (hEndM s (by omega))
    obtain ⟨D, ⟨μ, hμ, hsrc⟩, heD⟩ := P.late_locks_on_sources M F R E U
      (show r * S.C.R + S.C.k ≤ s - 1 by omega) hvE hw n₁ sent₁ hrun₁ hAw₁ e he hlive
    exact ⟨D, ⟨μ, by omega, hsrc⟩, heD⟩
  obtain ⟨μA, hμA, hAsrc⟩ := P.anchor_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx
    (show r * S.C.R + S.C.k + 2 ≤ s by omega) (hEndM s (by omega)) hp
  -- the proposer's tick to the start of slot `s`
  obtain ⟨kp, hkp, -⟩ := P.tick_before M F (w := S.P.proposer s) (c := M.slotStart S.C s)
    (t := M.supportCutoff S.C s) (by
      have := (P.gstSync M F U (show r * S.C.R ≤ s by omega)).1
      omega) (by omega) (hEndM s (by omega)) hp
  have htip : x.tickInput (S.P.proposer s) (M.slotStart S.C s) = x.st kp (S.P.proposer s) := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hkp]
  have hkpT := (E.tick_active kp _ _ hkp).2.2
  have hkpA := (E.tick_active kp _ _ hkp).2.1
  have hpk : S.P.proposer s ∉ A.corrupted kp := E.not_mem_corrupted_of_tick hkp
  have hk₀ := P.hk₀
  have hk₀T := (E.tick_active _ _ _ hk₀).2.2
  have hgap : ((aR M S r : ℕ) : ℝ) + Δ S ≤ ((M.slotStart S.C s : ℕ) : ℝ) := by
    have := hcm (r * S.C.R + 1) (s - 1) (by omega)
    exact_mod_cast (show aR M S r + Δ S ≤ M.slotStart S.C s by
      show M.supportCutoff S.C (r * S.C.R + 1) + Δ S ≤ M.slotStart S.C s
      omega)
  have hk₀k : x.tickStep v (aR M S r) < kp := (lt_of_time_lt M) x R (by linarith)
  -- the proposer's root at its tick is on the chain of a line source's confirmation of a slot at most `s − 2`
  have hσ2 : r * S.C.R ≤ s - 2 := by omega
  have hG2 : ∀ σ', σ' ≤ s - 2 → LineInv M S A x r H₂ σ' := fun σ' h => hG σ' (by omega)
  have hEnd2 : M.supportCutoff S.C (s - 2 + 2) ≤ M.supportCutoff S.C s'' := hEndM _ (by omega)
  have hcR : ((M.supportCutoff S.C s : ℕ) : ℝ) = ((M.slotStart S.C s : ℕ) : ℝ) + 2 * Δ S := by
    rw [hcs]; push_cast; ring
  have hjt : x.time kp < ((M.supportCutoff S.C (s - 2 + 2) : ℕ) : ℝ) - ΔClockAhead := by
    rw [show s - 2 + 2 = s by omega, hcR]; linarith
  obtain ⟨r', -, ⟨u', k', hk', hk'j, -, -, C₀, hsv, hRC₀⟩, hrsrc⟩ :=
    P.root_source_st_attester M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG2 hσ2 hEnd2 hk₀k hjt hpk
  have hr' : r' * S.C.R + 2 ≤ s := by
    have h1 : ((M.supportCutoff S.C (r' * S.C.R + 1) : ℕ) : ℝ) - ΔClockAhead ≤ x.time k' :=
      (E.tick_active _ _ _ hk').2.1
    have h2 := (time_mono M) x R hk'j.le
    by_contra hn
    have hle := hcm s (r' * S.C.R + 1) (by omega)
    have hleR : ((M.supportCutoff S.C s : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (r' * S.C.R + 1) : ℕ) : ℝ) := by
      exact_mod_cast hle
    linarith
  -- a member of slot `s − 1` saved a confirmation every line source of a slot at most `s − 2` is an ancestor of
  have hnon : ∃ u, u ∈ Hon M S A x (s - 1) := by
    have h := P.committee M F (show r * S.C.R ≤ s - 1 by omega) (hEndM _ (by omega))
    obtain ⟨u, hu⟩ : (S.P.committee (s - 1) ∩ Hon M S A x (s - 1)).Nonempty := Finset.card_pos.1 (by omega)
    exact ⟨u, (Finset.mem_inter.1 hu).2⟩
  obtain ⟨u₁, hu₁⟩ := hnon
  have hu₁U := ((P.members_sets M F U (show r * S.C.R ≤ s - 1 by omega) (hEndM _ (by omega))).2) hu₁
  obtain ⟨C₁, hC₁⟩ := P.member_saves_confirmation M F R E hNet hSkew hRedeliver Sy hΔs U Fx
    (show r * S.C.R + 1 ≤ s - 1 by omega) (hEndM _ (by omega)) hu₁
  have hGs1 := hG (s - 1) (by omega)
  have hRootC₁ : (M.get_fc_root (x.st kp (S.P.proposer s))).AncestorEq C₁ :=
    (hGs1 _ _ hrsrc (by omega)).2 u₁ hu₁U C₁ hC₁
  have hFrameP : ∀ C : Block V, 𝓒 C →
      ∃ W ∈ (M.fg_to_ac (x.tickInput (S.P.proposer s) (M.slotStart S.C s))).tree,
        W ∈ (M.fg_to_ac (x.tickInput (S.P.proposer s) (M.slotStart S.C s))).viable_heads ∧ C.AncestorEq W := by
    rintro C ⟨μ, hμ, hC⟩
    rw [htip]
    have hCC₁ : C.AncestorEq C₁ := (hGs1 _ _ hC (by omega)).2 u₁ hu₁U C₁ hC₁
    have hcomp := GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_both hRootC₁ hCC₁
      ((GoldilocksCorrectness.Proofs.Routines.compatible_iff _ _).2 (Or.inl (ancestorEq_refl C₁)))
    have hj0 : ((M.voteTime S.C (s - 2 + 1) : ℕ) : ℝ) ≤ x.time kp := by
      rw [show s - 2 + 1 = s - 1 by omega]
      have : ((M.voteTime S.C (s - 1) : ℕ) : ℝ) + 2 * Δ S ≤ ((M.slotStart S.C s : ℕ) : ℝ) := by
        exact_mod_cast (show M.voteTime S.C (s - 1) + 2 * Δ S ≤ M.slotStart S.C s by omega)
      linarith
    have hjc : x.time kp < ((M.supportCutoff S.C (s - 2 + 2) : ℕ) : ℝ) := by
      rw [show s - 2 + 2 = s by omega, hcR]; linarith
    rcases (GoldilocksCorrectness.Proofs.Routines.compatible_iff _ _).1 hcomp with hRC | hCR
    · exact P.frame_source_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG2 hσ2 hEnd2 hj0 hjc hpk hC (by omega) hRC
    · obtain ⟨W, hW⟩ := (frame_has_viable_head_st M F) S A x R E kp (S.P.proposer s)
      obtain ⟨hWT, hFW, hRW, -⟩ := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _
        ((lem11_node_invariant M F S A x R E kp _ hpk).1) _).1 hW
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)] at hRW
      exact ⟨W, ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hWT, hFW⟩, hW,
        ancestorEq_trans hCR hRW⟩
  -- the members' windows: honest at the support cutoff of their slot, active from `tGAT` to it
  have hdwS : tGAT + Δ S ≤ M.dutyWindowStart S.C s :=
    (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT s
      (le_trans hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
        (by omega)))
  have hgs := P.gstSync M F U (show r * S.C.R ≤ s by omega)
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  have hMemWin : ∀ w ∈ Hon M S A x s,
      w ∈ A.activeThroughout x (M.dutyWindowStart S.C s) (M.supportCutoff S.C (s + 1)) := fun w hw =>
    Activity.mem_activeThroughout_of_le (by exact_mod_cast (show tGAT ≤ M.dutyWindowStart S.C s by omega)) le_rfl
      (P.member M F hw (hEndM _ (by omega)))
  have hpAH : S.P.proposer s ∈ A.activeThroughout x tGAT (M.supportCutoff S.C s) := P.window M F hp (hEndM _ (by omega))
  have hqAH : S.P.proposer s'' ∈ A.activeThroughout x tGAT (M.supportCutoff S.C s'') := P.window M F hq le_rfl
  have hqH : S.P.proposer s'' ∈ Hon M S A x (s'' - 1) := by
    show S.P.proposer s'' ∈ roundMembers M S A x (s'' - 1 + 1)
    rw [show s'' - 1 + 1 = s'' by omega]
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hq⟩
  have h89 := (lem89r_quiet_round_targets M F U Fx) S A x R GST rs₀ s s'' (Hon M S A x) 𝓒 B B'
    (S.P.proposer s) (S.P.proposer s'') E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F
    ((GoldilocksCorrectness.Record.Statements.Executions.RootsNameBlocksUntil.mono M)
      (by exact_mod_cast hcm _ _ (Nat.sub_le s'' 1)) hRoots)
    (fun k u c hk hc => hRootsTick k u c hk (le_trans hc (hcm _ _ (Nat.sub_le s'' 1))))
    hParent hrs (by omega)
    ((GoldilocksCorrectness.Record.Proofs.Routines.delivery_of_round M.toSlotLayout F.sched) S hs'')
    (P.gstSync M F U (show r * S.C.R ≤ s - 1 by omega)).2.2
    (by
      --: the attestations' sync delay has elapsed after `GST` by the start of slot `s''`
      have hdel := (GoldilocksCorrectness.Record.Proofs.Routines.delivery_of_round M.toSlotLayout F.sched) S hs''
      have hΔsF : Δs_F ≤ Δ_F S ∨ Δs_F + 3 * Δ S ≤ 4 * Δ S * S.C.k := by
        rcases hΔs_F with h | h
        · left
          exact_mod_cast (show (Δs_F : ℝ) ≤ Δ_F S by linarith)
        · right
          exact_mod_cast (show ((Δs_F + 3 * Δ S : ℕ) : ℝ) ≤ ((4 * Δ S * S.C.k : ℕ) : ℝ) by push_cast; linarith)
      have hGc : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s := hgs.2.2
      have hA := hAnchor
      rw [GoldilocksCorrectness.Proofs.Routines.anchorCW_eq, Nat.mul_add] at hA
      have hsm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
        (show r * S.C.R + 1 ≤ s'' by omega)
      rcases max_choice (Δ_F S) Δs_F with hm | hm <;> rw [hm]
      · omega
      · rcases hΔsF with h | h
        · omega
        · omega)
    (fun w _ => (adversaryFewerThanThirdUntil_tickStep M F) x R E w _ (by
      have : M.supportCutoff S.C (s + 1) + Δ S ≤ tAwakeEnd := by omega
      have hR' : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + Δ S ≤ ((tAwakeEnd : ℕ) : ℝ) := by exact_mod_cast this
      linarith) hThird)
    (fun s' _ _ => (hon_succ_subset M F) S A R E s')
    (fun s' h1 h2 => (P.members_sets M F U (show r * S.C.R ≤ s' by omega) (hEndM _ (by omega))).1)
    (fun w hw => (holder42_of_dev_window M F U) S A x hA0 hB0 hΔs (by omega) (hMemWin w hw))
    (fun w hw => (holderV_of_dev_window M F U) S A x hA0 hB0 hΔs (by
      have := hgs.2.1
      omega) (hMemWin w hw))
    hHoldF
    ((fun (t : ℕ) (Hn : Finset V) (hTh : A.AdversaryFewerThanThirdUntil x (validator_count V) t)
        (hSup : Finset.univ \ A.corruptedAtTime x t ⊆ Hn) => (show quorum V ≤ Hn.card by
          have h1 := Finset.card_le_card hSup
          have h2 : 3 * (A.corruptedAtTime x t).card < validator_count V := hTh _ (fun v hv => by
            obtain ⟨i, hi, hv'⟩ := Activity.mem_corruptedAtTime.1 hv
            exact ⟨i, hi, hv'⟩)
          rw [Finset.card_univ_sdiff] at h1
          unfold quorum
          unfold validator_count at *
          omega)) (M.supportCutoff S.C (s + 1)) (Hon M S A x s)
      (hThird.mono (by exact_mod_cast (show M.supportCutoff S.C (s + 1) ≤ tAwakeEnd by omega)))
      (fun u hu => by unfold Hon roundMembers; exact hu))
    (fun s' h1 h2 => P.committee M F (show r * S.C.R ≤ s' by omega) (hEndM _ (by omega)))
    -- `tStart := tGAT + Δ S`, more than both clock bounds before Lemma 12's read time of slot `s − 1`
    ((tGAT + Δ S : ℕ) : ℤ)
    ((tStart_lt_readTime_of_anchor M F U) S hA0 hB0 hsk hΔs hAnchor hs)
    (by
      -- the proposer's reader to its tick to the start of slot `s`, from its window from `tGAT`
      have hle : tGAT + Δ S ≤ M.slotStart S.C s := by
        have := hgs.1
        omega
      refine (mem_activeThroughoutToTick_of_mem_activeThroughout M F) x R E (by omega) (by exact_mod_cast hle) ?_
      refine Activity.mem_activeThroughout_of_le ?_ ?_ hpAH
      · push_cast; linarith
      · have : ((M.slotStart S.C s : ℕ) : ℝ) + 2 * Δ S = ((M.supportCutoff S.C s : ℕ) : ℝ) := by linarith
        linarith)
    (by
      -- the proposer's holder row at the start of slot `s`, inside its window from `tGAT`
      have h := hgs.1
      have hu : M.slotStart S.C s - max (Δ S) Δs + Δs ≤ M.supportCutoff S.C s := by omega
      have hl : tGAT ≤ M.slotStart S.C s - max (Δ S) Δs := by omega
      exact Activity.mem_activeThroughout_of_le (by exact_mod_cast hl) (by exact_mod_cast hu) hpAH)
    (fun w _ => (proposer_honest_at_member_tick M F U) R E hSkew hp)
    hqH rfl rfl
    (by
      -- `q`'s receiver row, inside its window from `tGAT` to the support cutoff of slot `s''`
      intro i' h1 h2
      have hdR : ((tGAT : ℕ) : ℝ) ≤ ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) := by
        exact_mod_cast le_trans (by omega : tGAT ≤ M.dutyWindowStart S.C s) (le_max_left _ _)
      have ht := (time_tickStep_le_add_behind M F) x R E (S.P.proposer s'') (M.slotStart S.C s'')
      have hmono := R.time_mono h2
      obtain ⟨-, hcq, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s''
      have hleR : ((M.slotStart S.C s'' : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C s'' : ℕ) : ℝ) := by
        exact_mod_cast (show M.slotStart S.C s'' + Δ S ≤ M.supportCutoff S.C s'' by omega)
      exact Activity.mem_active_of_mem_activeThroughout_of_time (fun _ _ h => R.time_mono h) hqAH
        (le_trans hdR h1) (by linarith))
    hB hB' hQuiet hChain hFamLocks ⟨μA, hμA, hAsrc⟩ hFrameP
  rcases h89 with hcol | ⟨hBB', -, h3, hsaved, -, -⟩
  · exfalso
    apply hCol
    rw [(GoldilocksCorrectness.Record.Proofs.View.rootCollisionAtProposal_unfold M x)]
    exact hcol
  -- `B`'s height is greater than `H₂`: `L` is a line source of slot `r * R`, an ancestor of `B`'s parent
  have hPar := P.parent_extends_sources M F R E hNet hSkew hRedeliver Sy hΔs U Fx
    (show r * S.C.R + S.C.k + 2 ≤ s by omega) (hEndM _ (by omega)) hp hB
  have hPB : B.parent.AncestorEq B := by
    obtain ⟨s₀, rfl⟩ : ∃ s₀, s = s₀ + 1 := ⟨s - 1, by omega⟩
    obtain ⟨i, hl, hsent⟩ := hB
    obtain ⟨-, -, hBpar?, -⟩ := (proposal_parent_walk_end M F U) S A x R E s₀ i B _ hl hsent
    exact ancestorEq_of_parent? hBpar?
  have hLP := hPar (r * S.C.R) L (P.source_L M F R U (hcm _ _ (by omega))) (by omega)
  have hHB : H₂ < (M.chainStateOf S.C B).h := by
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C (ancestorEq_trans hLP hPB)
    rw [hL] at h1
    unfold Height at *
    omega
  obtain ⟨hrise, hjust⟩ := h3 (fun u huH j t' a hl ht' hsent hah => by
    have huc : u ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) := by
      unfold Hon roundMembers at huH
      exact (Finset.mem_sdiff.1 huH).2
    refine P.attestation_target M F R E hNet hSkew hRedeliver Sy hΔs U Fx hl ?_
      ((not_mem_corruptedAtTime_of_le M) x R E ht' huc)
      ((not_mem_corruptedAtTime_of_le M) x R E (hcm (r * S.C.R + 1) (s + 1) (by omega)) huc) hsent
      (by rw [hah]; exact hHB)
    intro r'' ht''
    rw [ht''] at ht'
    have hlt : r'' * S.C.R + 1 ≤ s + 1 := by
      by_contra hn
      have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_lt M.toSlotLayout F.sched) S
        (show s + 1 < r'' * S.C.R + 1 by omega)
      exact absurd ht' (Nat.not_le.mpr this)
    exact hcm _ _ (by omega))
  exact ⟨hBB', hrise, hjust, hsaved⟩

/-! ## The kit of C6: delivery, the justification cache, the honest chain -/

/-- **The justification cache bounds a held block's justification height.** At a step `i` at a
time at most `tEnd`, with fewer than a third of the validators in the adversary set up to `tEnd`,
an honest `w` holding `B` has `h_j(B)` at most its cache `h_j`: when `w`'s finalized block, the
finalized block of a held block `D`'s chain state, is an ancestor of `B` (Lemma 68, when `h_F(D)` is
less than `B`'s height), by Lemma 57; otherwise `h_j(B) < h(B) ≤ h_F(D) ≤ h_j(D) ≤ h_j`.

Roots name blocks until `tR`, at least `x[i].time`: Lemma 68 at the step `i`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: at a step at a time at most `tEnd`, the justification height of the chain state of a
block an honest validator holds is at most that validator's cached justification height. -/
theorem h_j_ge_of_held_exec (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {tR : ℝ}
      (hRoots : RootsNameBlocksUntil M A x tR) (tEnd i : ℕ)
    (w : V) (B : Block V)
      (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (hi : x.time i ≤ tEnd) (hw : w ∉ A.corrupted i)
    (hB : B ∈ (x.st i w).tree)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : x.time i ≤ tR) :
    (M.chainStateOf S.C B).h_j ≤ (x.st i w).justifiedHeight := by
  obtain ⟨D, hD, hF⟩ := (finalizedFromChain_of_exec M F) S A x R E i w
  have hσ : ∀ X ∈ (x.st i w).tree, M.chainStateOf S.C X = M.chainStateOf S.C X :=
    fun X hX => rfl
  have hT : A.AdversaryFewerThanThirdUntil x (validator_count V) (max (x.time i) (x.time i)) := by
    rw [max_self]
    exact hThird.mono hi
  by_cases hlt : (M.chainStateOf S.C D).h_F < (M.chainStateOf S.C B).h
  · have hFB := (lem68_honest_past_finalized M F Fx) S A x R E hRoots i i w w D B hT hw hw hD hB hlt
      (max_le htR htR)
    have := (GoldilocksCorrectness.Record.Statements.Executions.h_j_of_mem_T_of_exec M F) S A x R E i w B hB (by rw [hF]; exact hFB)
    rw [hσ B hB] at this
    exact this
  · have hFD : (x.st i w).finalized.AncestorEq D := by
      rw [hF]
      by_cases h0 : (M.chainStateOf S.C D).h_F = 0
      · rw [(GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_F_genesis M F) S.C D h0]
        exact GoldilocksCorrectness.Proofs.Routines.genesis_ancestorEq D
      · exact (((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).2.2
          (Nat.one_le_iff_ne_zero.mpr h0)).2.2.1
    have hjD := (GoldilocksCorrectness.Record.Statements.Executions.h_j_of_mem_T_of_exec M F) S A x R E i w D hD hFD
    rw [hσ D hD] at hjD
    have h1 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B B).1.2.1
    have h2 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C D D).1.2.2
    unfold Height at *
    omega

namespace PartAHyps
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {n' : M.N}

/-- **An honest finalized block before a proposal's vote time is an ancestor of the proposal.** For
the honest proposal `B` of a slot `s ≥ r * R + k + 2` whose support cutoff is in the phase, the
finalized block of every validator honest at the vote time of slot `s`, before that time, is an
ancestor of `B`: it is an ancestor of its root (Lemma 46), a line source of a round's first slot
`μ` with `μ + 2 ≤ s` (`root_source`), and `B`'s parent extends every such source
(`parent_extends_sources`).

The variables:
- `M`: the model; `F`: its facts.

Read aloud: every validator honest at the vote time of slot `s` has, before that time, its finalized
block an ancestor of the honest proposal of `s`, for `s ≥ r * R + k + 2` with its support cutoff in
the phase. -/
theorem F_before_vote_ancestor_proposal (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    {s : ℕ} {B : Block V} {u : V} (hs : r * S.C.R + S.C.k + 2 ≤ s)
    (hEnd : M.supportCutoff S.C s ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C s))
    (hB : ProposalAt M S x s B) (hu : u ∉ A.corruptedAtTime x (M.voteTime S.C s)) :
    (x.stateBefore (M.voteTime S.C s) u).finalized.AncestorEq B := by
  have hk := S.C.k_ge_two
  obtain ⟨σ, rfl⟩ : ∃ σ, s = σ + 2 := ⟨s - 2, by omega⟩
  obtain ⟨hvs, hcs, -, hss, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
  have hG := P.lineInv_upto M F R E hNet hSkew hRedeliver Sy hΔs U Fx hEnd
  have haR : aR M S r < M.voteTime S.C (σ + 2) := by
    have : aR M S r = M.supportCutoff S.C (r * S.C.R + 1) := rfl
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show r * S.C.R + 1 ≤ σ + 1 by omega)
    obtain ⟨-, hc1, -, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
    rw [show σ + 1 + 1 = σ + 2 from rfl] at hs1
    omega
  -- `v` ticks to the action time of round `r` at a real time at most that time plus `ΔClockBehind`, less than the
  -- vote time of slot `σ + 2`; the reading at that vote time is one delay before the support cutoff of slot `σ + 2`
  have hsk := P.hSkew
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hvk := E.tick_active _ _ _ P.hk₀
  have haRv : ((aR M S r : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C (σ + 2) : ℕ) : ℝ) := by
    have : aR M S r = M.supportCutoff S.C (r * S.C.R + 1) := rfl
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show r * S.C.R + 1 ≤ σ + 1 by omega)
    obtain ⟨-, hc1, -, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
    rw [show σ + 1 + 1 = σ + 2 from rfl] at hs1
    exact_mod_cast (show aR M S r + Δ S ≤ M.voteTime S.C (σ + 2) by omega)
  have hv0 : ∃ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r) ∧ k < x.stepBefore (M.voteTime S.C (σ + 2)) ∧
      u ∈ A.active k :=
    ⟨v, x.tickStep v (aR M S r), P.hk₀,
      (lt_stepBefore_of_not_other M) x R E (by rw [P.hk₀]; exact nofun) (by linarith [hvk.2.2]), hvk.1⟩
  have hvt : ((M.voteTime S.C (σ + 2) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) - ΔClockAhead := by
    have : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) = ((M.voteTime S.C (σ + 2) : ℕ) : ℝ) + Δ S := by
      rw [hcs, hvs]; push_cast; ring
    linarith
  obtain ⟨r', -, ⟨u', k', hk', hk't, -⟩, hsrc⟩ := P.root_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG (show r * S.C.R ≤ σ by omega) hEnd hv0
    hvt hu
  have hr' : r' * S.C.R + 2 ≤ σ + 2 := by
    by_contra h
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show σ + 2 ≤ r' * S.C.R + 1 by omega)
    -- `u'`'s tick to the support cutoff of slot `r' * R + 1` is at a real time at least that cutoff minus
    -- `ΔClockAhead`, and before the vote time of slot `σ + 2`, one delay before its support cutoff (`hSkew`)
    have hkt := (E.tick_active _ _ _ hk').2.1
    have hk1 := ((lt_stepBefore_iff M) x R E).1 hk't
    have hkk := (time_mono M) x R (Nat.le_succ k')
    have hsk := P.hSkew
    have hB0 := E.behind_nonneg
    have hle : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) ≤ ((aR M S r' : ℕ) : ℝ) := by exact_mod_cast this
    have hcv : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) = ((M.voteTime S.C (σ + 2) : ℕ) : ℝ) + Δ S := by
      rw [hcs, hvs]; push_cast; ring
    linarith
  obtain ⟨-, hPB⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.proposal_slot_parent M F U) S A x R E (show 1 ≤ σ + 2 by omega) hB
  exact ancestorEq_trans ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_stateBefore M F) S A x R E _ u)
    (ancestorEq_trans (P.parent_extends_sources M F R E hNet hSkew hRedeliver Sy hΔs U Fx hs hEnd hp hB _ _ hsrc hr') hPB)


/-- **An honest finalized block at a vote tick is an ancestor of the proposal** (rule R3: read at the
validator's own tick). For the honest proposal `B` of a slot `s ≥ r * R + k + 2` whose support cutoff
is in the phase, every validator `u` that ticks to the vote time of slot `s` has, in the state that
tick starts from, its finalized block an ancestor of `B`: it is an ancestor of its root (Lemma 46),
a line source of a round's first slot `μ` with `μ + 2 ≤ s` (`root_source_st` at the tick's step),
and `B`'s parent extends every such source (`parent_extends_sources`). The tick is at a real time at
most `ΔClockBehind` after the vote time, so more than `ΔClockAhead` before the support cutoff of
slot `s`, one delay after it (`hSkew`); a tick to the action time of a round whose first slot is at
least `s − 1` is at a real time at least `ΔClockAhead` before that cutoff, so after `u`'s tick.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `P`: the bundle of part A; `s`: the slot; `B`: its proposal; `u`: the validator;
- `hk`: `u` ticks to the vote time of slot `s` at the step `x.tickStep u (M.voteTime S.C s)`.

Read aloud: every validator that ticks to the vote time of slot `s` has, in the state its tick starts
from, its finalized block an ancestor of the honest proposal of `s`, for `s ≥ r * R + k + 2` with its
support cutoff in the phase. -/
theorem F_at_vote_tick_ancestor_proposal (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    {s : ℕ} {B : Block V} {u : V} (hs : r * S.C.R + S.C.k + 2 ≤ s)
    (hEnd : M.supportCutoff S.C s ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C s))
    (hB : ProposalAt M S x s B) (hk : x.lbl (x.tickStep u (M.voteTime S.C s)) = Event.tick u (M.voteTime S.C s)) :
    (x.tickInput u (M.voteTime S.C s)).finalized.AncestorEq B := by
  have hk2 := S.C.k_ge_two
  obtain ⟨σ, rfl⟩ : ∃ σ, s = σ + 2 := ⟨s - 2, by omega⟩
  obtain ⟨hvs, hcs, -, hss, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
  have hG := P.lineInv_upto M F R E hNet hSkew hRedeliver Sy hΔs U Fx hEnd
  have hsk := P.hSkew
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hvk := E.tick_active _ _ _ P.hk₀
  have hjk := E.tick_active _ _ _ hk
  have haRv : ((aR M S r : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C (σ + 2) : ℕ) : ℝ) := by
    have : aR M S r = M.supportCutoff S.C (r * S.C.R + 1) := rfl
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show r * S.C.R + 1 ≤ σ + 1 by omega)
    obtain ⟨-, hc1, -, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
    rw [show σ + 1 + 1 = σ + 2 from rfl] at hs1
    exact_mod_cast (show aR M S r + Δ S ≤ M.voteTime S.C (σ + 2) by omega)
  have hcv : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) = ((M.voteTime S.C (σ + 2) : ℕ) : ℝ) + Δ S := by
    rw [hcs, hvs]; push_cast; ring
  -- `v`'s tick to the action time of round `r` is a step before `u`'s tick
  have hv0 : ∃ (w : V) (k : ℕ), x.lbl k = Event.tick w (aR M S r) ∧
      k < x.tickStep u (M.voteTime S.C (σ + 2)) ∧ w ∈ A.active k := by
    refine ⟨v, x.tickStep v (aR M S r), P.hk₀, ?_, hvk.1⟩
    by_contra hc
    have h := (time_mono M) x R (not_lt.1 hc)
    linarith [hvk.2.2, hjk.2.1]
  have hjt : x.time (x.tickStep u (M.voteTime S.C (σ + 2))) <
      ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) - ΔClockAhead := by
    linarith [hjk.2.2]
  have hw' : u ∉ A.corrupted (x.tickStep u (M.voteTime S.C (σ + 2))) := E.not_mem_corrupted_of_tick hk
  obtain ⟨r', -, ⟨u', k', hk', hk'j, -⟩, hsrc⟩ := P.root_source_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG (show r * S.C.R ≤ σ by omega) hEnd hv0
    hjt hw'
  have hr' : r' * S.C.R + 2 ≤ σ + 2 := by
    by_contra h
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show σ + 2 ≤ r' * S.C.R + 1 by omega)
    have hkt := (E.tick_active _ _ _ hk').2.1
    have hkk := (time_mono M) x R hk'j.le
    have hle : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) ≤ ((aR M S r' : ℕ) : ℝ) := by exact_mod_cast this
    linarith [hjk.2.2]
  obtain ⟨-, hPB⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.proposal_slot_parent M F U) S A x R E (show 1 ≤ σ + 2 by omega) hB
  show (x.st (x.tickStep u (M.voteTime S.C (σ + 2))) u).finalized.AncestorEq B
  exact ancestorEq_trans ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E _ u)
    (ancestorEq_trans (P.parent_extends_sources M F R E hNet hSkew hRedeliver Sy hΔs U Fx hs hEnd hp hB _ _ hsrc hr') hPB)

/-- **The old attestations at an opening after the fast block.** For the honest proposal `B` of a
round's first slot `s ≥ r * R + k + 2` whose support cutoff of slot `s + 1` is in the phase, every
honest attestation sent before that support cutoff has a height at most `B`'s: before the action
time of round `r` at most `H₂ < h(B)`; from then on, it names a line source's entry of a round's
first slot `μ` with `μ + 2 ≤ s` at its height (`attestation_entry`, `round_slot_le_of_lt`), an
ancestor of `B`'s parent (`parent_extends_sources`).

The variables:
- `M`: the model; `F`: its facts.

Read aloud: every honest attestation sent before the support cutoff of slot `s + 1` has a height at
most that of the honest proposal of the round's first slot `s ≥ r * R + k + 2`. -/
theorem old_attestations_at_opening (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    {s : ℕ} {B : Block V} (hs : r * S.C.R + S.C.k + 2 ≤ s) (hsR : S.C.R ∣ s)
    (hEnd : M.supportCutoff S.C (s + 1) ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C s))
    (hB : ProposalAt M S x s B) :
    OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s + 1)) (M.supportCutoff S.C (s + 1)) (M.chainStateOf S.C B).h := by
  have hk := S.C.k_ge_two
  have hEnd0 : M.supportCutoff S.C s ≤ tAwakeEnd := le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd
  obtain ⟨-, hPB⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.proposal_slot_parent M F U) S A x R E (show 1 ≤ s by omega) hB
  have hPar := P.parent_extends_sources M F R E (by assumption) (by assumption) (by assumption) Sy hΔs U Fx hs hEnd0 hp hB
  have hLB : (M.chainStateOf S.C L).h ≤ (M.chainStateOf S.C B).h :=
    (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C (ancestorEq_trans (hPar (r * S.C.R) L
      (P.source_L M F R U (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd)) (by omega)) hPB)
  intro i t u a hl ht hHonC hSent
  -- the sender, honest at the support cutoff of slot `s + 1`, is honest at its tick and at the action
  -- time of round `r`
  have htN : t < M.supportCutoff S.C (s + 1) := by exact_mod_cast ht
  have hHon : u ∉ A.corruptedAtTime x t := (not_mem_corruptedAtTime_of_le M) x R E (le_of_lt (by exact_mod_cast ht)) hHonC
  have hHonR : u ∉ A.corruptedAtTime x (aR M S r) :=
    (not_mem_corruptedAtTime_of_le M) x R E (show aR M S r ≤ M.supportCutoff S.C (s + 1) from
      ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show r * S.C.R + 1 ≤ s + 1 by omega))) hHonC
  by_cases htr : aR M S r ≤ t
  · obtain ⟨r', Eb, -, rfl, hE, -, hEh, -⟩ :=
      P.attestation_entry M F R E (by assumption) (by assumption) (by assumption) Sy hΔs U Fx hl htr
      (fun r' hr' => by
        rw [hr'] at htN
        have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.round_slot_le_of_lt M.toSlotLayout F.sched) S hsR htN
        exact le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
          (show r' * S.C.R + 2 ≤ s + 1 by omega)) hEnd) hHon hSent
    have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.round_slot_le_of_lt M.toSlotLayout F.sched) S hsR htN
    rw [← hEh]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C (ancestorEq_trans (hPar _ Eb hE h2) hPB)
  · have := P.hOld i t u a hl (by norm_cast; omega) hHonR hSent
    rw [P.hL] at hLB
    unfold Height at *
    omega

end PartAHyps

/-! ## C6, the caches at the hand-over step -/

/-- **The delivery of an honest proposal to a receiver active from the send, at the receiver's own ticks.** `p`, outside the
adversary set after the steps `i` and `i + 1`, puts its block `B` of a slot at most `s` on the wire at the step `i`, at a real
time at most the start of slot `s` plus `ΔClockBehind`, and holds it after `i`; `w` ticks to the start of slot `s` at `k₂`
and to the vote time of slot `s` at `kR`, and is active after every step from `i + 1` up to `kR`; the deadline of `p`'s send,
plus `ΔClockAhead`, is at most the vote time. Then `B` is in `w`'s tree at `kR`, when `w`'s finalized block there is
compatible with `B`.

Why: `proposal_held_by_voter_of_deadline`'s argument, with the receiver's window starting at the send and its tick to the
start of slot `s` given: the delivery promise delivers `B` before `kR`; a
delivery that found `w` not reacted to the start of `B`'s slot comes before `k₂`, so `w`'s first tick at a clock value at
least that start is `k₂` or earlier, at a real time at most the start of slot `s` plus `ΔClockBehind`, at least
`ΔRedeliver` before `kR` (`hRedeliver`); `mem_tree_of_admitted_delivery` admits it.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, the run's facts, the environment's facts; `s`: the
  proposal's slot; `i`: the step of `p`'s send; `B`: the block; `p`: the proposer; `w`: the receiver; `k₂`, `kR`: `w`'s
  ticks to the start and to the vote time of slot `s`; `d`: the deadline of `p`'s send.

Read aloud: an honest proposal sent by the start of its slot, whose delivery deadline leaves `ΔClockAhead` before the vote
time of the slot, is in the tree of every receiver active from the send to its tick to that vote time, that ticked to the
slot's start, and whose finalized block there is compatible with it. -/
theorem proposal_held_by_receiver_of_ticks (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s i k₂ kR : ℕ) (B : Block V) (p w : V)
    {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (hRoots : RootsNameBlocksUntil M A x (x.time kR))
    (hParent : ParentHeldAtDelivery M x)
    (hk₂ : x.lbl k₂ = Event.tick w (M.slotStart S.C s))
    (hkR : x.lbl kR = Event.tick w (M.voteTime S.C s))
    (hwin : ∀ j : ℕ, i + 1 ≤ j → j ≤ kR → w ∈ A.active j)
    (hpi : p ∉ A.corrupted i) (hpi1 : p ∉ A.corrupted (i + 1))
    (hTi1 : x.time (i + 1) ≤ (M.slotStart S.C s : ℝ) + ΔClockBehind)
    (hsent : (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i)
    (hBp : B ∈ (x.st (i + 1) p).tree) (hBs : B.slot ≤ s)
    {d : ℝ} (hdl : deadline ⟨p, NamedObject.block B⟩ (x.time (i + 1)) = some d)
    (hd : d + ΔClockAhead ≤ (M.voteTime S.C s : ℝ))
    (hF : (x.st kR w).finalized.compatible B = true) :
    B ∈ (x.st kR w).tree := by
  classical
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hss : ∀ n : ℕ, M.slotStart S.C n = 4 * Δ S * n := fun n =>
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S n
  have hvt : M.voteTime S.C s = M.slotStart S.C s + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hvtR : ((M.voteTime S.C s : ℕ) : ℝ) = (M.slotStart S.C s : ℝ) + Δ S := by
    rw [hvt]; push_cast; ring
  -- the real times of `p`'s send `i` and of `w`'s ticks `k₂` and `kR`
  have hTi : x.time i ≤ (M.slotStart S.C s : ℝ) + ΔClockBehind := le_trans (R.time_le_succ i) hTi1
  have hkRt := (E.tick_active kR w _ hkR).2.1
  rw [hvtR] at hkRt
  have hk₂t := (E.tick_active k₂ w _ hk₂).2.2
  have hik : i < kR := by
    by_contra hc
    have := htime (show kR ≤ i by omega)
    linarith
  have hwkR : w ∉ A.corrupted kR :=
    Activity.not_mem_corrupted_of_mem_active (E.tick_active kR w _ hkR).1
  -- the deadline of `p`'s send is at most the time of `kR`
  have hdk : d ≤ x.time kR := by linarith
  have hrs : M.slotStart S.C B.slot ≤ M.slotStart S.C s := by
    rw [hss, hss]; exact Nat.mul_le_mul_left _ hBs
  -- the re-delivery premise: a delivery that found `w` not reacted to `B`'s release clock value is
  -- before `k₂`, so `w`'s first tick at a clock value at least it is `k₂` or earlier
  have hprem : ∀ (r j₀ k₁ t₁ : ℕ),
      releaseOf M S.C (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)).msg = some r →
      i < j₀ → x.lbl j₀ = Event.deliver w ⟨p, NamedObject.block B⟩ → ¬ x.ReactedAtLeast j₀ w r →
      j₀ < k₁ → k₁ ≤ kR → x.lbl k₁ = Event.tick w t₁ → r ≤ t₁ →
      (∀ (l t' : ℕ), j₀ < l → l < k₁ → x.lbl l = Event.tick w t' → t' < r) →
      x.time (k₁ + 1) + ΔRedeliver ≤ x.time kR := by
    intro r j₀ k₁ t₁ hrel _ _ hnr hjk₁ _ hlk₁ _ hfirst
    have hr' : M.slotStart S.C B.slot = r := Option.some.inj hrel
    subst hr'
    have hj₀k₂ : j₀ < k₂ := by
      by_contra hc
      exact hnr ⟨k₂, by omega, M.slotStart S.C s, hrs, Or.inl hk₂⟩
    have hk₁k₂ : k₁ ≤ k₂ := by
      by_contra hc
      have := hfirst k₂ _ hj₀k₂ (by omega) hk₂
      omega
    have h1 := htime hk₁k₂
    rw [R.time_keep k₁ (by rw [hlk₁]; exact nofun)]
    linarith
  -- the delivery of `B` to `w` before `kR`, which found `w` reacted to the start of `B`'s slot
  obtain ⟨j, -, hjk, hlj, hadm, -⟩ := E.delivered i kR w ⟨p, NamedObject.block B⟩ _ _ ⟨hsent, hpi⟩
    (show acObject (NamedObject.block B) from trivial) hkR hik hwin hdl hdk hprem
  have hreact : x.ReactedAtLeast j w (M.slotStart S.C B.slot) :=
    hadm _ rfl (hrs.trans (by rw [hvt]; omega))
  have hTj : x.time j ≤ x.time (x.tickStep w (M.voteTime S.C s)) := by
    rw [(tickStep_eq_of_lbl M) x E hkR]
    exact htime hjk.le
  have hRoots' : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.voteTime S.C s))) := by
    rw [(tickStep_eq_of_lbl M) x E hkR]; exact hRoots
  exact (mem_tree_of_admitted_delivery M F U) R E hRoots' hParent hpi1
    (by rw [(tickStep_eq_of_lbl M) x E hkR]; exact htime hik) hBp hlj hTj hreact hjk hwkR hF

/-- **C6's caches from the carrier held at the hand-over step.** The part of `caches_at_handover_of_held`
that follows once `u` holds `B₃` at the step `i₁`: `h_j(B₃) ≤ u`'s cache (`h_j_ge_of_held_exec`), greater
than `H`; `u`'s justified block is that of a held block `D`'s chain state with its cache
(`cachesWitnessed_of_exec`), carried by a justification certificate on `D`'s chain at that height
(Lemma 66), so `hCerts` gives an entry `E` on the honest chain with its root, held by an honest attester
at a tick before `i₁`, and `E` is the justified block (roots name blocks); the finalized block is an
ancestor of the justified one (Lemma 46).

Roots name blocks until `x[i₁].time`: the justified block `u` holds at the step `i₁` against the entry
`hCerts` names, held at a tick before `i₁`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `tAwakeEnd`: the bound of
  the adversary count; `s₀`: the first slot of the honest chain; `H`: the threshold; `i₁`: the step;
  `B₃`: the carrier; `u`: the validator.

Read aloud: a validator outside the adversary set that holds a block justified above `H` has its caches
on the honest chain above `H`, when every justified block above `H` an honest validator holds was
certified by an honest attester holding an entry of the honest chain. -/
theorem caches_at_handover_of_mem (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (tAwakeEnd s₀ H i₁ : ℕ) (B₃ : Block V) (u : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hRoots : RootsNameBlocksUntil M A x (x.time i₁))
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hti : x.time i₁ ≤ tAwakeEnd)
    (hJ : H < (M.chainStateOf S.C B₃).h_j)
    -- every justified block an honest validator holds at the step `i₁` at a height greater than
    -- `H` was certified by an honest attester `uₐ` that ran the update of the entry's slot `s_a` at
    -- its tick to the support cutoff of slot `s_a + 1`, a step before `i₁`, is honest up to the time
    -- of `i₁`, and held the entry when it ticked; the entry is on the honest chain at `s_a`
    (hCerts : ∀ (w : V) (D T : Block V) (h : Height),
      D ∈ (x.st i₁ w).tree → JustificationCertOn M D h T → H < h →
      ∃ (s_a : ℕ) (uₐ : V) (E : Block V), x.tickStep uₐ (M.supportCutoff S.C (s_a + 1)) < i₁ ∧
        x.lbl (x.tickStep uₐ (M.supportCutoff S.C (s_a + 1))) = Event.tick uₐ (M.supportCutoff S.C (s_a + 1)) ∧
        uₐ ∈ updaterAt M S A x s_a ∧ uₐ ∉ A.corruptedAtTime x (x.time i₁) ∧
        E ∈ (x.tickInput uₐ (M.supportCutoff S.C (s_a + 1))).tree ∧
        OnHonestChainAt M S A x s₀ s_a E ∧ IsEntry M S.C E ∧
        (M.chainStateOf S.C E).h = h ∧ T.root = E.root)
    -- `u` holds `B₃` at the step `i₁`
    (hB₃ : B₃ ∈ (x.st i₁ u).tree) :
    u ∉ A.corruptedAtTime x (x.time i₁) → CachesOnChain M S A x s₀ H (x.st i₁ u) := by
  intro huT
  have hu : u ∉ A.corrupted i₁ := (Activity.not_mem_corruptedAtTime.1 huT) i₁ le_rfl
  have hhj := (h_j_ge_of_held_exec M F Fx) S A x R E hRoots tAwakeEnd i₁ u B₃ hThird hti hu hB₃ le_rfl
  -- the justified block is a held block's, with its certificate
  obtain ⟨⟨D, hD, hJD, hjD⟩, -, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_exec M F) S A x R E i₁ u
  have hH : H < (x.st i₁ u).justifiedHeight := lt_of_lt_of_le hJ hhj
  have h1 : 1 ≤ (M.chainStateOf S.C D).h_j := by rw [← hjD]; unfold Height at *; omega
  obtain ⟨hcert, hJDD, hJh⟩ :=
    ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).1 h1
  obtain ⟨s_a, uₐ, Eb, hka, hla, -, hua, hEb, hE, hEe, -, hEr⟩ :=
    hCerts u D _ _ hD hcert (by rw [← hjD]; exact hH)
  have hJT : (M.chainStateOf S.C D).J ∈ (x.st i₁ u).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E i₁ u D _ hD hJDD
  have hkaT : x.time (x.tickStep uₐ (M.supportCutoff S.C (s_a + 1))) ≤ x.time i₁ := (time_mono M) x R hka.le
  have hua' : uₐ ∉ A.corrupted (x.tickStep uₐ (M.supportCutoff S.C (s_a + 1))) :=
    (Activity.not_mem_corruptedAtTime.1 hua) _ hkaT
  have hJE : (M.chainStateOf S.C D).J = Eb :=
    hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E hu le_rfl hJT)
      ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E hua' hkaT hEb) hEr
  refine ⟨hH, ?_, ?_, ?_, (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_J_of_exec M F) S A x R E i₁ u⟩
  · rw [hJD, hJE]; exact ⟨s_a, hE⟩
  · rw [hJD, hJE]; exact hEe
  · rw [hJD, hjD]; exact hJh

/-- **C6, the caches at the hand-over step (copy with the proposal held and the finalized blocks
on it).** The proof; the audited statement is in `Statements/Executions/Lemma89Statements.lean`.
Why: `B₃` reaches the validator `u` before its tick to the vote time of slot `s₃`
(`block_at_tick_of_held_tick` or `proposal_held_by_voter_of_deadline`, `u`'s finalized block before
that time an ancestor of `B₃` by hypothesis), so `h_j(B₃) ≤ u`'s cache (`h_j_ge_of_held_exec`), greater than `H`; `u`'s justified
block is that of a held block `D`'s chain state with its cache (`cachesWitnessed_of_exec`), carried
by a justification certificate on `D`'s chain at that height (Lemma 66), so `hCerts` gives an
entry `E` on the honest chain with its root, and `E` is the justified block (roots name blocks); the
finalized block is an ancestor of the justified one (Lemma 46).

Roots name blocks until `x[i₁].time`: the justified block `u` holds at the step `i₁` against the
entry `hCerts` names, at a slot whose update an honest attester ran at a tick before `i₁`, holding the entry; `B₃` reaches `u` by the vote time
of slot `s₃`, before it.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: once the carrier has reached everyone, every honest finality gadget's caches are on the
honest chain above the threshold. -/
theorem caches_at_handover_of_held (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd s₀ H s₃ s_m i₁ : ℕ) (B₃ : Block V) (u : V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time i₁))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hs₃ : s₃ ≤ s_m) (htGAT : tGAT + max (Δ S) Δs ≤ M.voteTime S.C s₃)
    (hEnd : M.supportCutoff S.C s_m ≤ tAwakeEnd)
    (hp : S.P.proposer s₃ ∉ A.corruptedAtTime x (M.supportCutoff S.C s₃))
    -- the proposer holds `B₃` in the state its tick to the start of slot `s₃` leaves
    (hHeld : B₃ ∈ (x.tickOutput (S.P.proposer s₃) (M.slotStart S.C s₃)).tree)
    -- `u` is active after every step from the proposer's tick to the start of slot `s₃` up to its own tick to the vote
    -- time of slot `s₃`, and `u` ticks to the start of slot `s₃`
    (hAct₃ : ∀ j : ℕ, x.tickStep (S.P.proposer s₃) (M.slotStart S.C s₃) ≤ j → j ≤ x.tickStep u (M.voteTime S.C s₃) → u ∈ A.active j)
    (hTick₃ : x.lbl (x.tickStep u (M.slotStart S.C s₃)) = Event.tick u (M.slotStart S.C s₃))
    -- every validator that ticks to the vote time of slot `s₃`, honest at that tick, has in the state
    -- the tick reads its finalized block `B₃` or an ancestor of `B₃`
    (hF₃ : ∀ w : V, x.lbl (x.tickStep w (M.voteTime S.C s₃)) = Event.tick w (M.voteTime S.C s₃) →
      w ∉ A.corruptedAtTime x (x.time (x.tickStep w (M.voteTime S.C s₃))) →
      (x.tickInput w (M.voteTime S.C s₃)).finalized.AncestorEq B₃)
    (hJ : H < (M.chainStateOf S.C B₃).h_j)
    -- every justified block an honest validator holds at the step `i₁` at a height greater than
    -- `H` was certified by an honest attester `uₐ` that ran the update of the entry's slot `s_a` at
    -- its tick to the support cutoff of slot `s_a + 1`, a step before `i₁`, is honest up to the time
    -- of `i₁`, and held the entry when it ticked; the entry is on the honest chain at `s_a` (K1's
    -- shape,)
    (hCerts : ∀ (w : V) (D T : Block V) (h : Height),
      D ∈ (x.st i₁ w).tree → JustificationCertOn M D h T → H < h →
      ∃ (s_a : ℕ) (uₐ : V) (E : Block V), x.tickStep uₐ (M.supportCutoff S.C (s_a + 1)) < i₁ ∧
        x.lbl (x.tickStep uₐ (M.supportCutoff S.C (s_a + 1))) = Event.tick uₐ (M.supportCutoff S.C (s_a + 1)) ∧
        uₐ ∈ updaterAt M S A x s_a ∧ uₐ ∉ A.corruptedAtTime x (x.time i₁) ∧
        E ∈ (x.tickInput uₐ (M.supportCutoff S.C (s_a + 1))).tree ∧
        OnHonestChainAt M S A x s₀ s_a E ∧ IsEntry M S.C E ∧
        (M.chainStateOf S.C E).h = h ∧ T.root = E.root)
    -- the step `i₁` is `u`'s tick to the vote time of slot `s_m`
    (hu : x.lbl i₁ = Event.tick u (M.voteTime S.C s_m)) :
    u ∉ A.corruptedAtTime x (x.time i₁) → CachesOnChain M S A x s₀ H (x.st i₁ u) := by
  intro huT
  classical
  set p := S.P.proposer s₃ with hpdef
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hN0 : (0 : ℝ) ≤ (ΔNet : ℝ) := Nat.cast_nonneg _
  obtain ⟨hvt₃, hcs₃, -, hss₃, hΔ⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s₃
  obtain ⟨hvtm, hcsm, -, -, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s_m
  have hssm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hs₃
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  -- the times, as reals
  have hvt₃R : ((M.voteTime S.C s₃ : ℕ) : ℝ) = (M.slotStart S.C s₃ : ℝ) + Δ S := by
    rw [hvt₃]; push_cast; ring
  have hcs₃R : ((M.supportCutoff S.C s₃ : ℕ) : ℝ) = (M.slotStart S.C s₃ : ℝ) + 2 * Δ S := by
    rw [hcs₃]; push_cast; ring
  have hvtmR : ((M.voteTime S.C s_m : ℕ) : ℝ) = (M.slotStart S.C s_m : ℝ) + Δ S := by
    rw [hvtm]; push_cast; ring
  have hcs₃E : ((M.supportCutoff S.C s₃ : ℕ) : ℝ) ≤ (tAwakeEnd : ℝ) := by
    exact_mod_cast (show M.supportCutoff S.C s₃ ≤ tAwakeEnd by omega)
  have hcsmE : ((M.slotStart S.C s_m : ℕ) : ℝ) + 2 * Δ S ≤ (tAwakeEnd : ℝ) := by
    have : M.slotStart S.C s_m + 2 * Δ S ≤ tAwakeEnd := by omega
    exact_mod_cast this
  have hG₃ : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.slotStart S.C s₃ : ℕ) : ℝ) + Δ S := by
    have : tGAT ≤ M.slotStart S.C s₃ := by omega
    have : ((tGAT : ℕ) : ℝ) ≤ ((M.slotStart S.C s₃ : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hGs : ((tGAT : ℕ) : ℝ) + (Δs : ℝ) ≤ ((M.slotStart S.C s₃ : ℕ) : ℝ) + Δ S := by
    have : tGAT + Δs ≤ M.slotStart S.C s₃ + Δ S := by omega
    exact_mod_cast this
  have hGST₃ : ((GST : ℕ) : ℝ) ≤ ((M.slotStart S.C s₃ : ℕ) : ℝ) := by
    have : GST ≤ M.slotStart S.C s₃ := by omega
    exact_mod_cast this
  have hssmR : ((M.slotStart S.C s₃ : ℕ) : ℝ) ≤ ((M.slotStart S.C s_m : ℕ) : ℝ) := by exact_mod_cast hssm
  -- `u`'s tick `i₁` to the vote time of slot `s_m`, inside the phase; `u` is active from `tGAT` up to it
  have hi₁t := (E.tick_active i₁ u _ hu).2
  rw [hvtmR] at hi₁t
  have hti : x.time i₁ ≤ tAwakeEnd := by linarith
  have hu_at : ∀ j : ℕ, x.time j ≤ x.time i₁ → u ∉ A.corrupted j := Activity.not_mem_corruptedAtTime.1 huT
  have huA : ∀ j : ℕ, (tGAT : ℝ) ≤ x.time (j + 1) → x.time j ≤ x.time i₁ → u ∈ A.active j := fun j h1 h2 =>
    Activity.mem_active.2 ⟨hAwake j u (le_trans h2 hti) h1 (hu_at j h2), hu_at j h2⟩
  -- `u`'s tick `kR` to the vote time of slot `s₃`, a step at most `i₁`
  obtain ⟨kR, hkR, hkRi⟩ : ∃ kR, x.lbl kR = Event.tick u (M.voteTime S.C s₃) ∧ kR ≤ i₁ := by
    rcases eq_or_lt_of_le hs₃ with h | h
    · subst h; exact ⟨i₁, hu, le_rfl⟩
    · have hss' := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
        (show s₃ + 1 ≤ s_m by omega)
      have hvv : ((M.slotStart S.C s₃ : ℕ) : ℝ) + 4 * Δ S ≤ ((M.slotStart S.C s_m : ℕ) : ℝ) := by
        have : M.slotStart S.C s₃ + 4 * Δ S ≤ M.slotStart S.C s_m := by omega
        exact_mod_cast this
      obtain ⟨k, hk, -, hk2⟩ := E.tick_of_active (M.voteTime S.C s₃) (by omega) u (fun j h1 h2 => by
        rw [hvt₃R] at h1 h2
        exact huA j (le_trans (by linarith) (R.time_le_succ j)) (by linarith))
      rw [hvt₃R] at hk2
      exact ⟨k, hk, ((lt_of_time_lt M) x R (by linarith)).le⟩
  have hkRt := (E.tick_active kR u _ hkR).2
  rw [hvt₃R] at hkRt
  have htkR : x.time kR ≤ x.time i₁ := htime hkRi
  have hTk : x.tickStep u (M.voteTime S.C s₃) = kR := (tickStep_eq_of_lbl M) x E hkR
  have hFu : (x.st kR u).finalized.AncestorEq B₃ := by
    have h := hF₃ u (by rw [hTk]; exact hkR)
      (Activity.not_mem_corruptedAtTime.2 fun j hj => hu_at j (le_trans hj (by rw [hTk]; exact htkR)))
    simp only [Trace.tickInput, hTk] at h
    exact h
  have hFw : (x.st kR u).finalized.compatible B₃ = true := (compatible_iff _ _).2 (Or.inl hFu)
  have hRootsR : RootsNameBlocksUntil M A x (x.time kR) :=
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) htkR hRoots
  have hwin : ∀ j : ℕ, (tGAT : ℝ) ≤ x.time j → j ≤ kR → u ∈ A.active j := fun j h1 h2 =>
    huA j (le_trans h1 (R.time_le_succ j)) (le_trans (htime h2) htkR)
  -- the proposer `p`, honest up to the support cutoff of slot `s₃`, is active from `tGAT` up to it, and ticks to the
  -- vote time of slot `s₃` at `kV`, where its finalized block is `B₃` or an ancestor of `B₃`
  have hp_at : ∀ j : ℕ, x.time j ≤ ((M.supportCutoff S.C s₃ : ℕ) : ℝ) → p ∉ A.corrupted j :=
    Activity.not_mem_corruptedAtTime.1 hp
  have hpA : ∀ j : ℕ, x.time j ≤ ((M.supportCutoff S.C s₃ : ℕ) : ℝ) → (tGAT : ℝ) ≤ x.time (j + 1) →
      p ∈ A.active j := fun j h1 h2 =>
    Activity.mem_active.2 ⟨hAwake j p (le_trans h1 hcs₃E) h2 (hp_at j h1), hp_at j h1⟩
  obtain ⟨kV, hkV, hkV1, hkV2⟩ := E.tick_of_active (M.voteTime S.C s₃) (by omega) p (fun j h1 h2 => by
    rw [hvt₃R] at h1 h2
    exact hpA j (by rw [hcs₃R]; linarith) (le_trans (by linarith) (R.time_le_succ j)))
  rw [hvt₃R] at hkV1 hkV2
  have hTkV : x.tickStep p (M.voteTime S.C s₃) = kV := (tickStep_eq_of_lbl M) x E hkV
  have hFp : (x.st kV p).finalized.AncestorEq B₃ := by
    have h := hF₃ p (by rw [hTkV]; exact hkV)
      (Activity.not_mem_corruptedAtTime.2 fun j hj => hp_at j (by rw [hTkV] at hj; rw [hcs₃R]; linarith))
    simp only [Trace.tickInput, hTkV] at h
    exact h
  -- `p`'s tick to the start of slot `s₃`, the step `kP` (`0` when `p` has none)
  obtain ⟨kP, hkPd⟩ : ∃ kP, x.tickStep p (M.slotStart S.C s₃) = kP := ⟨_, rfl⟩
  have hHeld' : B₃ ∈ (x.st (kP + 1) p).tree := by
    have h := hHeld
    simp only [Trace.tickOutput, hkPd] at h
    exact h
  rw [hkPd] at hAct₃
  have hkPl : (∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s₃)) →
      x.lbl kP = Event.tick p (M.slotStart S.C s₃) := by
    intro hex
    rw [← hkPd]; unfold Trace.tickStep; rw [dif_pos hex]; exact Nat.find_spec hex
  have hkP0 : (¬ ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s₃)) → kP = 0 := by
    intro hex
    rw [← hkPd]; unfold Trace.tickStep; rw [dif_neg hex]
  have hkPV : kP ≤ kV := by
    by_cases hex : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s₃)
    · have h := (E.tick_active kP p _ (hkPl hex)).2.2
      exact ((lt_of_time_lt M) x R (by linarith)).le
    · rw [hkP0 hex]; exact Nat.zero_le _
  -- `B₃`'s slot is at most `s₃`: `p` holds it after its tick to the vote time of slot `s₃`
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have hslotV : S.C.slot ((M.voteTime S.C s₃ : ℕ) : Int) = s₃ :=
    hsl _ ▸ (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S
      (show M.slotStart S.C s₃ ≤ M.voteTime S.C s₃ by omega)
      (show M.voteTime S.C s₃ < M.slotStart S.C (s₃ + 1) by omega)
  have hBs : B₃.slot ≤ s₃ := by
    have h := (slot_le_clockValue_of_mem_tree M F) R E (E.not_mem_corrupted_succ_of_tick hkV)
      ((mem_T_mono M F) x R E p (show kP + 1 ≤ kV + 1 by omega) hHeld')
    rw [x.clockValue_succ_of_tick hkV, hslotV] at h
    exact h
  -- `B₃` in `u`'s tree at `kR`
  have hB₃R : B₃ ∈ (x.st kR u).tree := by
    by_cases hg : B₃ = Block.genesis
    · rw [hg]
      exact (GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F) S A x R E kR u
    -- sent by `p` at a step `i` from `kP` on: the delivery promise, `u` active from the send (`hAct₃`)
    have hsend : ∀ i : ℕ, kP ≤ i →
        (⟨p, NamedObject.block B₃⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i →
        p ∉ A.corrupted i → B₃ ∈ (x.st (i + 1) p).tree →
        x.time (i + 1) ≤ ((M.slotStart S.C s₃ : ℕ) : ℝ) + ΔClockBehind → B₃ ∈ (x.st kR u).tree := by
      intro i hi hs hpi hBp hTi1
      have hpi1 : p ∉ A.corrupted (i + 1) := hp_at (i + 1) (by rw [hcs₃R]; linarith)
      have hmax : max (x.time (i + 1)) ((GST : ℕ) : ℝ) ≤ ((M.slotStart S.C s₃ : ℕ) : ℝ) + ΔClockBehind :=
        max_le hTi1 (by linarith)
      exact (proposal_held_by_receiver_of_ticks M F U) S A x R s₃ i (x.tickStep u (M.slotStart S.C s₃)) kR B₃ p u
        E hSkew hRedeliver hRootsR hParent hTick₃ hkR
        (fun j h1 h2 => hAct₃ j (by omega) (by rw [hTk]; exact h2)) hpi hpi1 hTi1 hs hBp hBs
        (d := max (x.time (i + 1)) ((GST : ℕ) : ℝ) + (ΔNet : ℝ)) rfl (by rw [hvt₃R]; linarith) hFw
    obtain ⟨ie, hie, hsende, hhone, -, hie1⟩ := (tree_block_relayed_entry M F) x R E hHeld' hg
    by_cases hex : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s₃)
    · have hkP := hkPl hex
      have hkPt := (time_of_lbl_tick M) x R E hkP
      by_cases hin : B₃ ∈ (x.st kP p).tree
      · -- held at `p`'s tick to the start of slot `s₃`: the relay at ticks
        have hsb : x.stepBefore tGAT ≤ kV := by
          rcases Nat.eq_zero_or_pos tGAT with h0 | h0
          · rw [h0, (stepBefore_zero M) x R]
            exact Nat.zero_le _
          · exact ((stepBefore_lt_of_le_time M) x R E h0 (by linarith)).le
        have hFa : (x.st (x.stepBefore tGAT) p).finalized.compatible B₃ = true :=
          (compatible_iff _ _).2 (Or.inl (ancestorEq_trans ((F_ancestorEq_of_le M F) x R E p hsb) hFp))
        have hu₀ : p ∈ A.activeThroughout x tGAT (tGAT + Δs) := by
          refine Activity.mem_activeThroughout.2 fun j h1 h2 => hpA j ?_ h2
          push_cast at h1
          rw [hcs₃R]; linarith
        have hDc₂ : M.slotStart S.C B₃.slot ≤ M.slotStart S.C s₃ :=
          (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hBs
        exact (block_at_tick_of_held_tick M F U) S A x R GST (M.voteTime S.C s₃) (M.slotStart S.C s₃) kP tGAT
          (M.voteTime S.C s₃) (M.slotStart S.C s₃) kR (x.tickStep u (M.slotStart S.C s₃)) p u B₃
          (E.upTo _) hNet hSkew hRedeliver (Sy.upTo _) hRootsR hParent hGST htGAT (by omega) le_rfl hu₀ hkP hin hFa
          hg hkR hwin hTick₃ (by omega) hDc₂ hFw
      · -- put on the wire at `kP`
        have hieq : kP ≤ ie := by
          by_contra hc
          exact hin ((mem_T_mono M F) x R E p (show ie + 1 ≤ kP by omega) hie1)
        have hie' : ie = kP := by omega
        subst hie'
        exact hsend ie le_rfl hsende hhone hie1 hkPt.2.2
    · -- `p` has no tick to the start of slot `s₃`: `B₃` was put on the wire at the step `0`, at time `0`
      have hk0 := hkP0 hex
      rw [hk0] at hie
      have hie0 : ie = 0 := by omega
      subst hie0
      have hne : x.lbl 0 ≠ Event.other := by
        intro h
        rcases E.other_sent 0 _ h hsende with h' | ⟨h', -⟩
        · rw [R.sent_zero] at h'
          exact absurd h' (Multiset.notMem_zero _)
        · exact hhone h'
      have hT1 : x.time (0 + 1) = 0 := by rw [R.time_keep 0 hne, R.time_zero]
      have hss0 : (0 : ℝ) ≤ ((M.slotStart S.C s₃ : ℕ) : ℝ) := Nat.cast_nonneg _
      exact hsend 0 (by omega) hsende hhone hie1 (by rw [hT1]; linarith)
  have hB₃ : B₃ ∈ (x.st i₁ u).tree := (mem_T_mono M F) x R E u hkRi hB₃R
  exact (caches_at_handover_of_mem M F U Fx) S A x R tAwakeEnd s₀ H i₁ B₃ u E hRoots hThird hti hJ hCerts hB₃ huT

/-- **A voter honest at its tick to a later vote time is active from an opening's proposal tick.** For a
validator `u` that ticks to the vote time of slot `s_m` and is outside the adversary set at that tick's real
time, a slot `s₃ ≤ s_m` whose start is at least one delay after `tGAT`, the proposer `p`'s tick to the start of
slot `s₃`, and the phase up to `tAwakeEnd`, at least the support cutoff of slot `s_m`: `u` is active after every
step from `p`'s tick to its own tick to the vote time of slot `s₃`, and `u` ticks to the start of slot `s₃`.

Why: every step up to `u`'s tick to the vote time of slot `s_m` is at a real time at most that tick's, so `u`
is outside the adversary set there; `hAwake` makes `u` awake at every such step from a time at least `tGAT`
on. `u`'s tick to the vote time of slot `s₃` is not after its tick to the vote time of slot `s_m`: a later
tick would be by `u` active there (`tick_active`), so its clock value would be at least the vote time of slot
`s_m` (`clock_mono`), equal to it, and the two ticks would be one step (`tick_unique`). Every step whose real
time is within the clock bounds of the start of slot `s₃` is before `u`'s tick to the vote time of slot `s_m`
(one delay apart, `hSkew`), so `u` is active there and ticks to that start (`tick_of_active`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `R`, `E`: the run's facts and the environment's facts; `tGAT`, `tAwakeEnd`: the phase; `s₃`, `s_m`: the
  slots; `p`: the proposer of slot `s₃`; `u`: the voter.

Read aloud: a validator honest at its tick to the vote time of slot `s_m` is active from the tick of slot
`s₃`'s proposer to its own tick to the vote time of slot `s₃`, and ticks to the start of slot `s₃`. -/
theorem voter_active_from_opening (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) {tGAT tAwakeEnd s₃ s_m : ℕ} {p u : V}
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hs₃ : s₃ ≤ s_m) (hGAT : tGAT + Δ S ≤ M.slotStart S.C s₃)
    (hEnd : M.supportCutoff S.C s_m ≤ tAwakeEnd)
    (hp : x.lbl (x.tickStep p (M.slotStart S.C s₃)) = Event.tick p (M.slotStart S.C s₃))
    (hu : x.lbl (x.tickStep u (M.voteTime S.C s_m)) = Event.tick u (M.voteTime S.C s_m))
    (hhon : u ∉ A.corruptedAtTime x (x.time (x.tickStep u (M.voteTime S.C s_m)))) :
    (∀ j : ℕ, x.tickStep p (M.slotStart S.C s₃) ≤ j → j ≤ x.tickStep u (M.voteTime S.C s₃) →
      u ∈ A.active j) ∧
    x.lbl (x.tickStep u (M.slotStart S.C s₃)) = Event.tick u (M.slotStart S.C s₃) := by
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hvt3 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s₃
  have hvtm := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s_m
  have hscm := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s_m
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hs₃
  have hvle : M.voteTime S.C s₃ ≤ M.voteTime S.C s_m := by omega
  -- the times, over the reals
  have hGATR : (tGAT : ℝ) + Δ S ≤ ((M.slotStart S.C s₃ : ℕ) : ℝ) := by exact_mod_cast hGAT
  have hssR : ((M.slotStart S.C s₃ : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C s_m : ℕ) : ℝ) := by
    exact_mod_cast (show M.slotStart S.C s₃ + Δ S ≤ M.voteTime S.C s_m by omega)
  have hvmR : ((M.voteTime S.C s_m : ℕ) : ℝ) + Δ S ≤ (tAwakeEnd : ℝ) := by
    exact_mod_cast (show M.voteTime S.C s_m + Δ S ≤ tAwakeEnd by omega)
  set i₁ := x.tickStep u (M.voteTime S.C s_m) with hi₁
  have ht₁ := (E.tick_active _ _ _ hu).2
  have htp := (E.tick_active _ _ _ hp).2
  -- `u` is outside the adversary set, and active from a time at least `tGAT` on, at every step up to `i₁`
  have hact : ∀ j : ℕ, j ≤ i₁ → (tGAT : ℝ) ≤ x.time (j + 1) → u ∈ A.active j := by
    intro j hj ht
    have hc : u ∉ A.corrupted j :=
      (Activity.not_mem_corruptedAtTime.1 hhon) j ((time_mono M) x R hj)
    have htj : x.time j ≤ (tAwakeEnd : ℝ) := by
      have := (time_mono M) x R hj
      linarith
    exact Finset.mem_sdiff.2 ⟨hAwake j u htj ht hc, hc⟩
  refine ⟨fun j hpj hj => ?_, ?_⟩
  · -- `u`'s tick to the vote time of slot `s₃` is not after `i₁`
    have hj₁ : j ≤ i₁ := by
      by_contra hlt
      push_neg at hlt
      by_cases hex : ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s₃)
      · obtain ⟨k₃, hk₃⟩ := hex
        have hks := (tickStep_eq_of_lbl M) x E hk₃
        rw [hks] at hj
        have hc₃ : u ∉ A.corrupted k₃ := (Finset.mem_sdiff.1 (E.tick_active _ _ _ hk₃).1).2
        have hmono := E.clock_mono i₁ k₃ u _ _ (by omega) hc₃ (Or.inl hu) (Or.inl hk₃)
        have heq : M.voteTime S.C s₃ = M.voteTime S.C s_m := le_antisymm hvle hmono
        rw [heq] at hk₃
        have := E.tick_unique _ _ _ _ hk₃ hu
        omega
      · have h0 : x.tickStep u (M.voteTime S.C s₃) = 0 := by
          unfold Trace.tickStep
          rw [dif_neg hex]
        omega
    refine hact j hj₁ ?_
    have h1 := (time_mono M) x R (show x.tickStep p (M.slotStart S.C s₃) ≤ j + 1 by omega)
    linarith [htp.1]
  · -- every step within the clock bounds of the start of slot `s₃` is before `i₁`
    have h1 : 1 ≤ M.slotStart S.C s₃ := by omega
    obtain ⟨k, hk, -⟩ := E.tick_of_active (M.slotStart S.C s₃) h1 u fun i hlo hhi => by
      have hi : i < i₁ := (lt_of_time_lt M) x R (by linarith [ht₁.1])
      refine hact i hi.le ?_
      have := (time_mono M) x R (Nat.le_succ i)
      linarith
    rw [(tickStep_eq_of_lbl M) x E hk]
    exact hk

/-! ## The hand-over -/

/-- **The hand-over after the fast block (part C's assembly).** The proof; the audited statement
is in `Statements/Executions/Lemma89Statements.lean`. The update of `v` at the action time is an
outcome `(n', sent)` of `v`'s tick there with `L` among the fast blocks of `n'` (template A2),
without A2's hypothesis that `v` has been awake since the duty window's start of slot `r * R + 1`:
`hAwake`, `hAnchor` and `hv` give it, as for `fast_block_base`'s twin. Why: with no root collision
at an honest round opening slot, every honest round opening slot has its proposal `B_i`, of its slot
and held by its proposer (`opening_proposal_exists`, `opening_proposal_held`); `s₀ := s_j`,
`B₀ := B_j`; C1 and C3 (their copies) at `j` give the base, the saved `B₀` and `B₀.slot = s₀`; the
old attestations are at most `h(B₀)` (`old_attestations_at_opening`), passed on as they are; C7
gives the frames for `s₀ < s < s_m`; C4 (its copy) at `j` and `j + 1` gives
`B_j ⪯ B_{j+1} ⪯ B_{j+2}`, each one height higher, and the justification clause at `j + 1`;
`B_{j+1}`'s entry is a strict descendant of `B_j`, so `HonestOpeningSeq.spacing` at `j` and the
tree's slot order give C5's hypotheses, and `h_j(B_{j+2}) ≥ h(B_{j+1}) ≥ h(B₀) + 1`; C6 (its copy) the caches at the threshold `h(B₀)`, its certificates on the honest chain
from `s₀`, at a slot whose update ran by `x[i₁].time`, by `cert_entry_at_slot` (Lemma 83's route
with Lemma 82 (b), the old attestations at most `h(B₀)` before the support cutoff of slot `s₀ + 1`),
the finalized blocks on `B_{j+2}` by `F_before_vote_ancestor_proposal`.

Roots name blocks until `M.supportCutoff S.C (rs m * S.C.R)`: the bundle `PartAHyps` is built with
its end time `M.supportCutoff S.C (rs m * S.C.R)`; C4 at the honest round opening slots `j` and
`j + 1`, C1, C3, C6 and C7 read up to that time.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: the first honest round opening slot a `k + 2`-slot wait after the fast block is the
healed round, and the two honest round opening slots after it bring the justification above `h(B₀)`
to every honest validator by the vote time of the last honest round opening slot. -/
theorem handover_after_fast_block (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m r H₂ : ℕ) (rs : ℕ → ℕ) (v : V)
    (L : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot before the last, the members of its round are active through the
    -- attestations' sync delay after the later of its duty window's start and `GST`, C4's row at that slot
    --
    (hHoldF : ∀ i, i < m → ∀ w ∈ Hon M S A x (rs i * S.C.R),
      w ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (rs m * S.C.R)))
    -- roots name blocks up to the real time of every tick to a clock value at most the support cutoff of slot
    -- `rs m * R` (, stops_recheck_85)
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (rs m * S.C.R) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    -- every tick to a clock value at most the support cutoff of slot `rs m * R` is at a real time at most
    -- `tAwakeEnd` (, stops_recheck_85)
    (hEndTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (rs m * S.C.R) →
      x.time k ≤ tAwakeEnd)
    -- the climb's output
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n') (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (j : ℕ) (hj2 : j + 2 ≤ m) (hsj : r * S.C.R + S.C.k + 2 ≤ rs j * S.C.R) :
    RootCollisionAtOpening M S A x rs m ∨
    (∃ (j' s₀ : ℕ) (B₀ : Block V),
      j' < m ∧ s₀ = rs j' * S.C.R ∧
      HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀ ∧
      (∀ u ∈ updaterAt M S A x s₀,
        (x.tickOutput u (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀) ∧
      B₀.slot = s₀ ∧
      OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) (M.chainStateOf S.C B₀).h ∧
      (∀ s : ℕ, s₀ < s → s < rs m * S.C.R →
        (∀ w ∈ roundMembers M S A x (s + 1), VoterFrameOnChainAt M S A x s₀ s w) ∧
        (∀ v ∈ updaterAt M S A x s, UpdaterFinalizedOnChainAt M S A x s₀ s v)) ∧
      (∀ u : V, x.lbl (x.tickStep u (M.voteTime S.C (rs m * S.C.R))) = Event.tick u (M.voteTime S.C (rs m * S.C.R)) →
        u ∉ A.corruptedAtTime x (x.time (x.tickStep u (M.voteTime S.C (rs m * S.C.R)))) →
        CachesOnChain M S A x s₀ (M.chainStateOf S.C B₀).h (x.tickInput u (M.voteTime S.C (rs m * S.C.R))))) := by
  classical
  by_cases hNoCol : RootCollisionAtOpening M S A x rs m
  · exact Or.inl hNoCol
  right
  have hk := S.C.k_ge_two
  have hR := S.C.R_ge_two
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hcm := fun {a b : ℕ} (h : a ≤ b) =>
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h
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
  have hEndO : ∀ i, i ≤ m → M.supportCutoff S.C (rs i * S.C.R) ≤ tAwakeEnd := fun i hi =>
    le_trans (hcm (hle i m hi le_rfl)) hSeq.last
  have hEndP : ∀ i, i ≤ m → M.supportCutoff S.C (rs i * S.C.R) ≤ M.supportCutoff S.C (rs m * S.C.R) :=
    fun i hi => hcm (hle i m hi le_rfl)
  have hRootsP : ∀ {t : ℕ}, t ≤ M.supportCutoff S.C (rs m * S.C.R) → RootsNameBlocksUntil M A x t := fun h =>
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (by exact_mod_cast h) hRoots
  have hjm := hle j m (by omega) le_rfl
  -- the bundle with its end time `M.supportCutoff S.C (rs m * S.C.R)`
  have P := (PartAHyps.of_tick M F U) (tAwakeEnd := M.supportCutoff S.C (rs m * S.C.R)) R E hNet hSkew hRedeliver Sy
    hΔs hRoots hParent hGST (hThird.mono (by exact_mod_cast hSeq.last))
    (fun i u hi => hAwake i u (le_trans hi (by exact_mod_cast hSeq.last)))
    (fun s h1 h2 => hActive s h1 (le_trans h2 hSeq.last)) (hCommittees.mono M hSeq.last) hAnchor hOld hv hUpdate hFast hL
    (hcm (show r * S.C.R + 2 ≤ rs m * S.C.R by omega))
  -- the proposals
  have hP : ∀ i, i ≤ m → ∃ B : Block V, ProposalAt M S x (rs i * S.C.R) B :=
    fun i hi => (opening_proposal_exists M F U) S A x R tGAT tAwakeEnd m i rs E hAwake hSkew hSeq hi
  let Bf : ℕ → Block V := fun i =>
    if hi : i ≤ m then Classical.choose (hP i hi) else Block.genesis
  have hBf : ∀ i (hi : i ≤ m), ProposalAt M S x (rs i * S.C.R) (Bf i) := by
    intro i hi
    simp only [Bf, dif_pos hi]
    exact Classical.choose_spec (hP i hi)
  have hnc : ∀ i, i ≤ m → ¬ RootCollisionAtProposal M S A x (rs i * S.C.R) (Bf i) :=
    fun i hi h => hNoCol (((GoldilocksCorrectness.Record.Proofs.View.rootCollisionAtOpening_unfold M) x rs m).2
      ⟨i, hi, Bf i, hBf i hi, h⟩)
  have hheld : ∀ i (hi : i ≤ m), (Bf i).slot = rs i * S.C.R ∧
      Bf i ∈ (x.tickOutput (S.P.proposer (rs i * S.C.R)) (M.slotStart S.C (rs i * S.C.R))).tree :=
    fun i hi => (opening_proposal_held M F U) S A x R tGAT tAwakeEnd m i rs (Bf i) E hSeq hi hNoCol (hBf i hi)
  have hTC : ∀ i, TreeClosed M S.P S.X
      (x.tickOutput (S.P.proposer (rs i * S.C.R)) (M.slotStart S.C (rs i * S.C.R))) := fun i =>
    F.nd.nodeInvCore_treeClosed
      ((lem11_node_invariantCore_of_run M F) S x R
        (x.tickStep (S.P.proposer (rs i * S.C.R)) (M.slotStart S.C (rs i * S.C.R)) + 1)
        (S.P.proposer (rs i * S.C.R))).1
  -- C4 at the openings `j`, `j + 1`
  have hC4 : ∀ i, j ≤ i → i + 1 ≤ m →
      (Bf i).AncestorEq (Bf (i + 1)) ∧
      (M.chainStateOf S.C (Bf i)).h + 1 ≤ (M.chainStateOf S.C (Bf (i + 1))).h ∧
      ((M.chainStateOf S.C (Bf (i + 1)).parent).h = (M.chainStateOf S.C (Bf i)).h →
        (M.chainStateOf S.C (Bf (i + 1))).J = (M.chainStateOf S.C (Bf i)).T_h) ∧
      ∀ u ∈ Hon M S A x (rs i * S.C.R),
        (x.tickOutput u (M.supportCutoff S.C (rs i * S.C.R + 1))).savedConfirmation
          (rs i * S.C.R) = some (Bf i) := by
    intro i hji him
    rcases (opening_rises_after_fast_block_opening M F U Fx) S A x R GST tGAT tAwakeEnd r H₂ (rs i * S.C.R)
        (rs (i + 1) * S.C.R) v L (Bf i) (Bf (i + 1)) E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F (hHoldF i (by omega))
        (hRootsP (hEndP (i + 1) him))
        (fun k u c hk hc => hRootsTick k u c hk (le_trans hc (hEndP (i + 1) him))) hParent hGST hThird hAwake hActive hCommittees
        hAnchor hOld hv hL n' sent hUpdate
        hFast (le_trans hsj (hle j i hji (by omega))) (Dvd.intro_left _ rfl) (hss i (by omega))
        (hEndO (i + 1) him) (fun k u c hk hc => hEndTick k u c hk (le_trans hc (hEndP (i + 1) him)))
        (hSeq.honest i (by omega)) (hSeq.honest (i + 1) him)
        (hBf i (by omega)) (hBf (i + 1) him) with h | h
    · exact absurd h (hnc i (by omega))
    · exact h
  obtain ⟨h01, h01h, -, -⟩ := hC4 j le_rfl (by omega)
  obtain ⟨h12, h12h, h12J, -⟩ := hC4 (j + 1) (by omega) (by omega)
  rw [show j + 1 + 1 = j + 2 from rfl] at h12 h12h h12J
  have h0 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C (Bf j) (Bf j)).1.1
  -- C5 at the openings `j + 1` and `j + 2`
  have hT1 := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_T_h_spec M F) S.C (Bf (j + 1))
  have hB0T : (Bf j).AncestorEq (M.chainStateOf S.C (Bf (j + 1))).T_h := by
    rcases ancestorEq_compatible hT1.1 h01 with h | h
    · exfalso
      have := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C h
      rw [hT1.2] at this
      unfold Height at *
      omega
    · exact h
  have hB0ne : Bf j ≠ (M.chainStateOf S.C (Bf (j + 1))).T_h := by
    intro h
    have h' := hT1.2
    rw [← h] at h'
    unfold Height at *
    omega
  have hTmem : (M.chainStateOf S.C (Bf (j + 1))).T_h ∈
      (x.tickOutput (S.P.proposer (rs (j + 1) * S.C.R)) (M.slotStart S.C (rs (j + 1) * S.C.R))).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E
      (x.tickStep (S.P.proposer (rs (j + 1) * S.C.R)) (M.slotStart S.C (rs (j + 1) * S.C.R)) + 1)
      (S.P.proposer (rs (j + 1) * S.C.R)) _ _ (hheld (j + 1) (by omega)).2 hT1.1
  have hslotT := (slot_lt_of_ancestorEq_of_treeClosed_node M F) (hTC (j + 1)) hTmem hB0T hB0ne
  rw [(hheld j (by omega)).1] at hslotT
  have hsp := hSeq.spacing j hj2
  have hJ2 : (M.chainStateOf S.C (Bf (j + 1))).h ≤ (M.chainStateOf S.C (Bf (j + 2))).h_j := by
    refine (GoldilocksCorrectness.Record.Proofs.Routines.round_justified_of_spacing3 M F) S.C (Bf (j + 1)) (Bf (j + 2))
      h12 h12h ?_ ?_ ?_
    · rw [(hheld (j + 2) hj2).1]
      unfold Slot at *
      omega
    · intro Y hY hne
      exact (slot_lt_of_ancestorEq_of_treeClosed_node M F) (hTC (j + 2)) (hheld (j + 2) hj2).2 hY hne
    · intro hpar
      have hJ := h12J hpar
      refine ⟨?_, hJ⟩
      have hspec := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C (Bf (j + 2))
      by_cases hz : (M.chainStateOf S.C (Bf (j + 2))).h_j = 0
      · exfalso
        have hg := hspec.2.1 hz
        rw [hJ] at hg
        have h' := hT1.2
        rw [hg] at h'
        have hg1 : (M.chainStateOf S.C (Block.genesis : Block V)).h = 1 :=
          (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_genesis_h M F) S.C
        rw [hg1] at h'
        unfold Height at *
        omega
      · have h' := hspec.2.2 (Nat.one_le_iff_ne_zero.mpr hz)
        rw [hJ, hT1.2] at h'
        exact h'.symm
  -- the base facts at the healed round `s₀ := s_j`
  have hs₀ := hsj
  have hsj1 := hss j (by omega)
  have hEndj1 : M.supportCutoff S.C (rs j * S.C.R + 2) ≤ M.supportCutoff S.C (rs (j + 1) * S.C.R) := hcm (by omega)
  have hEnd₀ : M.supportCutoff S.C (rs j * S.C.R + 2) ≤ tAwakeEnd := le_trans hEndj1 (hEndO (j + 1) (by omega))
  have hEndP₀ : M.supportCutoff S.C (rs j * S.C.R + 2) ≤ M.supportCutoff S.C (rs m * S.C.R) :=
    le_trans hEndj1 (hEndP (j + 1) (by omega))
  have hp₀ := hSeq.honest j (by omega)
  have hBase := (round_base_after_fast_block_opening M F U Fx) S A x R GST tGAT tAwakeEnd r H₂ (rs j * S.C.R)
    v L (Bf j) E hNet hSkew hRedeliver Sy hΔs (hRootsP hEndP₀) hParent
    hGST hThird hAwake hActive hCommittees hAnchor hOld hv hL n' sent hUpdate hFast hs₀
    (Dvd.intro_left _ rfl) hEnd₀ hp₀ (hBf j (by omega)) (hnc j (by omega))
  obtain ⟨μA, hμA, hAsrc⟩ := P.anchor_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx
    (show r * S.C.R + S.C.k + 2 ≤ rs j * S.C.R by omega) (hEndP j (by omega)) hp₀
  have hGs1 : LineInv M S A x r H₂ (rs j * S.C.R - 1) :=
    P.lineInv_all M F R E hNet hSkew hRedeliver Sy hΔs U Fx _ (by
      rw [show rs j * S.C.R - 1 + 2 = rs j * S.C.R + 1 by omega]
      exact le_trans (hcm (show rs j * S.C.R + 1 ≤ rs j * S.C.R + 2 by omega)) hEndP₀)
  obtain ⟨hHCE, hSaved, hslot₀, -⟩ := (healed_round_base_of_prev_votes M F U Fx) S A x R GST tGAT tAwakeEnd
    (rs j * S.C.R) (Bf j) E hNet hSkew hRedeliver Sy hΔs
    (hRootsP (le_trans (hcm (show rs j * S.C.R + 1 ≤ rs j * S.C.R + 2 by omega)) hEndP₀)) hParent
    hGST hThird hAwake hActive hCommittees (by omega)
    (le_trans hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega)))
    (le_trans hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega)))
    hEnd₀ hp₀ (hBf j (by omega)) hBase (hnc j (by omega))
    (fun u hu vote hvote => (hGs1 μA _ hAsrc (by omega)).1.1 u (Finset.mem_inter.1 hu).2 vote hvote)
  -- the old attestations
  have hOA := P.old_attestations_at_opening M F R E hNet hSkew hRedeliver Sy hΔs U Fx
    (show r * S.C.R + S.C.k + 2 ≤ rs j * S.C.R by omega) (Dvd.intro_left _ rfl)
    (le_trans (hcm (show rs j * S.C.R + 1 ≤ rs j * S.C.R + 2 by omega)) hEndP₀) hp₀ (hBf j (by omega))
  -- `B₀`'s height is greater than `H₂`
  have hHB₀ : H₂ < (M.chainStateOf S.C (Bf j)).h := by
    obtain ⟨-, hPB⟩ := (proposal_slot_parent M F U) S A x R E (show 1 ≤ rs j * S.C.R by omega)
      (hBf j (by omega))
    have hLP := P.parent_extends_sources M F R E hNet hSkew hRedeliver Sy hΔs U Fx
      (show r * S.C.R + S.C.k + 2 ≤ rs j * S.C.R by omega)
      (hEndP j (by omega)) hp₀ (hBf j (by omega)) (r * S.C.R) L
      (P.source_L M F R U (le_trans (hcm (show r * S.C.R + 1 ≤ rs j * S.C.R by omega)) (hEndP j (by omega))))
      (by omega)
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C (ancestorEq_trans hLP hPB)
    rw [hL] at h1
    unfold Height at *
    omega
  -- the frames
  have hFrames := (frames_at_phase_slots M F U Fx) S A x R GST tGAT tAwakeEnd r H₂ (rs j * S.C.R)
    (rs m * S.C.R) v L E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent hGST hThird hAwake hActive
    hCommittees hAnchor hOld hv hL n' sent hUpdate hFast hs₀ hSeq.last hEndTick
  -- the caches at every validator's tick to the vote time of slot `rs m * R`
  have hm2 := hle (j + 2) m hj2 le_rfl
  have h4 : 4 * Δ S * healFrontSlots S = 4 * Δ S * S.C.k * 3 + 4 * Δ S := by
    unfold healFrontSlots; rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm 3 S.C.k, ← Nat.mul_assoc]
  have hss0 : M.slotStart S.C (rs 0 * S.C.R) ≤ M.slotStart S.C (rs (j + 2) * S.C.R) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (hle 0 (j + 2) (by omega) hj2)
  have hFirst := hSeq.first
  have hGAT₃ : tGAT + Δ S ≤ M.slotStart S.C (rs (j + 2) * S.C.R) := by omega
  --: the recovery delay after `tGAT` has elapsed by the vote time of slot `rs (j + 2) * R`
  have hΔsN : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have h : ((max (Δ S) Δs : ℕ) : ℝ) + 3 * Δ S < 4 * Δ S * S.C.k := by
      push_cast
      linarith
    exact_mod_cast h
  have htGAT : tGAT + max (Δ S) Δs ≤ M.voteTime S.C (rs (j + 2) * S.C.R) := by
    have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (rs (j + 2) * S.C.R)
    rcases max_choice (Δ S) Δs with hm | hm <;> rw [hm] at hΔsN ⊢ <;> omega
  have hcut₀ : ((M.supportCutoff S.C (rs j * S.C.R + 1) : ℕ) : ℝ) ≤ (tAwakeEnd : ℝ) := by
    exact_mod_cast le_trans (hcm (show rs j * S.C.R + 1 ≤ rs j * S.C.R + 2 by omega)) hEnd₀
  have hQ := (fewerThanQuorum_of_fewerThanThird M F) A x tAwakeEnd hThird
  have hvtc : M.voteTime S.C (rs m * S.C.R) ≤ M.supportCutoff S.C (rs m * S.C.R) := by
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (rs m * S.C.R)
    omega
  have hkp : x.lbl (x.tickStep (S.P.proposer (rs (j + 2) * S.C.R)) (M.slotStart S.C (rs (j + 2) * S.C.R))) =
      Event.tick (S.P.proposer (rs (j + 2) * S.C.R)) (M.slotStart S.C (rs (j + 2) * S.C.R)) := by
    obtain ⟨i, hl, -⟩ := hBf (j + 2) hj2
    rw [(tickStep_eq_of_lbl M) x E hl]
    exact hl
  have hCaches : ∀ u : V,
      x.lbl (x.tickStep u (M.voteTime S.C (rs m * S.C.R))) = Event.tick u (M.voteTime S.C (rs m * S.C.R)) →
      u ∉ A.corruptedAtTime x (x.time (x.tickStep u (M.voteTime S.C (rs m * S.C.R)))) →
      CachesOnChain M S A x (rs j * S.C.R) (M.chainStateOf S.C (Bf j)).h
        (x.tickInput u (M.voteTime S.C (rs m * S.C.R))) := by
    intro u hu hhon
    have hti : x.time (x.tickStep u (M.voteTime S.C (rs m * S.C.R))) ≤ (tAwakeEnd : ℝ) :=
      hEndTick _ u _ hu hvtc
    obtain ⟨hAct₃, hTick₃⟩ := (voter_active_from_opening M F U) S A x R E hSkew hAwake hm2 hGAT₃ hSeq.last hkp hu hhon
    refine (caches_at_handover_of_held M F U Fx) S A x R GST tGAT tAwakeEnd (rs j * S.C.R)
      (M.chainStateOf S.C (Bf j)).h (rs (j + 2) * S.C.R) (rs m * S.C.R)
      (x.tickStep u (M.voteTime S.C (rs m * S.C.R))) (Bf (j + 2)) u
      E hNet hSkew hRedeliver Sy hΔs (hRootsTick _ u _ hu hvtc) hParent hGST hThird hAwake hm2 htGAT hSeq.last
      (hSeq.honest (j + 2) hj2) (hheld (j + 2) hj2).2 hAct₃ hTick₃
      (fun w hw _ => P.F_at_vote_tick_ancestor_proposal M F R E hNet hSkew hRedeliver Sy hΔs U Fx
        (show r * S.C.R + S.C.k + 2 ≤ rs (j + 2) * S.C.R by
          have := hle j (j + 2) (by omega) hj2
          omega)
        (hEndP (j + 2) hj2) (hSeq.honest (j + 2) hj2) (hBf (j + 2) hj2) hw)
      (by unfold Height at *; omega) ?_ hu hhon
    intro w D T h hD hJc hh
    have hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V)
        (max (x.time (x.tickStep u (M.voteTime S.C (rs m * S.C.R)))) (M.supportCutoff S.C (rs j * S.C.R + 1))) :=
      fun X hX => hQ X (fun v hv => let ⟨t'', h1, h2⟩ := hX v hv; ⟨t'', le_trans h1 (max_le hti hcut₀), h2⟩)
    exact (cert_entry_at_slot M F U Fx) S A x R (rs j * S.C.R) (M.chainStateOf S.C (Bf j)).h
      (x.tickStep u (M.voteTime S.C (rs m * S.C.R))) w D T h E hAdvQ hOA hD
      ((progressCertOn_of_justificationCertOn M F) hJc) hh
  exact ⟨j, rs j * S.C.R, Bf j, by omega, rfl, hHCE, hSaved, hslot₀, hOA,
    fun s h1 h2 => hFrames s h1 h2, hCaches⟩

end GoldilocksCorrectness.Record.Proofs.Executions

