module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.FinalityLivenessDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.FinalityLivenessKitStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealedAttestationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.FrameShapeStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.FinalityLivenessKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma90Inclusion
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PhaseKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma79
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Statements.Executions.FinalityLivenessDefs
public import GoldilocksCorrectness.Statements.Executions.FinalityLivenessKitStatements
public import GoldilocksCorrectness.Statements.Executions.HealedAttestationStatements
public import GoldilocksCorrectness.Statements.Executions.FrameShapeStatements
public import GoldilocksCorrectness.Proofs.Executions.FinalityLivenessKit
public import GoldilocksCorrectness.Proofs.Executions.Lemma90Inclusion
public import GoldilocksCorrectness.Proofs.Executions.PhaseKit
public import GoldilocksCorrectness.Proofs.Executions.Lemma79
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma94, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma94.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: no honest timeout after healing with the honest
chain read before a slot, and the frame and the targets of the members of an honest round opening
slot after the hand-over. The page's routine-level theorems are the facts' fields or have their
twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_mono dutyWindowStart_succ_le_slotStart
  one_le_Δ slotStart_eq slot_after_healed_round slot_le_of_supportCutoff_lt
  slot_lt_of_supportCutoff_le supportCutoff_eq voteTime_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

open GoldilocksCorrectness.Record.Statements.Routines (RecordConsistent)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject)
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-! ## No honest timeout, on the chain before a slot -/

/-- **`no_honest_timeout_after_healing` on the chain before a slot.** The statement of
`no_honest_timeout_after_healing` (`Statements/Executions/FinalityLivenessKitStatements.lean`) with
the honest confirmations forming a chain only before the slot `n`
(`ConfirmationsChainBefore M S Sched x s₀ n`), for an attestation sent at a time `t` at most the
support cutoff of slot `n`.

Why: the proof of `no_honest_timeout_after_healing`; the two attestations it compares are sent at
times at most `t`, at the support cutoff of slot `s' + 1` for the slot `s'` of the entry Lemma 82
names, so every such `s'` is less than `n`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `H`: the bound
  on the heights of the honest attestations sent before the healed round's action time; `n`: the
  bound on the slots of the chain;
- `i`: the step; `t`: its time; `v`: the validator; `a`: the attestation.

Read aloud: after healing, an honest attestation sent by the support cutoff of slot `n` at a height
greater than `H` is not a timeout, when the honest confirmations form a chain before slot `n`. -/
theorem no_honest_timeout_after_healing_before (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ H n i t : ℕ) (v : V) (a : Attestation V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hChain : ConfirmationsChainBefore M S A x s₀ n)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hl : x.lbl i = Event.tick v t) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ t)
    (htn : t ≤ M.supportCutoff S.C n)
    (hHon : v ∉ A.corruptedAtTime x t)
    (hSent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i)
    (hH : H < a.h) :
    a.τ = false := by
  induction i using Nat.strong_induction_on generalizing t a with
  | _ i ih =>
  by_contra hτ
  have hτ' : a.τ = true := by simpa using hτ
  -- `v` is outside the adversary set at its tick `i`, and from the healed round's action time on
  have hvi : v ∉ A.corrupted i := E.not_mem_corrupted_of_tick hl
  have hHonCut : v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1)) :=
    Activity.not_mem_corruptedAtTime.2 fun k hk =>
      Activity.not_mem_corruptedAtTime.1 hHon k (le_trans hk (by exact_mod_cast ht₀))
  -- the attestation is the one the client built from the validator's record
  obtain ⟨-, n', sent, hrun, ha⟩ := (tick_send_of_honestSendAt M F R E) hl hSent
  have hTI : x.tickInput v t = x.st i v := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput v t) := by
    rw [hTI]; exact (lem11_node_invariant M F S A x R E i v hvi).1
  obtain ⟨-, -, source, head, -, -, hca⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem49_tick_attests F) S.C S.P S.X _ n' _ sent a hrun
      hInvT ha
  obtain ⟨hah, haT, hcase⟩ :=
    GoldilocksCorrectness.Record.Proofs.Routines.create_attestation_timeout M F _ _ _ _ _ _ _ a hca.1 hτ'
  rw [hTI] at hcase
  have hΛ : GoldilocksCorrectness.Record.Statements.Routines.RecordConsistent M (x.st i v) := (recordConsistent_of_exec M F) S A x R E i v
  -- an earlier tick `j` of `v` is to a clock value at most `t`, so `v` is outside the adversary set
  -- up to it
  have hHonEarlier : ∀ (j t' : ℕ), j < i → x.lbl j = Event.tick v t' →
      v ∉ A.corruptedAtTime x t' := by
    intro j t' hj hl'
    have hle : t' ≤ t := E.clock_mono j i v t' t hj hvi (Or.inl hl') (Or.inl hl)
    exact Activity.not_mem_corruptedAtTime.2 fun k hk =>
      Activity.not_mem_corruptedAtTime.1 hHon k (le_trans hk (by exact_mod_cast hle))
  -- an earlier tick `j` of `v` is to a clock value at most `t`, so at most the support cutoff of `n`
  have htnEarlier : ∀ (j t' : ℕ), j < i → x.lbl j = Event.tick v t' →
      t' ≤ M.supportCutoff S.C n := fun j t' hj hl' =>
    le_trans (E.clock_mono j i v t' t hj hvi (Or.inl hl') (Or.inl hl)) htn
  -- an update slot whose support cutoff is at most that of `n` is less than `n`
  have hslot : ∀ σ : ℕ, M.supportCutoff S.C (σ + 1) ≤ M.supportCutoff S.C n → σ < n := by
    intro σ hσ
    by_contra hge
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_lt_of_lt M.toSlotLayout
      F.sched) S (show n < σ + 1 by omega)
    omega
  rcases hcase with htimeout | ⟨T', htarget, hne⟩
  · -- a timeout at the attestation's height was sent earlier, at a tick
    obtain ⟨c, hc, hch, hcτ⟩ := (hΛ.timeoutRec _).1 htimeout
    obtain ⟨j, t', a', hj, hl', -, hsent', -, hcont, -⟩ :=
      (record_content_sent_step M F) S A x R E v i c hc
    have hh' : a'.h = a.h := by
      rw [hah, ← hch]; exact congrArg AttestationContent.h hcont
    have hτa' : a'.τ = true := by
      rw [← hcτ]; exact congrArg AttestationContent.τ hcont
    rcases Nat.lt_or_ge t' (M.supportCutoff S.C (s₀ + 1)) with hlt | hge
    · -- before the healed round's action time its height is at most `H`
      have hle := hOld j t' v a' hl' (by exact_mod_cast hlt) hHonCut hsent'
      rw [hh'] at hle
      exact absurd hle (Nat.not_le.mpr hH)
    · -- from then on, it is a target by the induction
      have := ih j hj t' a' hl' hge (htnEarlier j t' hj hl') (hHonEarlier j t' hj hl') hsent' (by rw [hh']; exact hH)
      rw [hτa'] at this
      cases this
  · -- a target at the attestation's height for another block was sent earlier, at a tick
    obtain ⟨c, hc, hch, hcτ, hcT⟩ := (hΛ.targetRec _ _).1 htarget
    obtain ⟨j, t', a', hj, hl', -, hsent', -, hcont, -⟩ :=
      (record_content_sent_step M F) S A x R E v i c hc
    have hh' : a'.h = a.h := by
      rw [hah, ← hch]; exact congrArg AttestationContent.h hcont
    have hT' : a'.T = T' := by
      rw [← hcT]; exact congrArg AttestationContent.T hcont
    rcases Nat.lt_or_ge t' (M.supportCutoff S.C (s₀ + 1)) with hlt | hge
    · -- before the healed round's action time its height is at most `H`
      have hle := hOld j t' v a' hl' (by exact_mod_cast hlt) hHonCut hsent'
      rw [hh'] at hle
      exact absurd hle (Nat.not_le.mpr hH)
    · -- from then on, both attestations name the honest chain's entry at the height (Lemma 82b)
      obtain ⟨σ, E₁, C₁, hσ, htσ, hu₁, hS₁, hEC₁, hE2, hE3, hE4⟩ :=
        (lem82b_entry_at_slot M F U) S A x R s₀ i t v a E hl ht₀ hSent
      obtain ⟨σ', E₂, C₂, hσ', htσ', hu₂, hS₂, hEC₂, hE2', hE3', hE4'⟩ :=
        (lem82b_entry_at_slot M F U) S A x R s₀ j t' v a' E hl' hge hsent'
      -- two entries of the honest chain at one height are one block
      have hEE : E₁ = E₂ := by
        have hheq : (M.chainStateOf S.C E₁).h = (M.chainStateOf S.C E₂).h := by rw [hE3, hE3', hh']
        rcases (compatible_iff E₁ E₂).1
            ((onHonestChainBefore_compatible M F) S A x s₀ n E₁ E₂ hChain
              ⟨σ, hslot σ (by rw [← htσ]; exact htn), hσ, v, hu₁, C₁, hS₁, hEC₁⟩
              ⟨σ', hslot σ' (by rw [← htσ']; exact htnEarlier j t' hj hl'), hσ', v, hu₂, C₂, hS₂, hEC₂⟩) with h | h
        · have := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C E₁ E₂).2.2.2.2
            h hheq
          unfold GoldilocksCorrectness.Record.Statements.Routines.IsEntry at hE2 hE2'
          rw [hE2, hE2'] at this
          exact this
        · have := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C E₂ E₁).2.2.2.2
            h hheq.symm
          unfold GoldilocksCorrectness.Record.Statements.Routines.IsEntry at hE2 hE2'
          rw [hE2, hE2'] at this
          exact this.symm
      apply hne
      rw [← hT', hE4', ← hEE, ← hE4, haT]

/-! ## The round's members: the frame at the action time -/

/-- **Kit theorem, the frame of a member of the round at its action time.** For an honest round
opening slot `s` after the hand-over step `i₂` whose proposer's tick put `B` on the wire, with no
block the proposer held before `t_s` having `B`'s root, and a member `u` of
`honestActiveAt M S Sched s`: every block on the honest chain before slot `s` is `B` or an ancestor
of `B`; `B` is of slot `s`; every updater of slot `s` saves `B` as its confirmation of slot `s`;
`H < h(B)`; some outcome of `u`'s tick at the support cutoff `a` of slot `s + 1`, from a state awake
for slot `s + 1`, saves `B` with `B` among its fast blocks; every lock entry live at the vote time
of slot `s + 1` that an outcome of `u`'s tick there leaves, from a state awake for slot `s + 1`, is
compatible with `B`; and on `u`'s state at its tick to `a` (its tick input, rule R3): the fork-choice root is `B` or an ancestor of
`B`, `head_height_floor` is at most `h(B)`, `B` is in the tree, and the cache `h_j` is less than
`h(B)`, or the record holds no lock at `h(B)`, or its lock there is the root of `T_h(B)`.

Why: the inclusion (`honest_proposal_saved_until`, `included_update_facts_q_until`,
`honest_proposal_extends_chain_until`) gives the chain, the update and the root. The FG state of
`u` before `a` is not contested (Lemma 91 (d)), so its `head_height_floor` is one less than the
greatest chain-state height `h'` of its tree; a block at `h'` with `h' − 1 > h(B)` would carry a
progress certificate at `h' − 1 > H` naming an entry of the chain before slot `s`
(`cert_entry_at_slot`), an ancestor of `B` of greater height. A lock at `h(B) = h_j` was written by
a finality pair `u` signed from a chain state of a block it held with that justification
(`lock_justified_of_exec`); its certificate names an entry of the chain before `s` at `h(B)` (Lemma
83), which is `T_h(B)` (Lemma 47 (e)).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `s`: the slot; `B`: the proposal; `u`: the member.

Read aloud: after the hand-over, a member of an honest round opening slot `s` saves the proposal `B`
fast at its update of slot `s + 1`, keeps its live locks compatible with `B`, and before that update
holds `B` with its root on `B`'s chain, its `head_height_floor` at most `B`'s chain-state height and
no lock at that height on another block. -/
theorem round_member_frame_after_healing (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₂ H s : ℕ) (B : Block V) (u : V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRootsU : ∀ v ∈ updaterAt M S A x s, RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQU : ∀ v ∈ updaterAt M S A x s, A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s + 1))) (hAnchor : anchor ≤ x.time i₂)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₂)
    (hChain : ConfirmationsChainBefore M S A x s₀ s)
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor M S A x (honestActiveAt M S A x s')
        (OnHonestChainBefore M S A x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ w ∈ honestActiveAt M S A x s',
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' w)
    (hLocks₀ : ∀ w ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ w)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCachesU : ∀ v ∈ updaterAt M S A x s, ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j →
      x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) → w ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j w))
    (hAfter : x.time i₂ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s) (M.slotStart S.C s) → x.time i₂ < x.time k)
    (hOpener : HonestOpenerAt M S A x s)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hNoCollision : ¬ RootCollisionAtProposal M S A x s B)
    (hHold : ∀ s' : ℕ, s - 1 ≤ s' → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hu : u ∈ honestActiveAt M S A x s) :
    (∀ C : Block V, OnHonestChainBefore M S A x s₀ s C → C.AncestorEq B) ∧
    B.slot = s ∧
    (∀ w ∈ updaterAt M S A x s,
      (x.tickOutput w (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B) ∧
    H < (M.chainStateOf S.C B).h ∧
    (∃ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput u (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) ∧
      AwakeFor M S.C (x.tickInput u (M.supportCutoff S.C (s + 1))) (s + 1) ∧
      M.savedConfirmation n' s = some B ∧ B ∈ M.fastBlocks n') ∧
    (∀ (n'' : M.N) (sent : List (NamedObject V)),
      .ok (n'', sent) ∈ M.tick S.C S.P S.X (x.tickInput u (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput u (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n'',
        M.is_live (x.tickInput u (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true) ∧
    (M.get_fc_root (x.tickInput u (M.supportCutoff S.C (s + 1)))).AncestorEq B ∧
    M.head_height_floor (x.tickInput u (M.supportCutoff S.C (s + 1))) ≤
      (M.chainStateOf S.C B).h ∧
    B ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).tree ∧
    ((x.tickInput u (M.supportCutoff S.C (s + 1))).justifiedHeight < (M.chainStateOf S.C B).h ∨
      (x.tickInput u (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h = none ∨
      (x.tickInput u (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h =
        some (M.chainStateOf S.C B).T_h.root) := by
  obtain ⟨hs2, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.slot_after_healed_round M.toSlotLayout F.sched) S
    s₀ s (by exact_mod_cast lt_of_le_of_lt ht₀ hAfter.1)
  obtain ⟨q, rfl⟩ : ∃ q, s = q + 2 := ⟨s - 2, by omega⟩
  obtain ⟨ip, hl, hsent⟩ := hPropose
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hsR : ∀ s' : ℕ, ((M.slotStart S.C s' : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (s' : ℝ) := fun s' => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s']; push_cast; ring
  have hvR : ∀ s' : ℕ, ((M.voteTime S.C s' : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (s' : ℝ) + Δ S := fun s' => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s',
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s']; push_cast; ring
  have hcR : ∀ s' : ℕ, ((M.supportCutoff S.C s' : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (s' : ℝ) + 2 * Δ S := fun s' => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s',
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s',
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s']; push_cast; ring
  have hmaxR : (Δ S : ℝ) ≤ max (Δ S : ℝ) (Δs : ℝ) := le_max_left _ _
  -- the inclusion at slot `q + 2`, with the rows read at each updater's own tick (T-RC86-1)
  have hLk := (locks_before_of_locks_le M F) S A x s₀ q (fun s' h₁ h₂ => hLocks s' h₁ (by omega))
    hLocks₀ (by omega)
  have hChainq : ConfirmationsChainBefore M S A x s₀ (q + 1) :=
    fun a b c d e f h1 h2 h3 => hChain a b c d e f h1 h2 (by omega)
  have hRootNew : ∀ B' ∈ (x.tickInput (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2))).tree,
      B'.root ≠ B.root := fun B' hB' hr => hNoCollision ⟨B', hB', hr⟩
  have hp : S.P.proposer (q + 2) ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C (q + 2))
        (M.supportCutoff S.C (q + 3)) ∧
      S.P.proposer (q + 2) ∉ A.corruptedAtTime x (M.supportCutoff S.C (q + 3)) :=
    ⟨hOpener.1, fun h => hOpener.2 (Finset.mem_union_left _ (Finset.mem_union_left _ h))⟩
  have hu' : u ∈ updaterAt M S A x (q + 2) := (honestActiveAt_subset_updaterAt M F) S A x R E (q + 2) hu
  obtain ⟨hChainB, hBslot, -, -, hSavedAll, hFrame, -⟩ := (honest_proposal_saved_until M F U Fx) S A x R GST
    s₀ anchor i₂ H q ip B E hNet hSkew hRedeliver Sy hΔs hRootsU hParent hAdvQU hSleepK hAnchor hGST hChainq hInv
    hLocks hOld hCachesU ht₀ (by omega) hAfter hLk (fun s' h₁ h₂ => hHold s' (by omega) h₂) hp hHoldP hl hsent
    hRootNew
  -- the caches at the steps after the hand-over step, up to `u`'s tick (the kit's index form)
  have hCachesUi : ∀ (j : ℕ) (w : V), i₂ < j →
      x.time j ≤ x.time (x.tickStep u (M.supportCutoff S.C (q + 2 + 1))) → w ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j w) :=
    fun j w hj h2 h3 => hCachesU u hu' j w ((time_mono M) x R hj.le) h2 h3
  obtain ⟨-, -, -, -, -, hBw, -⟩ := (honest_proposal_saved_at_until M F U Fx) S A x R GST s₀ anchor i₂ H q ip B u
    E hNet hSkew hRedeliver Sy hΔs hu' (hRootsU u hu') hParent (hAdvQU u hu') hSleepK hAnchor hGST hChainq hInv
    hLocks hOld hCachesUi ht₀ (by omega) hAfter hLk (fun s' h₁ h₂ => hHold s' (by omega) h₂) hp hHoldP hl
    hsent hRootNew
  obtain ⟨hSv₀, hFb₀, -, -, -⟩ := (included_update_facts_q_until M F U Fx) S A x R GST s₀ anchor i₂ H q ip B u
    E hNet hSkew hRedeliver Sy hΔs (hRootsU u hu') hParent (hAdvQU u hu') hSleepK hAnchor hGST hChainq hInv
    hLocks hOld hCachesUi ht₀ (by omega) hAfter hLk (fun s' h₁ h₂ => hHold s' (by omega) h₂) hp hHoldP hl
    hsent hRootNew hu'
  -- `u`'s tick to the support cutoff of slot `q + 3`, at the step `K`, and its outcome
  obtain ⟨K, hlK, -⟩ := Activity.mem_activeThroughoutToTick.1 hu'
  have hKs : x.tickStep u (M.supportCutoff S.C (q + 2 + 1)) = K := (tickStep_eq_of_lbl M) x E hlK
  have hin : x.tickInput u (M.supportCutoff S.C (q + 2 + 1)) = x.st K u := by unfold Trace.tickInput; rw [hKs]
  obtain ⟨τ, hτ, hτle⟩ := (tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hu'
    (by
      have hdwz : (Goldilocks.duty_window_start S.C (q + 2 + 1) : ℤ) ≤
          ((M.dutyWindowStart S.C (q + 2 + 1) : ℕ) : ℤ) := by
        rw [(GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_eq_toNat M.toSlotLayout F.sched U)]
        exact Int.self_le_toNat _
      have h := (dutyWindowStart_succ_lt_supportCutoff M F U) S (q + 2)
      have h' : ((M.dutyWindowStart S.C (q + 2 + 1) : ℕ) : ℤ) < ((M.supportCutoff S.C (q + 2 + 1) : ℕ) : ℤ) := by
        exact_mod_cast h
      exact lt_of_le_of_lt hdwz h')
  obtain ⟨n', sent', hrun', hAw', e1, e2, -, -⟩ :=
    (update_state_of_tick M F U) S A x R (q + 2) u E hlK ⟨τ, hτ, hτle⟩
  have hSv : M.savedConfirmation n' (q + 2) = some B := by rw [← e1]; exact hSv₀
  have hFb : B ∈ M.fastBlocks n' := by rw [← e2]; exact hFb₀
  obtain ⟨-, hρu, hRev⟩ := hFrame u hu'
  -- the real time of `K`: after the hand-over step, and at most `ΔClockBehind` after the cutoff
  obtain ⟨-, hK1, hK2⟩ := E.tick_active K u _ hlK
  have hiK : x.time i₂ ≤ x.time K := by
    have h1 := hAfter.1
    have h2 := hsR (q + 2)
    have h3 := hcR (q + 2 + 1)
    push_cast at h2 h3 h1 hK1
    linarith
  have hc0K : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) ≤ x.time K := le_trans ht₀ hiK
  have hmax : max (x.time K) ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) = x.time K := max_eq_left hc0K
  have hAdvK : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time K) := by rw [← hKs]; exact hAdvQU u hu'
  have hCK : ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j → x.time j ≤ x.time K → w ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j w) := by rw [← hKs]; exact hCachesU u hu'
  have huK : u ∉ A.corrupted K := E.not_mem_corrupted_of_tick hlK
  -- every tick before `K` to a support cutoff is for a slot at most `q + 2`
  have hbefore : ∀ (k : ℕ) (w : V) (s_a : ℕ), k < K → x.lbl k = Event.tick w (M.supportCutoff S.C (s_a + 1)) →
      s_a < q + 3 := by
    intro k w s_a hk hkl
    refine (slot_lt_of_tick_time M F) S E hkl ?_
    have h1 := (time_mono M) x R hk.le
    have h3 := hcR (q + 2 + 1)
    have h4 := hcR (q + 3 + 1)
    push_cast at h3 h4 hK2 ⊢
    linarith
  -- the honest chain before slot `q + 3` is on `B`'s chain, and the confirmations up to slot `q + 2` form one chain
  have hOnB : ∀ (σ : ℕ) (C : Block V), σ < q + 3 → OnHonestChainAt M S A x s₀ σ C → C.AncestorEq B := by
    intro σ C hσ hC
    rcases Nat.lt_or_ge σ (q + 2) with h | h
    · exact hChainB C ⟨σ, h, hC⟩
    · obtain rfl : σ = q + 2 := by omega
      obtain ⟨-, v, hv, C', hC', hCC'⟩ := hC
      rw [hSavedAll v hv] at hC'
      obtain rfl := Option.some.inj hC'
      exact hCC'
  have hChain3 : ConfirmationsChainBefore M S A x s₀ (q + 3) := by
    intro a b v v' C C' ha hab hb hv hv' hC hC'
    rcases Nat.lt_or_ge b (q + 2) with h | h
    · exact hChain a b v v' C C' ha hab h hv hv' hC hC'
    · obtain rfl : b = q + 2 := by omega
      rw [hSavedAll v' hv'] at hC'
      obtain rfl := Option.some.inj hC'
      refine ⟨fun hlt => hOnB a C (by omega) ⟨ha, v, hv, C, hC, ancestorEq_refl _⟩, fun heq => ?_⟩
      subst heq
      rw [hSavedAll v hv] at hC
      obtain rfl := Option.some.inj hC
      exact (compatible_iff _ _).2 (Or.inl (ancestorEq_refl _))
  -- Lemma 91 (d) at `K`: `u`'s FG state is not contested
  have hd := (lem91d_not_contested_until M F U Fx) S A x R s₀ K (q + 3) H u E (by rw [hmax]; exact hAdvK)
    hChain3 hOld (hCK K u hiK le_rfl huK) huK (fun s_a ⟨k, w, hk, hkl⟩ => hbefore k w s_a hk hkl)
  -- the caches of `u` and a witness of its justification
  obtain ⟨hHu, -, -, -, -⟩ := hCK K u hiK le_rfl huK
  obtain ⟨⟨D, hD, -, hDj⟩, ⟨X, hX, hXh⟩, -⟩ := (cachesWitnessed_of_exec M F) S A x R E K u
  have hDh : (M.chainStateOf S.C D).h ≤ hMax M S.C (x.st K u) := le_hMax M hD
  have hD47 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C D D).1.2.1
  have hjm : (x.st K u).justifiedHeight + 1 ≤ hMax M S.C (x.st K u) := by
    rw [hDj]
    omega_nat
  -- `head_height_floor` (the least chain-state height a viable block may have) is at most `h(B)`
  have hfloor : hMax M S.C (x.st K u) - 1 ≤ (M.chainStateOf S.C B).h := by
    by_contra hgt
    have hH1 : H < hMax M S.C (x.st K u) - 1 := by omega_nat
    obtain ⟨Y, hYX, -, -, -, -, hPC⟩ := (GoldilocksCorrectness.Record.Statements.Routines.lem67_first_advance M F) S.C X
      (hMax M S.C (x.st K u) - 1) (by omega_nat) (by rw [hXh]; omega_nat)
    have hYT : Y ∈ (x.st K u).tree :=
      (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E K u X Y hX hYX
    obtain ⟨s_a, uₐ, Eb, hka, hla, -, -, -, hAt, -, hEh, -⟩ := (cert_entry_at_slot M F U Fx) S A x R s₀ H K u Y _ _
      E (by rw [hmax]; exact hAdvK) hOld hYT hPC hH1
    have hEB := hOnB s_a Eb (hbefore _ uₐ s_a hka hla) hAt
    have := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Eb B).2.2.2.1 hEB
    rw [hEh] at this
    exact hgt this
  have hφ : M.head_height_floor (x.st K u) ≤ (M.chainStateOf S.C B).h := by
    rw [hd.2]; exact hfloor
  have hHB : H < (M.chainStateOf S.C B).h := by omega_nat
  -- `u` holds `B` from its tick to the vote time of slot `q + 2` on
  have hvote : ∃ k : ℕ, x.lbl k = Event.tick u (M.voteTime S.C (q + 2)) := by
    have hdw := duty_window_start_real S (q + 2)
    have h1 : 1 ≤ M.voteTime S.C (q + 2) := by
      have : (1 : ℝ) ≤ ((M.voteTime S.C (q + 2) : ℕ) : ℝ) := by
        rw [hvR]; have : (0 : ℝ) ≤ 4 * (Δ S : ℝ) * ((q + 2 : ℕ) : ℝ) := by positivity
        linarith
      exact_mod_cast this
    have hr := (mem_activeThroughoutToTick_of_inside M F) R E ((honestActiveAt_window M F) S A (q + 2) u E hu) h1
      (by rw [hdw, hvR]; push_cast; linarith) (by rw [hvR, hcR]; push_cast; linarith)
    obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 hr
    exact ⟨k, hk⟩
  obtain ⟨kv, hkv⟩ := hvote
  have hBin : B ∈ (x.tickInput u (M.supportCutoff S.C (q + 2 + 1))).tree := by
    have hB1 := hBw u hu
    have hvc : M.voteTime S.C (q + 2) < M.supportCutoff S.C (q + 2 + 1) := by
      have : ((M.voteTime S.C (q + 2) : ℕ) : ℝ) < ((M.supportCutoff S.C (q + 2 + 1) : ℕ) : ℝ) := by
        rw [hvR, hcR]; push_cast; linarith
      exact_mod_cast this
    have h12 := (tick_lt_of_clock_lt M) x E hkv hlK hvc
    unfold Trace.tickInput at hB1
    rw [(tickStep_eq_of_lbl M) x E hkv] at hB1
    rw [hin]
    exact ((grows_of_le M F) x R E u h12.le).1 hB1
  refine ⟨hChainB, hBslot, hSavedAll, hHB, ⟨n', sent', hrun', hAw', hSv, hFb⟩,
    fun n'' sent hrun hA e he hlv => (compatible_iff _ _).2 (Or.inl (hRev n'' sent hrun hA e he hlv)), hρu,
    by rw [hin]; exact hφ, hBin, ?_⟩
  rw [hin]
  -- the lock at `h(B)`
  by_cases hlt : (x.st K u).justifiedHeight < (M.chainStateOf S.C B).h
  · exact Or.inl hlt
  right
  cases hlk : (x.st K u).sentLock (M.chainStateOf S.C B).h with
  | none => exact Or.inl rfl
  | some T' =>
    right
    obtain ⟨j', hj', D', hD'T, h1', hD'j, hD'J⟩ := (lock_justified_of_exec M F) S A x R E K u _ T' hlk
    have hD'K : D' ∈ (x.st K u).tree := ((grows_of_le M F) x R E u hj'.le).1 hD'T
    have hcert := (((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D').1
      (hD'j ▸ h1')).1
    rw [hD'j] at hcert
    obtain ⟨s_a, Eb, ⟨k, w, hk, hkl⟩, hAt, hEe, hEh, hEr⟩ :=
      (lem83_one_justification_greater_than_threshold M F Fx) S A x R E s₀ (M.supportCutoff S.C (s₀ + 1)) H K
        u D' _ _ hAdvK ((lem82_honest_attestations_on_chain M F U) S A x R s₀ E)
        ((oldAttestationsAtMostHonestAt_of_le_time M F) S A x R E K hc0K hOld) hD'K hcert hHB
    have hEB := hOnB s_a Eb (hbefore k w s_a hk hkl) hAt
    have hTE : (M.chainStateOf S.C Eb).T_h = (M.chainStateOf S.C B).T_h :=
      ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Eb B).2.2.2.2 hEB hEh
    unfold IsEntry at hEe
    rw [← hD'J, hEr, ← hEe, hTE]

/-! ## The round's members: their targets -/

/-- **Kit theorem, the round's members' targets after healing (the part of Lemma 94 that holds).**
For an honest round opening slot `s = r * R` after the hand-over step `i₂` whose proposer's tick put
`B` on the wire, with no block the proposer held before `t_s` having `B`'s root, every member `u` of
`honestActiveAt M S Sched s` put on the wire, at a tick at a time at most the support cutoff of slot
`s + 1`, a target of its own at `B`'s height naming the root of `B`'s `T_h`.

Why: Lemma 61 over the frame of `round_member_frame_after_healing`: `u` attests at the action time,
or its record already holds an attestation at `h(B)` naming `T_h(B)`, sent at an earlier tick
(`record_content_sent`); either is a target, since `h(B) > H`
(`no_honest_timeout_after_healing_before`, the attestations read being sent at times at most the
support cutoff of slot `s + 1`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the round; `s`: its first slot; `B`: the proposal; `u`: the member.

Read aloud: after the hand-over, every member of an honest round opening slot `s` sends, by the
support cutoff of slot `s + 1`, an attestation of its own at `B`'s chain-state height naming the
root of `B`'s `T_h`. -/
theorem round_attesters_target_after_healing (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₂ H r s : ℕ) (B : Block V) (u : V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRootsU : ∀ v ∈ updaterAt M S A x s, RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQU : ∀ v ∈ updaterAt M S A x s, A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s + 1))) (hAnchor : anchor ≤ x.time i₂)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₂)
    (hChain : ConfirmationsChainBefore M S A x s₀ (s + 1))
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor M S A x (honestActiveAt M S A x s')
        (OnHonestChainBefore M S A x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ w ∈ honestActiveAt M S A x s',
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' w)
    (hLocks₀ : ∀ w ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ w)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCachesU : ∀ v ∈ updaterAt M S A x s, ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j →
      x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) → w ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j w))
    (hs : s = r * S.C.R) (hAfter : x.time i₂ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s) (M.slotStart S.C s) → x.time i₂ < x.time k)
    (hOpener : HonestOpenerAt M S A x s)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hNoCollision : ¬ RootCollisionAtProposal M S A x s B)
    (hHold : ∀ s' : ℕ, s - 1 ≤ s' → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hu : u ∈ honestActiveAt M S A x s) :
    ∃ (i t : ℕ) (a : Attestation V), x.lbl i = Event.tick u t ∧
      t ≤ M.supportCutoff S.C (s + 1) ∧
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i ∧
      a.val_index = u ∧ a.h = (M.chainStateOf S.C B).h ∧ a.T = (M.chainStateOf S.C B).T_h.root ∧
      a.τ = false := by
  obtain ⟨hs2, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.slot_after_healed_round M.toSlotLayout F.sched) S
    s₀ s (by exact_mod_cast lt_of_le_of_lt ht₀ hAfter.1)
  have hChain' : ConfirmationsChainBefore M S A x s₀ s :=
    fun a b c d e f h1 h2 h3 => hChain a b c d e f h1 h2 (by omega)
  obtain ⟨-, hBslot, -, hHB, ⟨n', sent, hrun, hAw, hSv, hFb⟩, hRev, hρ, hφ, hBin, hBox⟩ :=
    (round_member_frame_after_healing M F U Fx) S A x R GST s₀ anchor i₂ H s B u E hNet hSkew hRedeliver Sy hΔs
      hRootsU hParent hAdvQU hSleepK hAnchor hGST ht₀ hChain' hInv hLocks hLocks₀ hOld hCachesU
      hAfter hOpener hPropose hNoCollision hHold hHoldP hu
  have hv : u ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)) :=
    (honestActiveAt_subset_updaterAt M F) S A x R E s hu
  have hLk := (update_lock_entries_ancestorEq M F U) S A x R s B u E hSkew hv n' sent hrun hAw hSv hBslot hRev
  -- `u` is outside the adversary set up to the support cutoff of slot `s + 1`
  have huc : ∀ t : ℕ, t ≤ M.supportCutoff S.C (s + 1) → u ∉ A.corruptedAtTime x t := by
    intro t ht
    have h : u ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) :=
      fun h => (Finset.mem_sdiff.1 hu).2 (Finset.mem_union_left _ h)
    rw [Activity.not_mem_corruptedAtTime] at h ⊢
    intro i hi hc
    exact h i (le_trans hi (by exact_mod_cast ht)) hc
  have hc01 : M.supportCutoff S.C (s₀ + 1) ≤ M.supportCutoff S.C (s + 1) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  -- every attestation of `u` at `h(B)` up to the support cutoff of slot `s + 1` is a target
  have hτ : ∀ (j t' : ℕ) (a : Attestation V), x.lbl j = Event.tick u t' →
      t' ≤ M.supportCutoff S.C (s + 1) →
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j →
      a.h = (M.chainStateOf S.C B).h → a.τ = false := by
    intro j t' a hl ht' hsent hah
    rcases Nat.lt_or_ge t' (M.supportCutoff S.C (s₀ + 1)) with hlt | hge
    · have := hOld j t' u a hl (by exact_mod_cast hlt) (huc _ hc01) hsent
      rw [hah] at this
      exact absurd this (Nat.not_le.mpr hHB)
    · exact (no_honest_timeout_after_healing_before M F U) S A x R s₀ H (s + 1) j t' u a E
        hChain hOld hl hge ht' (huc t' ht') hsent (by rw [hah]; exact hHB)
  rcases (lem61_honest_validator_attests_frame M F U) S A x R r s B u _ _ E hs hv n' sent hrun hAw hSv
      hFb hLk ⟨rfl, rfl⟩ hρ hφ hBin hBox with ⟨i, a, hl, hsent, hav, hah, haT⟩ | ⟨b, hb, hbh, hbT⟩
  · exact ⟨i, _, a, hl, le_rfl, hsent, hav, hah, haT, hτ i _ a hl le_rfl hsent hah⟩
  · obtain ⟨j, t', a, hl, ht', -, hsent, hav, hac, -⟩ := (record_content_sent M F) S A x R _ u b E hb
    have hah : a.h = (M.chainStateOf S.C B).h := by
      rw [← hbh, ← hac]
      rfl
    have haT : a.T = (M.chainStateOf S.C B).T_h.root := by
      rw [← hbT, ← hac]
      rfl
    exact ⟨j, t', a, hl, ht'.le, hsent, hav, hah, haT, hτ j t' a hl ht'.le hsent hah⟩

/-! ## The proposer of an honest round opening slot (moved from `Lemma95.lean`, so that
`Lemma95.lean` can import `Lemma107.lean`) -/

/-- **Kit fact, the proposer of an honest round opening slot is an honest active validator of
it.** When the proposer of slot `q + 2` is awake and honest from the start of its proposal window
to the support cutoff of slot `q + 3`, it is in `honestActiveAt M S Sched (q + 2)`.

Why: the proposal window of slot `q + 2` starts at the duty window of slot `q + 1`, at or before
the duty window of slot `q + 2`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `q`: the slot is `q + 2`.

Read aloud: the proposer of an honest round opening slot is an honest active validator of it. -/
theorem opener_mem_honestActiveAt (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (q : ℕ) (hOpener : HonestOpenerAt M S A x (q + 2)) :
    S.P.proposer (q + 2) ∈ honestActiveAt M S A x (q + 2) := by
  obtain ⟨hr, hh⟩ := hOpener
  have hpw : proposal_window_start S.C (q + 2) ≤ duty_window_start S.C (q + 2) := by
    rw [GoldilocksCorrectness.Proofs.Routines.proposal_window_start_eq S q]
    have h1 := duty_window_start_real S (q + 1)
    have h2 := duty_window_start_real S (q + 2)
    have hΔ : (0 : ℝ) ≤ (Δ S : ℝ) := by positivity
    have : ((duty_window_start S.C (q + 1) : ℤ) : ℝ) ≤ ((duty_window_start S.C (q + 2) : ℤ) : ℝ) := by
      rw [h1, h2]; push_cast; ring_nf; linarith
    exact_mod_cast this
  exact Finset.mem_sdiff.2 ⟨Activity.mem_awakeThroughoutToTick_of_mem_activeThroughoutToTick
    (Activity.mem_activeThroughoutToTick_of_le hpw hr), by
      -- `HonestOpenerAt`'s honesty clause has a third member, which `honestActiveAt` does not read
      simp only [Finset.mem_union, not_or] at hh ⊢; exact ⟨hh.1.1, hh.2⟩⟩

/-- **Kit theorem, the honest chain at an honest round opening slot after the hand-over.** The
first four conjuncts of `round_member_frame_after_healing`, which do not read the member `u`, under
its hypotheses without `hu`: every block on the honest chain before slot `s` is `B`
or an ancestor of `B`; `B` is of slot `s`; every updater of slot `s` saves `B` as its confirmation
of slot `s`; `H < h(B)`. Lemma 107 reads these four.

Why: as `round_member_frame_after_healing`, the inclusion (`honest_proposal_saved_until`,
`included_update_facts_q_until`, `honest_proposal_extends_chain_until`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `GST`: the time from which the network is
  synchronous; `s₀`: the healed slot; `anchor`: the time from which committee sleepiness holds;
  `i₂`: the hand-over step; `H`: the threshold; `s`: the slot; `B`: the proposal.

Read aloud: after the hand-over, the proposal `B` of an honest round opening slot `s` extends the
honest chain before `s`, is of slot `s`, is saved by every updater of `s`, and is higher than `H`. -/
theorem round_chain_frame_after_healing (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₂ H s : ℕ) (B : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRootsU : ∀ v ∈ updaterAt M S A x s, RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQU : ∀ v ∈ updaterAt M S A x s, A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s + 1))) (hAnchor : anchor ≤ x.time i₂)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₂)
    (hChain : ConfirmationsChainBefore M S A x s₀ s)
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor M S A x (honestActiveAt M S A x s')
        (OnHonestChainBefore M S A x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ w ∈ honestActiveAt M S A x s',
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' w)
    (hLocks₀ : ∀ w ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ w)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCachesU : ∀ v ∈ updaterAt M S A x s, ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j →
      x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) → w ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j w))
    (hAfter : x.time i₂ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s) (M.slotStart S.C s) → x.time i₂ < x.time k)
    (hOpener : HonestOpenerAt M S A x s)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hNoCollision : ¬ RootCollisionAtProposal M S A x s B)
    (hHold : ∀ s' : ℕ, s - 1 ≤ s' → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs)) :
    (∀ C : Block V, OnHonestChainBefore M S A x s₀ s C → C.AncestorEq B) ∧
    B.slot = s ∧
    (∀ w ∈ updaterAt M S A x s,
      (x.tickOutput w (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B) ∧
    H < (M.chainStateOf S.C B).h := by
  obtain ⟨hs2, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.slot_after_healed_round M.toSlotLayout F.sched) S
    s₀ s (by exact_mod_cast lt_of_le_of_lt ht₀ hAfter.1)
  obtain ⟨q, rfl⟩ : ∃ q, s = q + 2 := ⟨s - 2, by omega⟩
  -- the member frame at the proposer, an honest active validator of the slot
  obtain ⟨h1, h2, h3, h4, -⟩ := (round_member_frame_after_healing M F U Fx) S A x R GST s₀ anchor i₂ H (q + 2) B
    (S.P.proposer (q + 2)) E hNet hSkew hRedeliver Sy hΔs hRootsU hParent hAdvQU hSleepK hAnchor hGST ht₀
    hChain hInv hLocks hLocks₀ hOld hCachesU hAfter hOpener hPropose hNoCollision hHold hHoldP
    ((opener_mem_honestActiveAt M F U) S A R E q hOpener)
  exact ⟨h1, h2, h3, h4⟩

end GoldilocksCorrectness.Record.Proofs.Executions

