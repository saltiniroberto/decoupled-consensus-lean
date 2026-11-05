module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealedAttestationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestChainAfterHealingStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.AttestationStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickSends
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Record
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainState
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.RecordAttestation
public import GoldilocksCorrectness.Statements.Executions.HealedAttestationStatements
public import GoldilocksCorrectness.Statements.Executions.HonestChainAfterHealingStatements
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Statements.Routines.AttestationStatements
public import GoldilocksCorrectness.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Proofs.Executions.TickSends
public import GoldilocksCorrectness.Proofs.Routines.Record
public import GoldilocksCorrectness.Proofs.Routines.ChainState
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOf

@[expose] public section

/-!
# FinalityLivenessKit, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/FinalityLivenessKit.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: the record of the node state a tick
starts from is the record of the configuration, and no honest attestation sent after the healed
round's action time at a height greater than the threshold is a timeout. The page's routine-level
theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (supportCutoff)

open GoldilocksCorrectness.Proofs.Routines (wake_eq)

namespace GoldilocksCorrectness.Record.Proofs.Routines

open GoldilocksCorrectness.Record.Statements.Routines (RecordConsistent)

open Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## A timeout is built only behind a recorded timeout or another recorded target -/

/-! ## The finalization height along the state transition -/

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable [DecidableEq V] [Fintype V]

end GoldilocksCorrectness.Record.Proofs.Routines

namespace GoldilocksCorrectness.Record.Proofs.Executions

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (compatible_iff ancestorEq_genesis_iff
  ancestorEq_node_iff state_transition_pending_above)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## The monotonicity of `h_j` and `h_F` along a chain -/

/-! ## No honest timeout after healing -/

/-- The anti-slashing record of the state a tick starts from is the configuration's: the targets,
the timeouts, the locks and the attestation contents sent.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `t`: the time of the
  tick; `v`: the validator.

Read aloud: the node state a tick starts from has the anti-slashing record of the configuration's
node state. -/
theorem tickInputState_Λ (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
 (t : ℕ) (v : V) (ht : 1 ≤ t) (hv : v ∈ A.activeAtTime x t) :
    M.sentTarget (x.tickInput v t) = M.sentTarget (x.tickInput v t) ∧
      M.sentTimeout (x.tickInput v t) = M.sentTimeout (x.tickInput v t) ∧
      M.sentLock (x.tickInput v t) = M.sentLock (x.tickInput v t) ∧
      (x.tickInput v t).sentAttestations = (x.tickInput v t).sentAttestations :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **No honest timeout after healing.** The proof; the audited statement is in
`Statements/Executions/FinalityLivenessKitStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `H`: the bound
  on the heights of the honest attestations sent before the healed round's action time;
- `i`: the step; `t`: its time; `v`: the validator; `a`: the attestation.

Read aloud: after healing, honest validators only vote targets at new heights. -/
theorem no_honest_timeout_after_healing (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ H i t : ℕ) (v : V) (a : Attestation V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hChain : ConfirmationsChain M S A x s₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hl : x.lbl i = Event.tick v t) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ t)
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
      have := ih j hj t' a' hl' hge (hHonEarlier j t' hj hl') hsent' (by rw [hh']; exact hH)
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
      obtain ⟨σ, E₁, C₁, hσ, -, hu₁, hS₁, hEC₁, hE2, hE3, hE4⟩ :=
        (lem82b_entry_at_slot M F U) S A x R s₀ i t v a E hl ht₀ hSent
      obtain ⟨σ', E₂, C₂, hσ', -, hu₂, hS₂, hEC₂, hE2', hE3', hE4'⟩ :=
        (lem82b_entry_at_slot M F U) S A x R s₀ j t' v a' E hl' hge hsent'
      -- two entries of the honest chain at one height are one block
      have hEE : E₁ = E₂ := by
        have hheq : (M.chainStateOf S.C E₁).h = (M.chainStateOf S.C E₂).h := by rw [hE3, hE3', hh']
        rcases (compatible_iff E₁ E₂).1
            ((onHonestChain_compatible M F) S A x s₀ E₁ E₂ hChain ⟨σ, hσ, v, hu₁, C₁, hS₁, hEC₁⟩
              ⟨σ', hσ', v, hu₂, C₂, hS₂, hEC₂⟩) with h | h
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

end GoldilocksCorrectness.Record.Proofs.Executions

