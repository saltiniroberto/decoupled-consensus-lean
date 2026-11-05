module
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
# No honest timeout after healing, and the monotonicity of the justification and finalization
heights

The proofs of `no_honest_timeout_after_healing` and `chainStateOf_h_j_h_F_mono`, stated in
`GoldilocksCorrectness/Statements/Executions/FinalityLivenessKitStatements.lean`, and the routine
facts they need.

The route of `no_honest_timeout_after_healing`: the attestation is the one `create_attestation`
built from the validator's record (Lemma 49); a timeout is built only when the record holds a
timeout at the source's height, or a target there for another block (`create_attestation_timeout`);
by the record's consistency either was sent earlier by the same validator, at a tick, awake and
honest then (`record_content_sent_step`). Sent before the healed round's action time, it would have
a height at most `H`; sent from then on, a timeout is excluded by induction on the step, and a
target names the honest chain's entry at its height (Lemma 82), as the attestation itself does, and
two entries of the honest chain at one height are one block.

The route of the monotonicity: the state transition keeps every pending justification at a height
greater than the finalization height (`state_transition_pending_above`), so the loop over them
never lowers `h_F` (`state_transition_h_F_mono`); the justification height is kept or becomes the
parent's height, which is greater (`state_transition_h_j_mono`); then an induction on ancestry.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (supportCutoff)

open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (wake_eq)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks

variable {V : Type}

private theorem getElem_option (f : Height → Option BlockId) (h : Height) : f[h] = f h := rfl

private theorem getElem_bool (f : Height → Bool) (h : Height) : f[h] = f h := rfl

/-! ## A timeout is built only behind a recorded timeout or another recorded target -/

/-! ## The finalization height along the state transition -/

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable [DecidableEq V] [Fintype V]

end GoldilocksCorrectness.Proofs.Routines

namespace GoldilocksCorrectness.Proofs.Executions

open GoldilocksCorrectness.Proofs.Routines (lem47_chain_state_heights)

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (lem49_tick_attests RecordConsistent)
open GoldilocksCorrectness.Proofs.Routines (create_attestation_timeout compatible_iff
  ancestorEq_genesis_iff ancestorEq_node_iff state_transition_pending_above
  state_transition_h_F_mono state_transition_h_j_mono)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## The monotonicity of `h_j` and `h_F` along a chain -/

/-! ## No honest timeout after healing -/

/-- The record of the state a tick starts from is the record of the configuration.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `t`: the time of the
  tick; `v`: the validator. -/
theorem tickInputState_Λ (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (i t : ℕ) (v : V) : (tickInputState x i t v).Λ = (x[i][v].st).Λ := by
  unfold tickInputState
  split <;> (try rw [wake_eq]) <;> rfl

/-- **No honest timeout after healing.** The proof; the audited statement is in
`Statements/Executions/FinalityLivenessKitStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `H`: the bound
  on the heights of the honest attestations sent before the healed round's action time;
- `i`: the step; `t`: its time; `v`: the validator; `a`: the attestation. -/
theorem no_honest_timeout_after_healing (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ H i t : ℕ) (v : V) (a : Attestation V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hChain : ConfirmationsChain S Sched x s₀)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hl : x.lbl i = AtomicAction.tickAllAwake t) (ht₀ : supportCutoff S (s₀ + 1) ≤ t)
    (hAwake : v ∈ Sched.awake (t : Int)) (hHon : v ∉ Sched.adv (t : Int))
    (hSent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent)
    (hH : H < a.h) :
    a.τ = false := by
  have hAgree := lem82_honest_attestations_on_chain S Sched x s₀ hDiv hMono
  induction i using Nat.strong_induction_on generalizing t a with
  | _ i ih =>
  by_contra hτ
  have hτ' : a.τ = true := by simpa using hτ
  -- the attestation is the one the client built from the validator's record
  obtain ⟨-, n', sent, hrun, ha⟩ := tick_send_of_honestSendAt hl hSent
  obtain ⟨-, fi, source, -, -, hca, -⟩ := lem49_tick_attests S.C S.P S.X _ n' _ sent a hrun ha
  obtain ⟨hah, haT, hcase⟩ := create_attestation_timeout _ _ _ _ _ _ _ a hca hτ'
  rw [tickInputState_Λ] at hcase
  have hΛ : RecordConsistent (x[i][v].st).Λ := recordConsistent_of_exec S Sched x i v
  rcases hcase with htimeout | ⟨T', htarget, hne⟩
  · -- a timeout at the attestation's height was sent earlier, at a tick
    obtain ⟨c, hc, hch, hcτ⟩ := (hΛ.timeoutRec _).1 htimeout
    obtain ⟨j, t', a', hj, hl', hAw', hHon', hsent', -, hcont, -⟩ :=
      record_content_sent_step S Sched x v i c hc
    have hh' : a'.h = a.h := by
      rw [hah, ← hch]; exact congrArg AttestationContent.h hcont
    have hτa' : a'.τ = true := by
      rw [← hcτ]; exact congrArg AttestationContent.τ hcont
    rcases Nat.lt_or_ge t' (supportCutoff S (s₀ + 1)) with hlt | hge
    · -- before the healed round's action time its height is at most `H`
      have hle := hOld j t' v a' hl' hlt hAw' hHon' hsent'
      rw [hh'] at hle
      exact absurd hle (Nat.not_le.mpr hH)
    · -- from then on, it is a target by the induction
      have := ih j hj t' a' hl' hge hAw' hHon' hsent' (by rw [hh']; exact hH)
      rw [hτa'] at this
      cases this
  · -- a target at the attestation's height for another block was sent earlier, at a tick
    obtain ⟨c, hc, hch, hcτ, hcT⟩ := (hΛ.targetRec _ _).1 htarget
    obtain ⟨j, t', a', hj, hl', hAw', hHon', hsent', -, hcont, -⟩ :=
      record_content_sent_step S Sched x v i c hc
    have hh' : a'.h = a.h := by
      rw [hah, ← hch]; exact congrArg AttestationContent.h hcont
    have hT' : a'.T = T' := by
      rw [← hcT]; exact congrArg AttestationContent.T hcont
    rcases Nat.lt_or_ge t' (supportCutoff S (s₀ + 1)) with hlt | hge
    · -- before the healed round's action time its height is at most `H`
      have hle := hOld j t' v a' hl' hlt hAw' hHon' hsent'
      rw [hh'] at hle
      exact absurd hle (Nat.not_le.mpr hH)
    · -- from then on, both attestations name the honest chain's entry at the height (Lemma 82)
      obtain ⟨s, E, -, -, hE1, hE2, hE3, hE4⟩ := hAgree i t v a hl ht₀ hAwake hHon hSent
      obtain ⟨s', E', -, -, hE1', hE2', hE3', hE4'⟩ := hAgree j t' v a' hl' hge hAw' hHon' hsent'
      -- two entries of the honest chain at one height are one block
      have hEE : E = E' := by
        have hheq : (chainStateOf S.C E).h = (chainStateOf S.C E').h := by rw [hE3, hE3', hh']
        rcases (compatible_iff E E').1
            (onHonestChain_compatible S Sched x s₀ E E' hChain ⟨s, hE1⟩ ⟨s', hE1'⟩) with h | h
        · have := (lem47_chain_state_heights S.C E E').2.2.2.2 h hheq
          unfold IsEntry at hE2 hE2'
          rw [hE2, hE2'] at this
          exact this
        · have := (lem47_chain_state_heights S.C E' E).2.2.2.2 h hheq.symm
          unfold IsEntry at hE2 hE2'
          rw [hE2, hE2'] at this
          exact this.symm
      apply hne
      rw [← hT', hE4', ← hEE, ← hE4, haT]

end GoldilocksCorrectness.Proofs.Executions
