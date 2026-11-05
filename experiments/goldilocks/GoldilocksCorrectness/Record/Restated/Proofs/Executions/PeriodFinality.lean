module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodHolders
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma82
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma83
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickUpdateState
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.VoteDelivery
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Sleepy
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma55
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Roots
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReadersOnChain
public import GoldilocksCorrectness.Proofs.Executions.PeriodHolders
public import GoldilocksCorrectness.Proofs.Executions.Lemma82
public import GoldilocksCorrectness.Proofs.Executions.Lemma83
public import GoldilocksCorrectness.Proofs.Executions.TickUpdateState
public import GoldilocksCorrectness.Proofs.Executions.VoteDelivery
public import GoldilocksCorrectness.Proofs.Executions.Sleepy
public import GoldilocksCorrectness.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Proofs.Executions.Lemma55

@[expose] public section

/-!
# PeriodFinality, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/PeriodFinality.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 102's step, the certificates
at heights greater than `H` name blocks compatible with `B`. The page's routine-level theorems are
the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_lt_supportCutoff one_le_Δ
  slotStart_eq supportCutoff_cast supportCutoff_eq supportCutoff_slot supportCutoff_succ_times
  voteTime_cast voteTime_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions

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
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks)
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans tick_attest_awake
  awakeSince_of_record_awake create_attestation_cases compatible_iff
  compatible_of_ancestorEq_compatible ancestorEq_compatible goldfish_score_eq_ok dre_bind_ok)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once. No statement and no proof term changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## The fast blocks -/

/-! ## The certificates -/

/-- **Lemma 102 at a step: the certificates on held blocks name blocks compatible with `B`.** The
proof; the audited statement is in `Statements/Executions/PeriodFinalityStatements.lean`. Lemma
83's route (`lem83_one_certificate_greater_than_threshold`) with `hAtt` in place of the healed
facts: a member of the quorum never in the adversary set up to `x[j].time`, its vote in its record
(Lemma 74), sent by its tick at a step before `j`, at a height greater than `H`, so not old.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `t₀`: the
  time from which the attestations are new; `B`: the protected block; `j`: the step.

Read aloud: a certificate is a quorum, a quorum has an honest signer, and honest signers only name
chains compatible with `B`. -/
theorem certificatesCompatibleWithAt_of_attestations (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {H t₀ : ℕ} {B : Block V} (j : ℕ)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time j) t₀))
    (hAtt : AttestationsCompatibleWithBefore M S A x B H t₀ j) :
    CertificatesCompatibleWithAt M S A x H B j := by
  intro w D T h _ hD hJ hH
  obtain ⟨Q, hqA, hQ⟩ := hJ
  -- a member of the quorum outside the adversary set after every step read as a time at most the
  -- later of `x.time j` and `t₀`
  obtain ⟨u, hu, hhonM⟩ : ∃ u ∈ Q, A.HonestThroughTime x (max (x.time j) t₀) u := by
    by_contra hno
    have hall : ∀ v ∈ Q, ∃ i : ℕ, x.time i ≤ max (x.time j) t₀ ∧ v ∈ A.corrupted i := by
      intro v hv
      by_contra hn
      exact hno ⟨v, hv, fun i hi ha => hn ⟨i, hi, ha⟩⟩
    have h3 := hAdvQ Q hall
    omega
  have hhon : x.HonestThrough A j u := fun i' hi' =>
    hhonM i' (le_trans (R.time_mono hi') (le_max_left _ _))
  have hu₀ : u ∉ A.corruptedAtTime x t₀ :=
    Activity.not_mem_corruptedAtTime.2 fun i hi => hhonM i (by
      have := le_max_right (x.time j) (t₀ : ℝ); linarith)
  -- its vote of the certificate is in its record, and its tick sent it
  obtain ⟨a, hau, hah, haT, hon⟩ := hQ u hu
  have hrec : a.content ∈ (x.st j a.val_index).sentAttestations := by
    exact (GoldilocksCorrectness.Record.Statements.Executions.lem74_honest_attestations_recorded M F) S
      A x R E j w D a hD ((GoldilocksCorrectness.Record.Proofs.Routines.on_chain_iff M F a D).2
      ((GoldilocksCorrectness.Proofs.Routines.on_chain_iff a D).1 hon)) (by rw [hau]; exact hhon)
  rw [hau] at hrec
  obtain ⟨j', t', a', hj', hl, -, hsent, -, hcont, -⟩ :=
    (record_content_sent_step M F) S A x R E u j _ hrec
  have hh' : a'.h = h := by
    rw [← hah]
    exact congrArg AttestationContent.h hcont
  have hT' : a'.T = T.root := by
    rw [← haT]
    exact congrArg AttestationContent.T hcont
  obtain ⟨hOld, hNew⟩ := hAtt j' t' u a' hj' hl hsent
  rcases Nat.lt_or_ge t' t₀ with hlt | hge
  · -- before `t₀`, its height would be at most `H`
    have hle := hOld hlt hu₀
    rw [hh'] at hle
    exact absurd hle (Nat.not_le.mpr hH)
  · -- from `t₀` on, it names an entry compatible with `B` at its height: the member is honest
    -- after every step whose real time is at most its tick's, a step before `j`
    obtain ⟨E', hEB, -, hEh, hET⟩ :=
      hNew hge (Activity.not_mem_corruptedAtTime.2 fun i hi =>
        hhonM i (le_trans hi (le_trans (R.time_mono hj'.le) (le_max_left _ _))))
    exact ⟨E', hEh.trans hh', hT'.symm.trans hET, hEB⟩

end GoldilocksCorrectness.Record.Proofs.Executions

