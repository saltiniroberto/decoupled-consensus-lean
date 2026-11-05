module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodFinality
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AsyncResilienceDefs
public import GoldilocksCorrectness.Statements.Executions.AsyncResilienceDefs

@[expose] public section

/-!
# PeriodFinalityStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/PeriodFinalityStatements.lean`, over
a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 102's step, the
certificates at heights greater than `H` name blocks compatible with `B`; it is the theorem of the
same name of `Record/Restated/Proofs/Executions/PeriodFinality.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (voteTime supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

variable (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)

/-! ## The certificates -/

/-- **Lemma 102 at a step: the certificates on held blocks name blocks compatible with `B`.**
Under unforgeability, with fewer than a quorum ever corrupted up to the time after `j` steps: when
every honest attestation sent at a step before `j` is old (height at most `H`) or names an entry
compatible with `B`, every progress certificate at a height greater than `H` on the chain of a
block a validator honest at `j` holds then names a block compatible with `B` at that height.

Why: Lemma 83's route (`lem83_one_certificate_greater_than_threshold`): some signer of the quorum
was never corrupted up to `x[j].time`, its attestation is in its record (Lemma 74), so its tick
sent it at a step before `j`, at a height greater than `H`, hence not old.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `t₀`: the
  time from which the attestations are new; `B`: the protected block; `j`: the step;
- `hU`: unforgeability; `hAdvQ`: fewer than a quorum have been corrupted up to the later of `x[j].time` and `t₀`
;
  `hAtt`: the attestations sent before step `j` are old or compatible with `B`.



Read aloud: a certificate is a quorum, a quorum has an honest signer, and honest signers only
name chains compatible with `B`. -/
theorem certificatesCompatibleWithAt_of_attestations (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {H t₀ : ℕ} {B : Block V} (j : ℕ)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time j) t₀))
    (hAtt : AttestationsCompatibleWithBefore M S A x B H t₀ j) :
    CertificatesCompatibleWithAt M S A x H B j :=
  (GoldilocksCorrectness.Record.Proofs.Executions.certificatesCompatibleWithAt_of_attestations M F)
    S A x R E j hAdvQ hAtt

end GoldilocksCorrectness.Record.Statements.Executions

