module
public import GoldilocksCorrectness.Proofs.Executions.PeriodFinality
public import GoldilocksCorrectness.Statements.Executions.AsyncResilienceDefs

@[expose] public section

/-!


`fast_blocks_compatible_of_votes` moved to
`Statements/Executions/PeriodCompatCopiesStatements.lean`, its proof calling the copy
`fast_blocks_compatible_of_votes_updater_ofCompat`.

  The probe's `attest_source_fast_block` is stated here with `updaterAt` in place of
`honestActiveAt` under its own name (its rendering note says why);
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (voteTime supportCutoff)

open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

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
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `t₀`: the
  time from which the attestations are new; `B`: the protected block; `j`: the step;
- `hU`: unforgeability; `hAdvQ`: fewer than a quorum have been corrupted up to `x[j].time`;
  `hAtt`: the attestations sent before step `j` are old or compatible with `B`.



Read aloud: a certificate is a quorum, a quorum has an honest signer, and honest signers only
name chains compatible with `B`. -/
theorem certificatesCompatibleWithAt_of_attestations {H t₀ : ℕ} {B : Block V} (j : ℕ)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : AdversaryFewerThanQuorumUntil Sched (quorum V) (x[j].time : Int))
    (hAtt : AttestationsCompatibleWithBefore S Sched x B H t₀ j) :
    CertificatesCompatibleWithAt S Sched x H B j :=
  GoldilocksCorrectness.Proofs.Executions.certificatesCompatibleWithAt_of_attestations S Sched x j
    hU hAdvQ hAtt

end GoldilocksCorrectness.Statements.Executions
