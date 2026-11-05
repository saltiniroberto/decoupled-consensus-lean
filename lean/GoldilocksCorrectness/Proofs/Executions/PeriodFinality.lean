module
public import GoldilocksCorrectness.Proofs.Executions.PeriodHolders
public import GoldilocksCorrectness.Proofs.Executions.Lemma82
public import GoldilocksCorrectness.Proofs.Executions.Lemma83
public import GoldilocksCorrectness.Proofs.Executions.TickUpdateState
public import GoldilocksCorrectness.Proofs.Executions.VoteDelivery
public import GoldilocksCorrectness.Proofs.Executions.Sleepy
public import GoldilocksCorrectness.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Proofs.Executions.Lemma55
public import GoldilocksCorrectness.Proofs.Executions.Roots
public import GoldilocksCorrectness.Proofs.Routines.Lemma36
public import GoldilocksCorrectness.Proofs.Routines.Score
public import GoldilocksCorrectness.Proofs.Routines.Schedule

@[expose] public section

/-!
- `certificatesCompatibleWithAt_of_attestations`, Lemma 102's step: the certificates at heights
  greater than `H` name blocks compatible with `B`.

 `fast_blocks_compatible_of_votes` moved to
`Proofs/Executions/PeriodCompatCopies.lean`, its proof calling the copy
`fast_blocks_compatible_of_votes_updater_ofCompat`.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_lt_supportCutoff one_le_Δ
  slotStart_eq supportCutoff_cast supportCutoff_eq supportCutoff_slot supportCutoff_succ_times
  voteTime_cast voteTime_eq)

open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg AtomicHonest)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (lem15_tick_updates_confirmation lem49_tick_attests
  ProgressCertOn expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans ac_to_fg_source_mem
  ac_to_fg_source_fast tick_attest_awake awakeSince_of_record_awake create_attestation_cases
  compatible_iff compatible_of_ancestorEq_compatible ancestorEq_compatible
  update_confirmation_fast_blocks_pass goldfish_score_eq_ok mem_supportersOf_iff
  disjoint_supportersOf_equivocators supportersOf mem_equivocators_iff dre_bind_ok)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once. No statement and no proof term changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## The fast blocks -/

omit [Fintype V] [RootOrder] in
/-- **The fast test fails for a block supported only by validators outside the lock holders.**
Write `C` for the committee of a slot, `Hd` for the lock holders of that slot and `Supp` for the
validators whose vote supports a block `X`. When every supporter of `X` is a committee member
outside `Hd`, and the committee members in `Hd` are more than the other members, twice the number
of supporters is less than the size of the committee: `fast_test`'s inequality
`|committee| ≤ 2 · score` fails for `X`. Copied from
`scratch/goldilocks_async/probe_outside_1.lean:58`.

The variables:
- `C`: the committee; `Hd`: the lock holders; `Supp`: the supporters. -/
theorem fast_test_fails_of_minority (C Hd Supp : Finset V)
    (hSupp : Supp ⊆ C \ Hd) (hMaj : |C \ Hd| < |Hd ∩ C|) :
    ¬ (|C| ≤ 2 * |Supp|) := by
  have h1 : |Supp| ≤ |C \ Hd| := Finset.card_le_card hSupp
  have h2 : |C \ Hd| + |C ∩ Hd| = |C| := Finset.card_sdiff_add_card_inter C Hd
  rw [Finset.inter_comm] at h2
  omega

/-! ## The certificates -/

/-- **Lemma 102 at a step: the certificates on held blocks name blocks compatible with `B`.** The
proof; the audited statement is in `Statements/Executions/PeriodFinalityStatements.lean`. Lemma
83's route (`lem83_one_certificate_greater_than_threshold`) with `hAtt` in place of the healed
facts: a member of the quorum never in the adversary set up to `x[j].time`, its vote in its record
(Lemma 74), sent by its tick at a step before `j`, at a height greater than `H`, so not old.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `t₀`: the
  time from which the attestations are new; `B`: the protected block; `j`: the step. -/
theorem certificatesCompatibleWithAt_of_attestations (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) {H t₀ : ℕ} {B : Block V} (j : ℕ)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : AdversaryFewerThanQuorumUntil Sched (quorum V) (x[j].time : Int))
    (hAtt : AttestationsCompatibleWithBefore S Sched x B H t₀ j) :
    CertificatesCompatibleWithAt S Sched x H B j := by
  intro w D T h _ hD hJ hH
  obtain ⟨A, hqA, hA⟩ := hJ
  -- a member of the quorum outside the adversary set up to the time after `j` steps
  obtain ⟨u, hu, hhon⟩ : ∃ u ∈ A, HonestThrough x j u := by
    by_contra hno
    have hall : ∀ v ∈ A, ∃ t' : Int, t' ≤ (x[j].time : Int) ∧ v ∈ Sched.adv t' := by
      intro v hv
      by_contra hn
      exact hno ⟨v, hv, fun t' ht' ha => hn ⟨t', ht', ha⟩⟩
    have h3 := hAdvQ A hall
    omega
  -- its vote of the certificate is in its record, and its tick sent it
  obtain ⟨a, hau, hah, haT, hon⟩ := hA u hu
  have hrec := GoldilocksCorrectness.Statements.Executions.lem74_honest_attestations_recorded S
    Sched x hU j w D a hD hon (by rw [hau]; exact hhon)
  rw [hau] at hrec
  obtain ⟨j', t', a', hj', hl, hAw, hHon, hsent, -, hcont, -⟩ :=
    record_content_sent_step S Sched x u j _ hrec
  have hh' : a'.h = h := by
    rw [← hah]
    exact congrArg AttestationContent.h hcont
  have hT' : a'.T = T.root := by
    rw [← haT]
    exact congrArg AttestationContent.T hcont
  obtain ⟨hOld, hNew⟩ := hAtt j' t' u a' hj' hl hAw hHon hsent
  rcases Nat.lt_or_ge t' t₀ with hlt | hge
  · -- before `t₀`, its height would be at most `H`
    have hle := hOld hlt
    rw [hh'] at hle
    exact absurd hle (Nat.not_le.mpr hH)
  · -- from `t₀` on, it names an entry compatible with `B` at its height
    obtain ⟨E, hEB, -, hEh, hET⟩ := hNew hge
    exact ⟨E, hEh.trans hh', hT'.symm.trans hET, hEB⟩

end GoldilocksCorrectness.Proofs.Executions
