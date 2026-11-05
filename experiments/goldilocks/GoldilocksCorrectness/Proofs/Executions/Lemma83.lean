module
public import GoldilocksCorrectness.Statements.Executions.HealedAttestationDefs
public import GoldilocksCorrectness.Statements.Executions.HonestAccountableStatements
public import GoldilocksCorrectness.Statements.Routines.CertificateDefs
public import GoldilocksCorrectness.Proofs.Executions.HonestAccountable
public import GoldilocksCorrectness.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Proofs.Executions.TickSends

@[expose] public section

/-!
# Lemma 83: one certificate per height greater than the threshold

The proofs of `lem83_one_certificate_greater_than_threshold` and
`lem83_one_justification_greater_than_threshold`, stated in
`GoldilocksCorrectness/Statements/Executions/HealedAttestationStatements.lean`.

The route: the certificate's quorum has a member `u` outside the adversary set at every time up to
the time after `j` steps, since fewer than a quorum have been in it; `u`'s vote of the certificate
is in `u`'s own record (Lemma 74), so `u`'s tick put an attestation with that content on the wire,
awake and honest then, at a tick before the step `j` (`record_content_sent_step`). That
attestation has the certificate's height, greater than `H`, so it was not sent before `t₀` (`u` is
honest at the time after `j` steps, the time at which the bound on the old attestations reads its
senders' honesty); sent at or after `t₀`, it was sent at the support cutoff of slot `s_a + 1`, so
that cutoff is at most `x[j].time`, and it names by its root the honest chain's entry block of slot
`s_a` at its height.

The bound on the old attestations in the honest-at form follows from the form with the senders honest at the send (`OldAttestationsAtMost`):
`oldAttestationsAtMostHonestAt_of_oldAttestationsAtMost`.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (supportCutoff)

open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (JustificationCertOn ProgressCertOn)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 83, one progress certificate per height greater than the threshold.** The proof; the
audited statement is in `Statements/Executions/HealedAttestationStatements.lean`. The entry is on
the honest chain at a slot `s_a` whose support cutoff of slot `s_a + 1` is at most `x[j].time`: the
honest member's attestation was sent at that cutoff (`hAgree`), at a tick before the step `j`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `t₀`: the
  time from which the honest attestations name the honest chain; `H`: the bound on the heights of
  the earlier ones; `j`: the step; `w`: the holder; `B`: the held block; `T`: the block the
  certificate names; `h`: its height; `s_a`: the slot of the entry `E`. -/
theorem lem83_one_certificate_greater_than_threshold (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ t₀ H : ℕ) (j : ℕ) (w : V) (B T : Block V)
    (h : Height)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : AdversaryFewerThanQuorumUntil Sched (quorum V) (x[j].time : Int))
    (hAgree : HonestAttestationsOnChain S Sched x s₀ t₀)
    (hOld : OldAttestationsAtMostHonestAt S Sched x t₀ x[j].time H)
    (hB : B ∈ (x[j][w].st).S.T)
    (hJ : ProgressCertOn B h T)
    (hH : H < h) :
    ∃ (s_a : ℕ) (E : Block V), supportCutoff S (s_a + 1) ≤ x[j].time ∧
      OnHonestChainAt S Sched x s₀ s_a E ∧ IsEntry S.C E ∧
      (chainStateOf S.C E).h = h ∧ T.root = E.root := by
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
    Sched x hU j w B a hB hon (by rw [hau]; exact hhon)
  rw [hau] at hrec
  obtain ⟨j', t', a', hj', hl, hAw, hHon, hsent, -, hcont, -⟩ :=
    record_content_sent_step S Sched x u j _ hrec
  have hh' : a'.h = h := by
    rw [← hah]
    exact congrArg AttestationContent.h hcont
  have hT' : a'.T = T.root := by
    rw [← haT]
    exact congrArg AttestationContent.T hcont
  rcases Nat.lt_or_ge t' t₀ with hlt | hge
  · -- before `t₀`, its height would be at most `H`
    have hle := hOld j' t' u a' hl hlt hAw (hhon _ le_rfl) hsent
    rw [hh'] at hle
    exact absurd hle (Nat.not_le.mpr hH)
  · -- from `t₀` on, it names the honest chain's entry at its height
    have htj : t' ≤ x[j].time := by
      rw [← (time_of_lbl_tickAllAwake x hl).2]
      exact time_mono x hj'
    obtain ⟨s_a, E, -, ht', hE1, hE2, hE3, hE4⟩ := hAgree j' t' u a' hl hge hAw hHon hsent
    exact ⟨s_a, E, ht' ▸ htj, hE1, hE2, hE3.trans hh', hT'.symm.trans hE4⟩

/-- **Lemma 83, one justification per height greater than the threshold.** The proof; the
audited statement is in `Statements/Executions/HealedAttestationStatements.lean`. The entry is on
the honest chain at a slot `s_a` whose support cutoff of slot `s_a + 1` is at most `x[j].time`.

The variables: as for `lem83_one_certificate_greater_than_threshold`. -/
theorem lem83_one_justification_greater_than_threshold (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ t₀ H : ℕ) (j : ℕ) (w : V) (B T : Block V)
    (h : Height)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : AdversaryFewerThanQuorumUntil Sched (quorum V) (x[j].time : Int))
    (hAgree : HonestAttestationsOnChain S Sched x s₀ t₀)
    (hOld : OldAttestationsAtMostHonestAt S Sched x t₀ x[j].time H)
    (hB : B ∈ (x[j][w].st).S.T)
    (hJ : JustificationCertOn B h T)
    (hH : H < h) :
    ∃ (s_a : ℕ) (E : Block V), supportCutoff S (s_a + 1) ≤ x[j].time ∧
      OnHonestChainAt S Sched x s₀ s_a E ∧ IsEntry S.C E ∧
      (chainStateOf S.C E).h = h ∧ T.root = E.root := by
  obtain ⟨A, hqA, hA⟩ := hJ
  refine lem83_one_certificate_greater_than_threshold S Sched x s₀ t₀ H j w B T h hU hAdvQ
    hAgree hOld hB ⟨A, hqA, fun v hv => ?_⟩ hH
  obtain ⟨a, h1, h2, h3, -, h5⟩ := hA v hv
  exact ⟨a, h1, h2, h3, h5⟩

/-- **The bound on the old attestations, from the senders honest at the send to the senders
honest at a time.** When every attestation an honest awake validator put on the wire at a tick
before `t₀` has height at most `H`, then for every time `tH`, every attestation a validator honest
at `tH` put on the wire at a tick before `t₀` has height at most `H`.

Why: what a tick puts on the wire is signed by a validator awake and outside the adversary set at
the tick (`tick_send_of_honestSendAt`), so the sender was honest at the send.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t₀`: the time before which the
  attestations are read; `tH`: the time at which the senders' honesty is read; `H`: the bound. -/
theorem oldAttestationsAtMostHonestAt_of_oldAttestationsAtMost (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t₀ tH H : ℕ)
    (hOld : OldAttestationsAtMost S Sched x t₀ H) :
    OldAttestationsAtMostHonestAt S Sched x t₀ tH H := by
  intro i t v a hl ht hAw _ hsent
  exact hOld i t v a hl ht hAw (Finset.mem_sdiff.1 (tick_send_of_honestSendAt hl hsent).1).2 hsent

end GoldilocksCorrectness.Proofs.Executions
