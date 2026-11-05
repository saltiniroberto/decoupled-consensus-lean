module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealedAttestationDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestAccountableStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.CertificateDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HonestAccountable
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickSends
public import GoldilocksCorrectness.Statements.Executions.HealedAttestationDefs
public import GoldilocksCorrectness.Statements.Executions.HonestAccountableStatements
public import GoldilocksCorrectness.Statements.Routines.CertificateDefs

@[expose] public section

/-!
# Lemma83, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma83.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: Lemma 83, one certificate and one justification
per height greater than the threshold, and the bound on the old attestations in the form with the
senders honest at a time. The page's routine-level theorems are the facts' fields or have their
twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (supportCutoff)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Statements.Routines (IsEntry)

open GoldilocksCorrectness.Record.Statements.Routines (JustificationCertOn ProgressCertOn)

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

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Lemma 83's argument, over a real honesty time `tH`.** The body of
`lem83_one_certificate_greater_than_threshold_at` with the honesty time `tH` a real number at least
the time after `j` steps: the adversary bound and the bound on the old attestations are read at `tH`,
and the honest member of the certificate is chosen outside the adversary set up to `tH`. Both
`lem83_one_certificate_greater_than_threshold_at` (a natural `tH`) and
`lem83_one_certificate_greater_than_threshold` (`tH := x[j].time`) are instances.

The variables: as for `lem83_one_certificate_greater_than_threshold_at`, with `tH : ℝ`.

Read aloud: a progress certificate at a height greater than `H`, on the chain of a held block, names
by root the honest chain's entry block at that height, at a slot whose update ran by the time after
`j` steps, when the adversary bound and the old attestations' bound are read at a real time `tH` at
least the time after `j` steps. -/
theorem one_certificate_greater_than_threshold_at_real (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s₀ t₀ H : ℕ) (j : ℕ) (w : V) (B T : Block V)
    (h : Height) (tH : ℝ) (htH : x.time j ≤ tH)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) tH)
    (hAgree : HonestAttestationsOnChain M S A x s₀ t₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ tH H)
    (hB : B ∈ (x.st j w).tree)
    (hJ : ProgressCertOn M B h T)
    (hH : H < h) :
    ∃ (s_a : ℕ) (E : Block V), (∃ (k : ℕ) (u : V), k < j ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) ∧
      OnHonestChainAt M S A x s₀ s_a E ∧ IsEntry M S.C E ∧
      (M.chainStateOf S.C E).h = h ∧ T.root = E.root := by
  obtain ⟨X, hXB, Q, hqA, hA⟩ := hJ
  -- the quorum at `X` is `quorum V`, the validators being fixed; `X` is held, an ancestor of `B`
  rw [GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched X] at hqA
  have hX := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E j w B X hB hXB
  -- a member of the quorum outside the adversary set after every step whose time is at most `tH`
  obtain ⟨u, hu, hhonH⟩ : ∃ u ∈ Q, A.HonestThroughTime x tH u := by
    by_contra hno
    have hall : ∀ v ∈ Q, ∃ i : ℕ, x.time i ≤ tH ∧ v ∈ A.corrupted i := by
      intro v hv
      by_contra hn
      exact hno ⟨v, hv, fun i hi ha => hn ⟨i, hi, ha⟩⟩
    have h3 := hAdvQ Q hall
    omega
  have hhon : x.HonestThrough A j u := fun i' hi' => hhonH i' (le_trans ((time_mono M) x R hi') htH)
  -- its vote of the certificate is in its record, and its tick sent it
  obtain ⟨a, hau, hah, haT, hon⟩ := hA u hu
  have hrec := (GoldilocksCorrectness.Record.Statements.Executions.lem74_honest_attestations_recorded M F) S
    A x R E j w X a hX hon (by rw [hau]; exact hhon)
  rw [hau] at hrec
  obtain ⟨j', t', a', hj', hl, -, hsent, -, hcont, -⟩ :=
    (record_content_sent_step M F) S A x R E u j _ hrec
  have hh' : a'.h = h := by
    rw [← hah]
    exact congrArg AttestationContent.h hcont
  have hT' : a'.T = T.root := by
    rw [← haT]
    exact congrArg AttestationContent.T hcont
  have hvH : u ∉ A.corruptedAtTime x tH := Activity.not_mem_corruptedAtTime.2 hhonH
  rcases Nat.lt_or_ge t' t₀ with hlt | hge
  · -- before `t₀`, its height would be at most `H`
    have hle := hOld j' t' u a' hl (by exact_mod_cast hlt) hvH hsent
    rw [hh'] at hle
    exact absurd hle (Nat.not_le.mpr hH)
  · -- from `t₀` on, it names the honest chain's entry at its height: `u` is outside the adversary set up to the
    -- real time of its tick's step `j' < j`, which is at most `tH`
    have hvt : u ∉ A.corruptedAtTime x (x.time j') :=
      Activity.not_mem_corruptedAtTime.2 fun k hk =>
        hhonH k (le_trans hk (le_trans ((time_mono M) x R (Nat.le_of_lt hj')) htH))
    obtain ⟨s_a, E, -, ht', hE1, hE2, hE3, hE4⟩ := hAgree j' t' u a' hl hge hvt hsent
    subst ht'
    exact ⟨s_a, E, ⟨j', u, hj', hl⟩, hE1, hE2, hE3.trans hh', hT'.symm.trans hE4⟩

/-- **Lemma 83, one progress certificate per height greater than the threshold.** The proof; the
audited statement is in `Statements/Executions/HealedAttestationStatements.lean`, whose proof is the
instance `tH := x[j].time` of this form: the adversary bound and the bound on the old attestations
are read at a time `tH` at least the time after `j` steps, and the honest member of the certificate
is chosen outside the adversary set up to `tH`. The entry is on the honest chain at a slot `s_a`
to whose support cutoff of slot `s_a + 1` some validator ticked at a step before `j`: the honest member's attestation was sent at its tick to that cutoff
(`hAgree`), a step before `j`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `t₀`: the
  time from which the honest attestations name the honest chain; `H`: the bound on the heights of
  the earlier ones; `j`: the step; `w`: the holder; `B`: the held block; `T`: the block the
  certificate names; `h`: its height; `s_a`: the slot of the entry `E`; `tH`: the time the
  senders' honesty is read at.

Read aloud: a progress certificate at a height greater than `H`, on the chain of a held block, names
by root the honest chain's entry block at that height, at a slot whose update ran by the time after
`j` steps. -/
theorem lem83_one_certificate_greater_than_threshold_at (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s₀ t₀ H : ℕ) (j : ℕ) (w : V) (B T : Block V)
    (h : Height) (tH : ℕ) (htH : x.time j ≤ tH)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) tH)
    (hAgree : HonestAttestationsOnChain M S A x s₀ t₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ tH H)
    (hB : B ∈ (x.st j w).tree)
    (hJ : ProgressCertOn M B h T)
    (hH : H < h) :
    ∃ (s_a : ℕ) (E : Block V), (∃ (k : ℕ) (u : V), k < j ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) ∧
      OnHonestChainAt M S A x s₀ s_a E ∧ IsEntry M S.C E ∧
      (M.chainStateOf S.C E).h = h ∧ T.root = E.root := by
  exact (one_certificate_greater_than_threshold_at_real M F Fx) S A x R E s₀ t₀ H j w B T h tH htH
    hAdvQ hAgree hOld hB hJ hH

/-- **Lemma 83, one progress certificate per height greater than the threshold.** The proof; the
audited statement is in `Statements/Executions/HealedAttestationStatements.lean`: the instance of
`one_certificate_greater_than_threshold_at_real` at the honesty time `tH := x[j].time`.

The variables: as for `lem83_one_certificate_greater_than_threshold_at`.

Read aloud: a progress certificate at a height greater than `H`, on the chain of a held block, names
by root the honest chain's entry block at that height, at a slot whose update ran by the time after
`j` steps. -/
theorem lem83_one_certificate_greater_than_threshold (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s₀ t₀ H : ℕ) (j : ℕ) (w : V) (B T : Block V)
    (h : Height)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time j))
    (hAgree : HonestAttestationsOnChain M S A x s₀ t₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ (x.time j) H)
    (hB : B ∈ (x.st j w).tree)
    (hJ : ProgressCertOn M B h T)
    (hH : H < h) :
    ∃ (s_a : ℕ) (E : Block V), (∃ (k : ℕ) (u : V), k < j ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) ∧
      OnHonestChainAt M S A x s₀ s_a E ∧ IsEntry M S.C E ∧
      (M.chainStateOf S.C E).h = h ∧ T.root = E.root := by
  exact
    (one_certificate_greater_than_threshold_at_real M F Fx) S A x R E s₀ t₀ H j w B T h (x.time j) le_rfl
      hAdvQ hAgree hOld hB hJ hH

/-- **Lemma 83 for justifications, over an honesty time `tH` at least the time after `j` steps.**
`lem83_one_justification_greater_than_threshold` with the adversary bound and the bound on the old
attestations read at `tH ≥ x[j].time` (the honest member of the certificate is chosen outside the
adversary set up to `tH`).

The variables: as for `lem83_one_certificate_greater_than_threshold_at`.

Read aloud: a justification certificate at a height greater than `H`, on the chain of a held block,
names by root the honest chain's entry block at that height, when the old attestations are bounded
for the senders honest at a time `tH` at least the time after `j` steps. -/
theorem lem83_one_justification_greater_than_threshold_at (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s₀ t₀ H : ℕ) (j : ℕ) (w : V) (B T : Block V)
    (h : Height) (tH : ℕ) (htH : x.time j ≤ tH)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) tH)
    (hAgree : HonestAttestationsOnChain M S A x s₀ t₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ tH H)
    (hB : B ∈ (x.st j w).tree)
    (hJ : JustificationCertOn M B h T)
    (hH : H < h) :
    ∃ (s_a : ℕ) (E : Block V), (∃ (k : ℕ) (u : V), k < j ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) ∧
      OnHonestChainAt M S A x s₀ s_a E ∧ IsEntry M S.C E ∧
      (M.chainStateOf S.C E).h = h ∧ T.root = E.root := by
  obtain ⟨X, hXB, Q, hqA, hA⟩ := hJ
  refine (lem83_one_certificate_greater_than_threshold_at M F Fx) S A x R E s₀ t₀ H j w B T h tH htH hAdvQ
    hAgree hOld hB ⟨X, hXB, Q, hqA, fun v hv => ?_⟩ hH
  obtain ⟨a, h1, h2, h3, -, h5⟩ := hA v hv
  exact ⟨a, h1, h2, h3, h5⟩

/-- **Lemma 83, one justification per height greater than the threshold.** The proof; the
audited statement is in `Statements/Executions/HealedAttestationStatements.lean`. The entry is on
the honest chain at a slot `s_a` to whose support cutoff of slot `s_a + 1` some validator ticked at a
step before `j`.

The variables: `M`, the model; `F`, its facts; `U`, its slot layout is uniform; `Fx`, its
validators are fixed; the others as for `lem83_one_certificate_greater_than_threshold`.

Read aloud: a justification certificate at a height greater than `H`, on the chain of a held block,
names by root the honest chain's entry block at that height, at a slot whose update some validator ran at a tick before the step `j`. -/
theorem lem83_one_justification_greater_than_threshold (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s₀ t₀ H : ℕ) (j : ℕ) (w : V) (B T : Block V)
    (h : Height)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time j))
    (hAgree : HonestAttestationsOnChain M S A x s₀ t₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ (x.time j) H)
    (hB : B ∈ (x.st j w).tree)
    (hJ : JustificationCertOn M B h T)
    (hH : H < h) :
    ∃ (s_a : ℕ) (E : Block V), (∃ (k : ℕ) (u : V), k < j ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) ∧
      OnHonestChainAt M S A x s₀ s_a E ∧ IsEntry M S.C E ∧
      (M.chainStateOf S.C E).h = h ∧ T.root = E.root := by
  obtain ⟨X, hXB, Q, hqA, hA⟩ := hJ
  refine (lem83_one_certificate_greater_than_threshold M F Fx) S A x R E s₀ t₀ H j w B T h hAdvQ
    hAgree hOld hB ⟨X, hXB, Q, hqA, fun v hv => ?_⟩ hH
  obtain ⟨a, h1, h2, h3, -, h5⟩ := hA v hv
  exact ⟨a, h1, h2, h3, h5⟩

/-- **Lemma 83 for justifications, over a real honesty time `tH`.** The justification form of
`one_certificate_greater_than_threshold_at_real`: the adversary bound and the bound on the old
attestations are read at a real time `tH` at least the time after `j` steps.

The variables: as for `one_certificate_greater_than_threshold_at_real`.

Read aloud: a justification certificate at a height greater than `H`, on the chain of a held block,
names by root the honest chain's entry block at that height, when the adversary bound and the old
attestations' bound are read at a real time `tH` at least the time after `j` steps. -/
theorem one_justification_greater_than_threshold_at_real (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s₀ t₀ H : ℕ) (j : ℕ) (w : V) (B T : Block V)
    (h : Height) (tH : ℝ) (htH : x.time j ≤ tH)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) tH)
    (hAgree : HonestAttestationsOnChain M S A x s₀ t₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ tH H)
    (hB : B ∈ (x.st j w).tree)
    (hJ : JustificationCertOn M B h T)
    (hH : H < h) :
    ∃ (s_a : ℕ) (E : Block V), (∃ (k : ℕ) (u : V), k < j ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) ∧
      OnHonestChainAt M S A x s₀ s_a E ∧ IsEntry M S.C E ∧
      (M.chainStateOf S.C E).h = h ∧ T.root = E.root := by
  obtain ⟨X, hXB, Q, hqA, hA⟩ := hJ
  refine (one_certificate_greater_than_threshold_at_real M F Fx) S A x R E s₀ t₀ H j w B T h tH htH hAdvQ
    hAgree hOld hB ⟨X, hXB, Q, hqA, fun v hv => ?_⟩ hH
  obtain ⟨a, h1, h2, h3, -, h5⟩ := hA v hv
  exact ⟨a, h1, h2, h3, h5⟩

/-- **The bound on the old attestations, carried to the honesty time of a step.** A bound on the
attestations of the validators honest at a real time `tH` bounds those of the validators honest at the
time of a step `k` whose time is at least `tH`.

Why: a validator outside the adversary set after every step whose time is `x[k].time` is outside it
after every step whose time is `tH`: such a step is at most `k` (corruption is permanent), or later
than `k` with its time squeezed between `x[k].time` and `tH ≤ x[k].time`, so at the time of `k`. The
later honesty time is the time of a step: at a real time no step has, honesty is vacuous.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, the run's facts and the
  environment's facts; `t₀`: the time before which the attestations are read; `tH`: the earlier
  honesty time; `k`: the step whose time is the later one; `H`: the bound.

Read aloud: the bound over the senders honest at `tH` holds for the senders honest at the time of any
step whose time is at least `tH`. -/
theorem oldAttestationsAtMostHonestAt_of_le_time (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {t₀ tH : ℝ} {H : ℕ} (k : ℕ) (htH : tH ≤ x.time k)
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ tH H) :
    OldAttestationsAtMostHonestAt M S A x t₀ (x.time k) H := by
  intro i t v a hl ht hHk hsent
  refine hOld i t v a hl ht ?_ hsent
  rw [Activity.not_mem_corruptedAtTime] at hHk ⊢
  intro i' hi' hc
  exact hHk i' (le_trans hi' htH) hc

/-- **The bound on the old attestations, from the senders honest at the send to the senders
honest at a time.** When every attestation an honest validator put on the wire at a tick before
`t₀` has height at most `H`, then for every time `tH`, every attestation a validator honest at `tH`
put on the wire at a tick before `t₀` has height at most `H`.

Why: `OldAttestationsAtMost` bounds every attestation a tick before `t₀` put on the wire, whatever
the sender's honesty after its tick, so it bounds those of the senders honest at `tH`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t₀`: the time before which the
  attestations are read; `tH`: the time at which the senders' honesty is read; `H`: the bound.

Read aloud: a bound on the attestations of the validators honest at the send bounds those of the
validators honest at any later or earlier time. -/
theorem oldAttestationsAtMostHonestAt_of_oldAttestationsAtMost (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t₀ tH H : ℕ)
    (hOld : OldAttestationsAtMost M S A x t₀ H) :
    OldAttestationsAtMostHonestAt M S A x t₀ tH H := by
  intro i t v a hl ht _ hs
  exact hOld i t v a hl (by exact_mod_cast ht) hs

/-- A bound on the attestations of the validators honest at `tH`, sent before `t₀`, bounds those of
the validators honest at any later time `tH' ≥ tH`, sent before any earlier time `t₀' ≤ t₀`.

Why: corruption is permanent, so a validator outside the adversary set at `tH'` is outside it at
`tH`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t₀' ≤ t₀`: the two times before which
  the attestations are read; `tH ≤ tH'`: the two times at which the senders' honesty is read; `H`:
  the bound.

Read aloud: the bound over the senders honest at `tH` holds for the senders honest later, and for
attestations sent earlier. -/
theorem oldAttestationsAtMostHonestAt_mono (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {t₀' t₀ tH tH' H : ℕ} (ht₀ : t₀' ≤ t₀) (htH : tH ≤ tH')
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ tH H) :
    OldAttestationsAtMostHonestAt M S A x t₀' tH' H := by
  intro i t v a hl ht hH hsent
  exact hOld i t v a hl (lt_of_lt_of_le ht (by exact_mod_cast ht₀)) ((not_mem_corruptedAtTime_of_le M) x R E htH hH) hsent

end GoldilocksCorrectness.Record.Proofs.Executions

