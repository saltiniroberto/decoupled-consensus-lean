module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodInductionCompat
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# PeriodInductionCompatStatements, over a model

The statements of
`GoldilocksCorrectness/Statements/Executions/PeriodInductionCompatStatements.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: the asynchronous period under the
compatible vote clause, namely an honest active vote at a timely slot on `B`'s chain or compatible
with `B` from a voter justified past `B`, no honest confirmation of a timely slot conflicting with
`B`, the joint induction `PeriodInvCompatDueByCutoff` at every step after the hand-over update,
Lemma 104 with the compatible vote clause, and its two corollaries; each is the theorem of the same
name of `Record/Restated/Proofs/Executions/PeriodInductionCompat.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (voteTime supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (CachesCompatibleWith HeadOf)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Statement 1′: the vote of a timely slot is on `B`'s chain, or compatible with `B` from a
voter justified past `B`.** Under the hypotheses `P` of the period after the hand-over slot `s`
(with `GST` at or before the vote time of slot `s + 1`), with roots naming blocks among what
honest validators hold up to the later of the vote time of `s'` and the real time of `u`'s own tick
to it (the vote time for the delivery line `DelTLine`, the tick for `u`'s own state): take a slot `s' ≥ s + 2` whose previous
slot's votes were not owed inside the period, and a validator `u ∈ honestActiveAt M S Sched s'`
whose state before the vote time of `s'` has caches compatible with `B`, holds only descendants
of `B` at chain-state heights at least `h(B) + 2`, and is not contested or has `h_max` at least
`h(B) + 2`; let every honest active voter of `s' − 1` have caches compatible with `B` before its
own vote, and the votes of `s' − 1` satisfy `VotesCompatibleAt`. Then every slot-`s'` vote `u`
puts on the wire at its tick at the vote time of `s'` is `u`'s vote for a block `H_u` it holds
that is `B` or a descendant of `B`, or that is compatible with `B` while `u`'s justification
height is at least `h(B) + 1`.

Why: when `u`'s justification height is at least `h(B) + 1`, every viable head of `u`'s state
descends from `B`, and the vote's head is compatible with `B`. Otherwise, when `B` is a strict
ancestor of `u`'s finalized block, the vote's head descends from that block. Otherwise `u` is
not contested; every vote of `s' − 1` that the induction counts is on `B`'s chain (a vote of an
honest active voter justified past `B` would spread its justification to `u` before its vote,
`justified_past_spreads`); those votes reach `u` before its view freeze, the locks the revocation
leaves are compatible with `B`, a viable head of `u`'s voter tree is on `B`'s chain (`B` itself,
or the certified entry one height under `u`'s top height, which an honest attester held), and
Lemma 26b from held votes puts the vote on `B`'s chain.

  every hypothesis is
read (`hNC` excludes the contested case when `u`'s justification height is at most `h(B)`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `P`: the hypotheses of the period; `s'`: the slot of the vote; `u`: the voter.

Read aloud: at a timely slot, an honest active voter votes on `B`'s chain, or votes for a block that
does not conflict with `B` with its finality gadget justified past `B`. -/
theorem vote_compatible_of_timely_view (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs_F : ℕ}
    -- the hypotheses of the period, with `GST` at or before the vote time of slot `s + 1`
    (P : AsyncHypsOfChainBlockGSTBeforeVotes M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet tW)
    (s' : ℕ) (u : V)
    -- roots name blocks among what honest validators hold up to the later of the vote time of `s'` and `u`'s own tick to it
    (hRoots : RootsNameBlocksUntil M A x (max ((M.voteTime S.C s' : ℕ) : ℝ) (x.time (x.tickStep u (M.voteTime S.C s')))))
    -- the slot is at least two after the hand-over slot
    (hs' : s + 2 ≤ s')
    -- the votes of slot `s' − 1` were not owed inside the period
    (hgood : ¬ VotesOwedInPeriod M S Δs b₀ b₁ s')
    -- `u` is awake through the duties of `s'` and honest at its update
    (hu : u ∈ honestActiveAt M S A x s')
    -- `u`'s caches before the vote time of `s'` are compatible with `B`
    (hC : CachesCompatibleWith M S B H (x.tickInput u (M.voteTime S.C s')))
    -- every block `u` holds then two heights past `B` descends from `B`
    (hTwo : ∀ D ∈ (x.tickInput u (M.voteTime S.C s')).tree,
      (M.chainStateOf S.C B).h + 2 ≤ (M.chainStateOf S.C D).h → B.AncestorEq D)
    -- `u` is not contested then, or its top height is at least `h(B) + 2`
    (hNC : M.fg_contest (x.tickInput u (M.voteTime S.C s')) = false ∨
      (M.chainStateOf S.C B).h + 2 ≤ hMax M S.C (x.tickInput u (M.voteTime S.C s')))
    -- every honest active voter of `s' − 1` has caches compatible with `B` at its tick to its vote time
    (hCprev : ∀ w ∈ honestActiveAt M S A x (s' - 1),
      CachesCompatibleWith M S B H (x.tickInput w (M.voteTime S.C (s' - 1))))
    -- the votes of slot `s' − 1` satisfy `VotesCompatibleAt`
    (hVotes : VotesCompatibleAt M S A x s B Δs b₀ b₁ (s' - 1)) :
    ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C s')).tree,
        vote = GoldfishVote.mk u s' H_u.root ∧
        (B.AncestorEq H_u ∨ (H_u.compatible B = true ∧
          (M.chainStateOf S.C B).h + 1 ≤ (x.tickInput u (M.voteTime S.C s')).justifiedHeight))
              :=
  (GoldilocksCorrectness.Record.Proofs.Executions.vote_compatible_of_timely_view M F U Fx R E hNet hSkew hRedeliver hΔs)
    ((GoldilocksCorrectness.Record.Proofs.Executions.AsyncHypsOfChainBlockGSTBeforeVotes.toUntil M F) P (M.supportCutoff S.C s')) s' u
    le_rfl hRoots hs' hgood hu hC hTwo hNC hCprev hVotes

/-- **Statement 2′: no honest confirmation of a timely slot conflicts with `B`.** Under the
hypotheses `P` of the period after the hand-over slot `s`, with roots naming blocks among what
honest validators hold up to the support cutoff of `s'`: take a slot `s' ≥ s + 1` whose votes are
due by its support cutoff, a validator `v ∈ honestActiveAt M S Sched s'` whose finalized block
before the support cutoff of `s' + 1` is compatible with `B`, and let the votes of `s'` satisfy
`VotesCompatibleAt`. Then the confirmation `v`'s update at that cutoff saves for `s'`, when there
is one, is compatible with `B`.

Why: the voters whose votes `VotesCompatibleAt` makes compatible with `B` (the lock holders where
the previous votes were owed, the honest active committee members otherwise) outweigh the rest of
the committee (`voters_compatible_majority`); Lemma 78c, or its twin when the votes are due before
the period.


 every
hypothesis is read.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`: the hypotheses of the period; `s'`: the slot; `v`: the validator whose update it is.

Read aloud: once the votes of a slot are due by its support cutoff, no honest confirmation of that
slot conflicts with `B`. -/
theorem confirmation_compatible_of_timely_votes (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs_F : ℕ}
    -- the hypotheses of the period, with `GST` at or before the vote time of slot `s + 1`
    (P : AsyncHypsOfChainBlockGSTBeforeVotes M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet tW)
    (s' : ℕ) (v : V)
    -- roots name blocks among what honest validators hold up to the real time of `v`'s own tick to the support
    -- cutoff of `s'`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C s'))))
    -- the slot is after the hand-over slot, and its votes are due by its support cutoff
    (hs' : s + 1 ≤ s') (hgood : VotesDueByCutoff M S Δs b₀ b₁ s')
    -- `v` is awake through the duties of `s'` and honest at its update
    (hv : v ∈ honestActiveAt M S A x s')
    -- the finalized block `v`'s tick to the support cutoff of `s' + 1` reads is compatible with `B`
    (hF : (x.tickInput v (M.supportCutoff S.C (s' + 1))).finalized.compatible B = true)
    -- the votes of slot `s'` satisfy `VotesCompatibleAt`
    (hVotes : VotesCompatibleAt M S A x s B Δs b₀ b₁ s') :
    ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' →
      C'.compatible B = true :=
  (GoldilocksCorrectness.Record.Proofs.Executions.confirmation_compatible_of_timely_votes M F U R E hNet hSkew hRedeliver hΔs)
    ((GoldilocksCorrectness.Record.Proofs.Executions.AsyncHypsOfChainBlockGSTBeforeVotes.toUntil M F) P (M.supportCutoff S.C (s' + 1)))
    s' v le_rfl hRoots hs' hgood hv hF hVotes

/-- **Statement 3′: the joint invariant of the period under the compatible vote clause, for
ever.** Under the hypotheses `P` of the period after the hand-over slot `s`: at every step `j`
after every updater's tick to the hand-over cutoff `M.supportCutoff S.C (s + 1)` and at a time at least that cutoff
, with roots naming blocks
among what honest validators hold up to `x[j].time`, `PeriodInvCompatDueByCutoff` holds at `j`.

Why: strong induction on the step from the configuration right after the hand-over update. The
base is the hand-over facts. At a step, the sixth clause at a slot `s' ≥ s + 2` comes from the
invariant at the step before the vote time of `s'` (the holders by
`holder_vote_extends_B_orTwoPast_ofCompat` during the lock's life, the honest active voters of a
timely slot by statement 1′, or at `s' = s + 2` by its core with the hand-over votes); the first by
`holderInv_step_ofCompat`; the fifth, fourth and third by the attestation, certificate and cache
steps; the seventh by statement 2′; the second by the first before the lock's deadline, and after
it by the holder's own update, whose saved confirmation is compatible with `B` and, written over a
record on `B`'s chain, is `B` or a descendant of `B`.



A configuration in the hand-over window: some configuration's real time is
at least the hand-over cutoff `M.supportCutoff S.C (s + 1)` and at most `ΔClockBehind` after it, where the hand-over
facts' third to fifth clauses say something; Lemma 101's step and the induction's base read the fifth
clause there.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `P`: the hypotheses of the period.

Read aloud: the hand-over facts carry for ever in the weakened form: at every step after the
hand-over update, given that roots name blocks by that step's time, the seven clauses hold, with
votes and confirmations compatible with `B`. -/
theorem period_inv_compat_all (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs_F : ℕ}
    -- the hypotheses of the period, with `GST` at or before the vote time of slot `s + 1`
    (P : AsyncHypsOfChainBlockGSTBeforeVotes M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet (((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind))
    -- some configuration's real time lies in the hand-over facts' window
    (hWin : ∃ j₀ : ℕ, ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time j₀ ∧ x.time j₀ ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind) :
    ∀ j : ℕ, (∀ w ∈ updaterAt M S A x s, x.tickStep w (M.supportCutoff S.C (s + 1)) < j) →
      M.supportCutoff S.C (s + 1) ≤ x.time j → RootsNameBlocksUntil M A x (x.time j) →
      PeriodInvCompatDueByCutoff M S A x s B H t₀ Δs b₀ b₁ j := by
  intro j hj hj' hR
  -- the premises read up to a natural number at least the time of `j` plus `ΔClockAhead`, which every tick
  -- before `j` respects
  obtain ⟨T, hT⟩ := exists_nat_ge (x.time j + ΔClockAhead)
  have hA0 := E.ahead_nonneg
  exact (GoldilocksCorrectness.Record.Proofs.Executions.period_inv_compat_all M F U Fx R E hNet hSkew hRedeliver hΔs)
    ((GoldilocksCorrectness.Record.Proofs.Executions.AsyncHypsOfChainBlockGSTBeforeVotes.toUntil M F) P T) hWin j hj hj'
    (by linarith)
    (fun k v c' hk hl => (GoldilocksCorrectness.Record.Proofs.Executions.tick_clock_le_of_time_le M F) E hT k v c'
      ((GoldilocksCorrectness.Record.Proofs.Executions.time_mono M) x R hk.le) hl) hR

/-- **Lemma 104′: from slot `s + k + 1` on, no honest vote or confirmation conflicts with `B`.**
Under the hypotheses `P` of the period after the hand-over slot `s`: at every slot
`s' ≥ s + k + 1`, with roots naming blocks among what honest validators hold up to every
validator's tick to the support cutoff of `s' + 1`, the votes of `s'` satisfy `VotesCompatibleAt` (every honest active vote is on
`B`'s chain, or for a block compatible with `B` from a voter justified past `B`), and every
confirmation an honest active validator of `s'` saves for `s'` is compatible with `B`.

Why: statement 3′, in the form at the steps after every updater's tick to the hand-over cutoff, at
an honest active validator's own tick to the support cutoff of `s' + 1`: its sixth clause at `s'`, and
its third clause for that validator's finalized block with statement 2′ (the votes of `s'` are due by
its support cutoff, the period having ended by `M.voteTime S.C (s + k)`).



A configuration in the hand-over window: some configuration's real time is
at least the hand-over cutoff `M.supportCutoff S.C (s + 1)` and at most `ΔClockBehind` after it, where the hand-over
facts' third to fifth clauses say something; Lemma 101's step and the induction's base read the fifth
clause there.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `P`: the hypotheses of the period.

Read aloud: from slot `s + k + 1` on, every honest active vote is on `B`'s chain or comes from a
voter justified past `B` and does not conflict with `B`, and no honest confirmation conflicts with
`B`. -/
theorem after_period_compat (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs_F : ℕ}
    -- the hypotheses of the period, with `GST` at or before the vote time of slot `s + 1`
    (P : AsyncHypsOfChainBlockGSTBeforeVotes M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet (((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind))
    -- some configuration's real time lies in the hand-over facts' window
    (hWin : ∃ j₀ : ℕ, ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time j₀ ∧ x.time j₀ ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind) :
    ∀ s' : ℕ, s + S.C.k + 1 ≤ s' →
      (∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (s' + 1)) →
        RootsNameBlocksUntil M A x (x.time k)) →
      VotesCompatibleAt M S A x s B Δs b₀ b₁ s' ∧
      ∀ v ∈ honestActiveAt M S A x s', ∀ C' : Block V,
        (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' →
        C'.compatible B = true :=
  (GoldilocksCorrectness.Record.Proofs.Executions.after_period_compat M F U Fx R E hNet hSkew hRedeliver hΔs) P hWin

/-- **The certificate corollary.** Under the hypotheses `P` of the period after the hand-over slot
`s`, with roots naming blocks: at every step, every certificate at a height greater than `H` on a
held chain, for a block of that chain, is for a block compatible with `B`.

Why: statement 3′, in the form at the steps after every updater's tick to the hand-over cutoff, at
a step after the given one, after every such tick and at a real time at least that cutoff: its
attestation clause covers every attestation sent before the given step, and the certificate step
concludes there.

Stated as v3's statement 6, now through
`period_inv_compat_all`.

A configuration in the hand-over window: some configuration's real time is
at least the hand-over cutoff `M.supportCutoff S.C (s + 1)` and at most `ΔClockBehind` after it, where the hand-over
facts' third to fifth clauses say something; Lemma 101's step and the induction's base read the fifth
clause there.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `P`: the hypotheses of the period; `hRoots`: roots name blocks.

Read aloud: no honest validator ever holds a chain with a certificate at a height greater than `H`
for a block of that chain conflicting with `B`. -/
theorem certificates_compatible_with_ofChainBlock (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs_F : ℕ}
    -- the hypotheses of the period, with `GST` at or before the vote time of slot `s + 1`
    (P : AsyncHypsOfChainBlockGSTBeforeVotes M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet (((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind))
    -- some configuration's real time lies in the hand-over facts' window
    (hWin : ∃ j₀ : ℕ, ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time j₀ ∧ x.time j₀ ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind)
    -- roots name blocks among what honest validators ever hold
    (hRoots : RootsNameBlocks M A x) :
    CertificatesCompatibleWithOfChainBlock M A x H B :=
  (GoldilocksCorrectness.Record.Proofs.Executions.certificates_compatible_with_ofChainBlock M F U Fx R E hNet hSkew hRedeliver hΔs)
    P hWin hRoots

/-- **The two-past corollary.** Under the hypotheses `P` of the period after the hand-over slot
`s`, with roots naming blocks: at every step, every block an honest validator holds at a
chain-state height at least `h(B) + 2` is `B` or a descendant of `B`.

Why: the certificate corollary at every step, and `blocksTwoPastDescend_at_ofChainBlock`.

Stated as v3's statement 6, now through
`period_inv_compat_all`.

A configuration in the hand-over window: some configuration's real time is
at least the hand-over cutoff `M.supportCutoff S.C (s + 1)` and at most `ΔClockBehind` after it, where the hand-over
facts' third to fifth clauses say something; Lemma 101's step and the induction's base read the fifth
clause there.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `P`: the hypotheses of the period; `hRoots`: roots name blocks.

Read aloud: a chain conflicting with `B` gains at most one height past `B`'s. -/
theorem blocks_two_past_descend (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs_F : ℕ}
    -- the hypotheses of the period, with `GST` at or before the vote time of slot `s + 1`
    (P : AsyncHypsOfChainBlockGSTBeforeVotes M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet (((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind))
    -- some configuration's real time lies in the hand-over facts' window
    (hWin : ∃ j₀ : ℕ, ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time j₀ ∧ x.time j₀ ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind)
    -- roots name blocks among what honest validators ever hold
    (hRoots : RootsNameBlocks M A x) :
    BlocksTwoPastDescend M S A x B :=
  (GoldilocksCorrectness.Record.Proofs.Executions.blocks_two_past_descend M F U Fx R E hNet hSkew hRedeliver hΔs) P hWin hRoots

end GoldilocksCorrectness.Record.Statements.Executions

