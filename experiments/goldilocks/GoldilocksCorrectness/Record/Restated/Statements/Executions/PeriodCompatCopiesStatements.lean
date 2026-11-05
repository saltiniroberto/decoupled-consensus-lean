module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodCompatCopies
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# PeriodCompatCopiesStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/PeriodCompatCopiesStatements.lean`,
over a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the period's step
lemmas with the compatible vote clause, namely a slot owed inside the period at most `s + k`, the
lock holders' invariant at a step, the attestations' clause at a step, a lock holder's vote on `B`'s
chain or two heights past `B`, and no fast block conflicting with `B`; each is the theorem of the
same name of `Record/Restated/Proofs/Executions/PeriodCompatCopies.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (CachesCompatibleWith ConfirmationUpdated LocksRevoked
  Opposes OpponentsOf LockedViableBlocks)
open GoldilocksCorrectness.Record.Statements.Routines (SupportVotes EarlyVotes)

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

omit [RootOrder] in
/-- **A slot whose previous votes were owed inside the period is at most `s + k`.** When the
period plus its recovery `max (Δ S) Δs` ends before the vote time of slot `s + k`, a slot `s'` whose
previous votes were owed inside the period has `s' ≤ s + k`.

Why: `M.voteTime S.C (s' − 1) + 2Δ = M.supportCutoff S.C (s' − 1) + Δ < b₁ + max (Δ S) Δs ≤
M.voteTime S.C (s + k)`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `s`: the hand-over slot; `Δs`: the sync delay; `b₀`, `b₁`: the start and the end
  of the period; `s'`: the slot.

Read aloud: the votes owed inside the period are all owed during the hand-over lock's life. -/
theorem owed_slot_le_k (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {s b₀ b₁ s' Δs : ℕ}
    -- the period plus its recovery `max (Δ S) Δs` ends before the vote time of slot `s + k`
    (hb₁ : b₁ + max (Δ S) Δs ≤ M.voteTime S.C (s + S.C.k)) (h : VotesOwedInPeriod M S Δs b₀ b₁ s') :
    s' ≤ s + S.C.k :=
  (GoldilocksCorrectness.Record.Proofs.Executions.owed_slot_le_k M F U) hb₁ h

/-- **Lemma 100, the step of the lock holder's invariant, under the compatible vote clause.**
`holderInv_step` (`Statements/Executions/PeriodHolderStatements.lean:243`) with
`VotesCompatibleAt` in place of `VotesExtendAt`: with `P : AsyncHyps M`, for a step `j` which, when it is
`w`'s tick, ticks to a clock value at least the hand-over cutoff and before the
lock's deadline, and which, when it is `w`'s restart, does not set its clock back, with roots
naming blocks among what honest validators hold up to the time of step `j + 1`: when `w`
satisfies `HolderInvAt` at `j`, its caches at `j` are compatible with `B`, and the votes of every
slot `s' ≥ s + 1` whose support cutoff is at or before `x[j + 1].time` satisfy `VotesCompatibleAt`, then `w`
satisfies `HolderInvAt` at `j + 1`.

Why: `holderInv_step`'s proof, whose one reading of the votes is the count of the opponents of
`B` at the revocation (`opponents_fewer_than_half_ofCompat`): a vote for a block compatible with
`B` does not oppose `B`.



The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`: the hypotheses; `j`: the step; `w`: the lock holder.

Roots name blocks until `x[j + 1].time`: as `holderInv_step`.

Read aloud: nothing that happens to a lock holder before the lock's deadline moves its lock or its
record off `B`'s chain, when the honest votes do not conflict with `B`. -/
theorem holderInv_step_ofCompat (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F : ℕ}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the sum of the two clock bounds is less than `Δ S`
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (P : AsyncHyps M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F release ΔRedeliver ΔClockAhead ΔClockBehind tW) (j : ℕ) (w : V)
    -- roots name blocks among what honest validators hold up to the time of step `j + 1`
    (hRoots : RootsNameBlocksUntil M A x (x.time (j + 1)))
    -- when step `j` is `w`'s tick, its clock value is at least the hand-over cutoff
    (hjT : ∀ c : ℕ, x.lbl j = Event.tick w c → M.supportCutoff S.C (s + 1) ≤ c)
    -- when step `j` is `w`'s restart, its clock value is at least `w`'s clock value before it
    (hR : ∀ (c : ℕ) (keep : Bool), x.lbl j = Event.restart w c keep → x.clockValue j w ≤ c)
    -- when step `j` is `w`'s tick, its clock value is less than the lock's deadline
    (hjd : ∀ c : ℕ, x.lbl j = Event.tick w c → c < M.voteTime S.C (s + S.C.k + 1))
    -- `w` satisfies `HolderInvAt` at `j`
    (hInv : HolderInvAt M S x s B j w)
    -- `w`'s caches at `j` are compatible with `B`
    (hC : CachesCompatibleWith M S B H (x.st j w))
    -- the votes of every slot `s' ≥ s + 1` whose support cutoff is at or before `x[j + 1].time` satisfy
    -- `VotesCompatibleAt`
    (hVotes : ∀ s' : ℕ, s + 1 ≤ s' → M.supportCutoff S.C s' ≤ x.time (j + 1) →
      VotesCompatibleAt M S A x s B Δs b₀ b₁ s') :
    HolderInvAt M S x s B (j + 1) w := by
  -- the premises are read up to a natural number at least `x.time (j + 1) + ΔClockAhead + Δ S`
  obtain ⟨T, hT⟩ := exists_nat_ge (x.time (j + 1) + ΔClockAhead + Δ S)
  have hA := E.ahead_nonneg
  exact
    (GoldilocksCorrectness.Record.Proofs.Executions.holderInv_step_ofCompat M F U R E hSkew)
      ((GoldilocksCorrectness.Record.Proofs.Executions.AsyncHyps.toUntil M F) P T) j w
      (by have := (Nat.cast_nonneg (α := ℝ) (Δ S)); linarith)
      (fun s' hl => by
        -- a tick to the vote time of `s'` at step `j` is at a real time at least that vote time minus `ΔClockAhead`
        have h1 := (E.tick_active j w _ hl).2.1
        have h2 := (GoldilocksCorrectness.Record.Proofs.Executions.time_mono M) x R (Nat.le_succ j)
        have h' : ((M.supportCutoff S.C s' : ℕ) : ℝ) ≤ T := by
          rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s',
            Nat.cast_add]
          linarith
        exact_mod_cast h')
      hRoots hjT hR hjd hInv hC hVotes

/-- **Lemma 101, the step, over the copied attestation clause and the compatible vote clause.**
`attestations_step_ofHeldEntry` (`Statements/Executions/PeriodChainBlockStatements.lean:171`) with
`VotesCompatibleAt` in place of `VotesExtendAt`: with `P : AsyncHypsOfChainBlock M`, with roots
naming blocks among what honest validators hold up to the time of step `j + 1`: when the
attestations sent at the steps before `j` are old, or name an entry compatible with `B` held by an
honest validator by their time, and the votes of every slot `s' ≥ s + 1` whose support cutoff is at or
before `x[j].time` satisfy `VotesCompatibleAt`, then the attestations sent at the steps before `j + 1`
are too.

Why: `attestations_step_ofHeldEntry`'s proof; the fast block an attestation's entry is taken from
is compatible with `B` (`fast_blocks_compatible_of_votes_updater_ofCompat`: a block conflicting
with `B` has as supporters only validators outside the honest voters, which outweigh the rest).



The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`: the hypotheses; `j`: the step.

Roots name blocks until `x[j + 1].time`: as `attestations_step_ofHeldEntry`.

A configuration in the hand-over window: a tick at step `j` to a clock value at most the
hand-over cutoff is covered by the fifth clause of the hand-over facts at that configuration when the
step is before the cutoff's real time, and is a tick to the cutoff by an updater of slot `s`, whose fast
blocks are compatible with `B` by the holders' clause, otherwise.

Read aloud: every honest attestation after the hand-over names a chain compatible with `B`,
through an entry an honest validator holds, when the honest votes do not conflict with `B`. -/
theorem attestations_step_ofHeldEntry_ofCompat (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F : ℕ}
    (P : AsyncHypsOfChainBlock M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind (((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind)) (j : ℕ)
    -- some configuration's real time lies in the hand-over facts' window
    (hWin : ∃ j₀ : ℕ, ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time j₀ ∧ x.time j₀ ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind)
    -- roots name blocks among what honest validators hold up to the time of step `j + 1`
    (hRoots : RootsNameBlocksUntil M A x (x.time (j + 1)))
    -- the attestations sent before step `j` are old, or compatible with `B` and held
    (hAtt : AttestationsCompatibleWithBeforeOfHeldEntry M S A x B H t₀ j)
    -- the votes of every slot `s' ≥ s + 1` whose support cutoff is at or before `x[j].time` satisfy
    -- `VotesCompatibleAt`
    (hVotes : ∀ s' : ℕ, s + 1 ≤ s' → M.supportCutoff S.C s' ≤ x.time j →
      VotesCompatibleAt M S A x s B Δs b₀ b₁ s') :
    AttestationsCompatibleWithBeforeOfHeldEntry M S A x B H t₀ (j + 1) := by
  -- the premises are read up to a natural number at least `x.time (j + 1) + ΔClockAhead`
  obtain ⟨T, hT⟩ := exists_nat_ge (x.time (j + 1) + ΔClockAhead)
  exact
    (GoldilocksCorrectness.Record.Proofs.Executions.attestations_step_ofHeldEntry_ofCompat M F U R E)
      hNet hSkew hRedeliver ((GoldilocksCorrectness.Record.Proofs.Executions.AsyncHypsOfChainBlock.toUntil M F) P T) j
      (fun v c hl => by
        -- a tick at step `j` to `c` is at a real time at least `c − ΔClockAhead`
        have h1 := (E.tick_active j v c hl).2.1
        have h2 := (GoldilocksCorrectness.Record.Proofs.Executions.time_mono M) x R (Nat.le_succ j)
        have h' : (c : ℝ) ≤ T := by linarith
        exact_mod_cast h')
      hWin le_rfl hRoots hAtt hVotes

/-- **A lock holder's vote during the hand-over lock's life is on `B`'s chain, under the
compatible vote clause.** `holder_vote_extends_B_orTwoPast`
(`Statements/Executions/PeriodChainBlockStatements.lean:362`) with `VotesCompatibleAt` in place of
`VotesExtendAt` for slot `s' − 1`: with `P : AsyncHyps M`, at a slot `s'` with
`s + 2 ≤ s' ≤ s + k`, with roots naming blocks among what honest validators hold up to the real
time of `w`'s own tick to the vote time of `s'`, with the clock bounds' sum less than
`Δ S`, for a validator `w` that satisfies `HolderInvAt` at the step of its tick to the vote
time of `s'`, whose caches there are compatible with `B`, whose held blocks there at a chain-state
height at least `h(B) + 2` descend from `B`, and whose finality gadget there is not contested or
has `h_max ≥ h(B) + 2`: every slot-`s'` vote `w` puts on the wire at its tick at the vote time of
`s'` names a block it holds that is `B` or a descendant of `B`.

Why: `holder_vote_extends_B_orTwoPast`'s proof, whose one reading of the votes is the count of the
opponents of `B` at the revocation (`opponents_fewer_than_half_ofCompat`).



The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`: the hypotheses; `s'`: the slot of the vote; `w`: the voter.

Roots name blocks up to `w`'s own tick to `M.voteTime S.C s'`: `opponents_fewer_than_half_ofCompat`
at the revocation `w`'s tick runs, which reads `w`'s state at that step and each opponent's block at
the opponent's own earlier tick.

Read aloud: a validator holding the lock votes on `B`'s chain at every slot of the lock's life,
when the previous slot's honest votes do not conflict with `B`. -/
theorem holder_vote_extends_B_orTwoPast_ofCompat (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the sum of the two clock bounds is less than `Δ S`
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F : ℕ}
    (P : AsyncHyps M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F release ΔRedeliver ΔClockAhead ΔClockBehind tW) (s' : ℕ) (w : V)
    -- roots name blocks among what honest validators hold up to the real time of `w`'s own tick to the vote time of `s'`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.voteTime S.C s'))))
    -- `s + 2 ≤ s' ≤ s + k`
    (hs' : s + 2 ≤ s') (hs'k : s' ≤ s + S.C.k)
    -- `w`'s lock and record at the step of its tick to the vote time
    (hInv : HolderInvAt M S x s B (x.tickStep w (M.voteTime S.C s')) w)
    -- `w`'s caches there are compatible with `B`
    (hC : CachesCompatibleWith M S B H (x.tickInput w (M.voteTime S.C s')))
    -- every block `w` holds there at a chain-state height at least `h(B) + 2` descends from `B`
    (hTwo : ∀ D ∈ (x.tickInput w (M.voteTime S.C s')).tree,
      (M.chainStateOf S.C B).h + 2 ≤ (M.chainStateOf S.C D).h → B.AncestorEq D)
    -- `w`'s finality gadget there is not contested, or its `h_max` is at least `h(B) + 2`
    (hNC : M.fg_contest (x.tickInput w (M.voteTime S.C s')) = false ∨
      (M.chainStateOf S.C B).h + 2 ≤ hMax M S.C (x.tickInput w (M.voteTime S.C s')))
    -- the votes of slot `s' − 1` satisfy `VotesCompatibleAt`
    (hVotes : VotesCompatibleAt M S A x s B Δs b₀ b₁ (s' - 1)) :
    ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C s') ∧
        (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput w (M.voteTime S.C s')).tree,
        vote = GoldfishVote.mk w s' H_u.root ∧ B.AncestorEq H_u :=
  (GoldilocksCorrectness.Record.Proofs.Executions.holder_vote_extends_B_orTwoPast_ofCompat M F U R E hSkew)
    ((GoldilocksCorrectness.Record.Proofs.Executions.AsyncHyps.toUntil M F) P (M.supportCutoff S.C s'))
    s' w le_rfl hRoots hs' hs'k hInv hC hTwo hNC hVotes

/-! ## A reader of the original vote clause -/

section Readers

variable (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)

/-- **The fast blocks of every honest update inside and after the period are compatible with
`B`.** With `P : AsyncHyps M`, at a slot `s' ≥ s + 1` whose votes satisfy `VotesExtendAt`, with
roots naming blocks among what honest validators hold up to the real time of `u`'s own tick to the support cutoff of
slot `s' + 1`,
every fast block of the state right after the update of slot `s'` at a validator `u` of
`honestActiveAt M S Sched s'` is compatible with `B`.

Why: a block off `B`'s chain is supported only by voters whose vote does not extend `B` and by
equivocators, all outside `holdersAt M S Sched s s'` (and outside `honestActiveAt M S Sched s'` when
slot `s'`'s previous votes were not owed inside the period): fewer than half of the committee of
`s'`, by `HoldersOutweighWhereOwed` at `s'` or `CommitteeSleepiness` at `s' + 1`; and `fast_test`
compares the score with the committee's size (`fast_test_fails_of_minority`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`: the hypotheses; `s'`: the slot of the update; `u`: the validator;
- `hs'`: `s + 1 ≤ s'`; `hu`: `u` is honest and active at slot `s'`; `hVotes`: the votes of slot
  `s'` satisfy `VotesExtendAt`.



Roots name blocks up to `u`'s own tick to `M.supportCutoff S.C (s' + 1)`: the block of the tree of `M.fg_to_ac` of the
state that tick starts from which a supporter's vote names is compared with the block the supporter held at its own tick
to the vote time, before `u`'s tick (`hSkew`).

Read aloud: no block off `B`'s chain ever passes the fast test at anyone. -/
theorem fast_blocks_compatible_of_votes (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F : ℕ}
    (P : AsyncHyps M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F release ΔRedeliver ΔClockAhead ΔClockBehind tW) (s' : ℕ) (u : V)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep u (M.supportCutoff S.C (s' + 1)))))
    (hs' : s + 1 ≤ s') (hu : u ∈ honestActiveAt M S A x s')
    (hVotes : VotesExtendAt M S A x s B Δs b₀ b₁ s') :
    ∀ D ∈ (x.tickOutput u (M.supportCutoff S.C (s' + 1))).fastBlocks,
      D.compatible B = true :=
  (GoldilocksCorrectness.Record.Proofs.Executions.fast_blocks_compatible_of_votes M F U R E) P s' u
    hRoots hs' hu hVotes

end Readers

end GoldilocksCorrectness.Record.Statements.Executions

