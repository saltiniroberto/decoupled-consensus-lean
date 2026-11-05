module
public import GoldilocksCorrectness.Proofs.Executions.PeriodInductionCompat

@[expose] public section

/-!  Proved in `GoldilocksCorrectness/Proofs/Executions/PeriodInductionCompat.lean`.
Write `h(X)` for `(chainStateOf S.C X).h`, the chain-state height of a block `X`.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (voteTime supportCutoff)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Statements.Routines (CachesCompatibleWith)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Statement 1′: the vote of a timely slot is on `B`'s chain, or compatible with `B` from a
voter justified past `B`.** Under the hypotheses `P` of the period after the hand-over slot `s`
(with `GST` at or before the vote time of slot `s + 1`), with roots naming blocks among what
honest validators hold up to the vote time of `s'`: take a slot `s' ≥ s + 2` whose previous
slot's votes were not owed inside the period, and a validator `u ∈ honestActiveAt S Sched s'`
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
- `P`: the hypotheses of the period; `s'`: the slot of the vote; `u`: the voter.

Read aloud: at a timely slot, an honest active voter votes on `B`'s chain, or votes for a block that
does not conflict with `B` with its finality gadget justified past `B`. -/
theorem vote_compatible_of_timely_view {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    -- the hypotheses of the period, with `GST` at or before the vote time of slot `s + 1`
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁)
    (s' : ℕ) (u : V)
    -- roots name blocks among what honest validators hold up to the vote time of `s'`
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S s'))
    -- the slot is at least two after the hand-over slot
    (hs' : s + 2 ≤ s')
    -- the votes of slot `s' − 1` were not owed inside the period
    (hgood : ¬ VotesOwedInPeriod S b₀ b₁ s')
    -- `u` is awake through the duties of `s'` and honest at its update
    (hu : u ∈ honestActiveAt S Sched s')
    -- `u`'s caches before the vote time of `s'` are compatible with `B`
    (hC : CachesCompatibleWith S B H (stateBefore x (voteTime S s') u))
    -- every block `u` holds then two heights past `B` descends from `B`
    (hTwo : ∀ D ∈ (stateBefore x (voteTime S s') u).S.T,
      (chainStateOf S.C B).h + 2 ≤ (chainStateOf S.C D).h → B.AncestorEq D)
    -- `u` is not contested then, or its top height is at least `h(B) + 2`
    (hNC : fg_contest (stateBefore x (voteTime S s') u).S = false ∨
      (chainStateOf S.C B).h + 2 ≤ (stateBefore x (voteTime S s') u).S.h_max)
    -- every honest active voter of `s' − 1` has caches compatible with `B` before its vote
    (hCprev : ∀ w ∈ honestActiveAt S Sched (s' - 1),
      CachesCompatibleWith S B H (stateBefore x (voteTime S (s' - 1)) w))
    -- the votes of slot `s' − 1` satisfy `VotesCompatibleAt`
    (hVotes : VotesCompatibleAt S Sched x s B b₀ b₁ (s' - 1)) :
    ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S s') u).S.T,
        vote = GoldfishVote.mk u s' H_u.root ∧
        (B.AncestorEq H_u ∨ (H_u.compatible B = true ∧
          (chainStateOf S.C B).h + 1 ≤ (stateBefore x (voteTime S s') u).S.h_j)) :=
  GoldilocksCorrectness.Proofs.Executions.vote_compatible_of_timely_view P s' u hRoots hs' hgood hu
    hC hTwo hNC hCprev hVotes

/-- **Statement 2′: no honest confirmation of a timely slot conflicts with `B`.** Under the
hypotheses `P` of the period after the hand-over slot `s`, with roots naming blocks among what
honest validators hold up to the support cutoff of `s'`: take a slot `s' ≥ s + 1` whose votes are
due by its support cutoff, a validator `v ∈ honestActiveAt S Sched s'` whose finalized block
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
- `P`: the hypotheses of the period; `s'`: the slot; `v`: the validator whose update it is.

Read aloud: once the votes of a slot are due by its support cutoff, no honest confirmation of that
slot conflicts with `B`. -/
theorem confirmation_compatible_of_timely_votes {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    -- the hypotheses of the period, with `GST` at or before the vote time of slot `s + 1`
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁)
    (s' : ℕ) (v : V)
    -- roots name blocks among what honest validators hold up to the support cutoff of `s'`
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s'))
    -- the slot is after the hand-over slot, and its votes are due by its support cutoff
    (hs' : s + 1 ≤ s') (hgood : VotesDueByCutoff S b₀ b₁ s')
    -- `v` is awake through the duties of `s'` and honest at its update
    (hv : v ∈ honestActiveAt S Sched s')
    -- `v`'s finalized block before the support cutoff of `s' + 1` is compatible with `B`
    (hF : (stateBefore x (supportCutoff S (s' + 1)) v).S.F.compatible B = true)
    -- the votes of slot `s'` satisfy `VotesCompatibleAt`
    (hVotes : VotesCompatibleAt S Sched x s B b₀ b₁ s') :
    ∀ C' : Block V,
      (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C' →
      C'.compatible B = true :=
  GoldilocksCorrectness.Proofs.Executions.confirmation_compatible_of_timely_votes P s' v hRoots hs'
    hgood hv hF hVotes

/-- **Statement 3′: the joint invariant of the period under the compatible vote clause, for
ever.** Under the hypotheses `P` of the period after the hand-over slot `s`: at every step `j`
whose time is after the hand-over cutoff `supportCutoff S (s + 1)`, with roots naming blocks among
what honest validators hold up to `x[j].time`, `PeriodInvCompatDueByCutoff` holds at `j`.

Why: strong induction on the step from the configuration right after the hand-over update. The
base is the hand-over facts. At a step, the sixth clause at a slot `s' ≥ s + 2` comes from the
invariant at the step before the vote time of `s'` (the holders by
`holder_vote_extends_B_orTwoPast_ofCompat` during the lock's life, the honest active voters of a
timely slot by statement 1′, or at `s' = s + 2` by its core with the hand-over votes); the first by
`holderInv_step_ofCompat`; the fifth, fourth and third by the attestation, certificate and cache
steps; the seventh by statement 2′; the second by the first before the lock's deadline, and after
it by the holder's own update, whose saved confirmation is compatible with `B` and, written over a
record on `B`'s chain, is `B` or a descendant of `B`.



The variables:
- `P`: the hypotheses of the period.

Read aloud: the hand-over facts carry for ever in the weakened form: at every step after the
hand-over update, given that roots name blocks by that step's time, the seven clauses hold, with
votes and confirmations compatible with `B`. -/
theorem period_inv_compat_all {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    -- the hypotheses of the period, with `GST` at or before the vote time of slot `s + 1`
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁) :
    ∀ j : ℕ, supportCutoff S (s + 1) < x[j].time → RootsNameBlocksUntil S Sched x x[j].time →
      PeriodInvCompatDueByCutoff S Sched x s B H t₀ b₀ b₁ j :=
  GoldilocksCorrectness.Proofs.Executions.period_inv_compat_all P

/-- **Lemma 104′: from slot `s + k + 1` on, no honest vote or confirmation conflicts with `B`.**
Under the hypotheses `P` of the period after the hand-over slot `s`: at every slot
`s' ≥ s + k + 1`, with roots naming blocks among what honest validators hold up to the support
cutoff of `s' + 1`, the votes of `s'` satisfy `VotesCompatibleAt` (every honest active vote is on
`B`'s chain, or for a block compatible with `B` from a voter justified past `B`), and every
confirmation an honest active validator of `s'` saves for `s'` is compatible with `B`.

Why: statement 3′ at the step before the update of `s'`: its sixth clause at `s'`, and its third
clause for the finalized block with statement 2′ (the votes of `s'` are due by its support cutoff,
the period having ended by `voteTime S (s + k)`).



The variables:
- `P`: the hypotheses of the period.

Read aloud: from slot `s + k + 1` on, every honest active vote is on `B`'s chain or comes from a
voter justified past `B` and does not conflict with `B`, and no honest confirmation conflicts with
`B`. -/
theorem after_period_compat {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    -- the hypotheses of the period, with `GST` at or before the vote time of slot `s + 1`
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁) :
    ∀ s' : ℕ, s + S.C.k + 1 ≤ s' → RootsNameBlocksUntil S Sched x (supportCutoff S (s' + 1)) →
      VotesCompatibleAt S Sched x s B b₀ b₁ s' ∧
      ∀ v ∈ honestActiveAt S Sched s', ∀ C' : Block V,
        (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C' →
        C'.compatible B = true :=
  GoldilocksCorrectness.Proofs.Executions.after_period_compat P

/-- **The certificate corollary.** Under the hypotheses `P` of the period after the hand-over slot
`s`, with roots naming blocks: at every step, every certificate at a height greater than `H` on a
held chain, for a block of that chain, is for a block compatible with `B`.

Why: after the hand-over cutoff, statement 3′'s fourth clause; at or before it, the hand-over
facts' attestation clause at every earlier step, and the certificate step.

Stated as v3's statement 6, now through
`period_inv_compat_all`.

The variables:
- `P`: the hypotheses of the period; `hRoots`: roots name blocks.

Read aloud: no honest validator ever holds a chain with a certificate at a height greater than `H`
for a block of that chain conflicting with `B`. -/
theorem certificates_compatible_with_ofChainBlock {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    -- the hypotheses of the period, with `GST` at or before the vote time of slot `s + 1`
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁)
    -- roots name blocks among what honest validators ever hold
    (hRoots : RootsNameBlocks S Sched x) :
    CertificatesCompatibleWithOfChainBlock S Sched x H B :=
  GoldilocksCorrectness.Proofs.Executions.certificates_compatible_with_ofChainBlock P hRoots

/-- **The two-past corollary.** Under the hypotheses `P` of the period after the hand-over slot
`s`, with roots naming blocks: at every step, every block an honest validator holds at a
chain-state height at least `h(B) + 2` is `B` or a descendant of `B`.

Why: the certificate corollary at every step, and `blocksTwoPastDescend_at_ofChainBlock`.

Stated as v3's statement 6, now through
`period_inv_compat_all`.

The variables:
- `P`: the hypotheses of the period; `hRoots`: roots name blocks.

Read aloud: a chain conflicting with `B` gains at most one height past `B`'s. -/
theorem blocks_two_past_descend {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    -- the hypotheses of the period, with `GST` at or before the vote time of slot `s + 1`
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁)
    -- roots name blocks among what honest validators ever hold
    (hRoots : RootsNameBlocks S Sched x) :
    BlocksTwoPastDescend S Sched x B :=
  GoldilocksCorrectness.Proofs.Executions.blocks_two_past_descend P hRoots

end GoldilocksCorrectness.Statements.Executions
