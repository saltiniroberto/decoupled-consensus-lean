module
public import GoldilocksCorrectness.Statements.Executions.PeriodInductionDefs

@[expose] public section

/-! The
originals (`VotesExtendAt`, `PeriodInvOfChainBlockDueByCutoff`) stay byte-identical;

- `VotesCompatibleAt`, the copy of `VotesExtendAt`: the lock holders' conjunct is kept only at
  slots `s' ≤ s + k`, and an honest active vote of a slot whose previous votes were not owed in
  the period is on `B`'s chain, or is for a block compatible with `B` cast by a voter whose
  justification height before the vote is at least `h(B) + 1`;
- `PeriodInvCompatDueByCutoff`, the copy of `PeriodInvOfChainBlockDueByCutoff` whose sixth
  clause reads `VotesCompatibleAt` and whose seventh clause concludes compatibility with `B`;
- `votesCompatibleAt_of_votesExtendAt`, the conversion the induction's base reads.

Write `h(X)` for `(chainStateOf S.C X).h`, the chain-state height of a block `X`.
-/

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (voteTime supportCutoff)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Statements.Routines (CachesCompatibleWith)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

section Period

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

/-- `VotesCompatibleAt S Sched x s B b₀ b₁ s'`: at a slot `s' ≤ s + k`, every slot-`s'` Goldfish
vote that a lock holder `u ∈ holdersAt S Sched s s'` put on the wire at its tick at the vote time
of `s'` is `u`'s vote for a block it holds that is `B` or a descendant of `B`; and, when the votes
of slot `s' − 1` were not owed inside the period (`VotesOwedInPeriod`), every such vote of a
validator `u ∈ honestActiveAt S Sched s'` is `u`'s vote for a block `H_u` it holds that is `B` or
a descendant of `B`, or that is compatible with `B` while `u`'s justification height before the
vote time is at least `h(B) + 1`.

 The changes:
the second conjunct concludes "on `B`'s chain, or compatible with `B` from a voter justified past
`B`" in place of "on `B`'s chain", and the first conjunct is read only at slots `s' ≤ s + k`.
 Why "compatible" alone does not carry:
honest votes for strict ancestors of `B` can leave the child of `B`'s side without a strict
majority, and a voter whose least viable height lets a block conflicting with `B` be a viable head
steps onto it; the extra fact, that such a vote comes from a voter justified past `B`, is what
excludes that configuration (section 2). The holders' conjunct stops at `s + k` (section 3): up
to the hand-over lock's deadline their anchor is that lock; no consumer reads the conjunct later.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot; `B`: the
  protected block; `b₀`, `b₁`: the start and the end of the period; `s'`: the slot of the votes.

Read aloud: up to the hand-over lock's deadline the holders vote on `B`'s chain; at a slot whose
previous votes arrived in time, every honest active vote is on `B`'s chain, or does not conflict
with `B` and comes from a voter whose finality gadget has justified a block higher than `B`. -/
def VotesCompatibleAt (s : ℕ) (B : Block V) (b₀ b₁ s' : ℕ) : Prop :=
  (s' ≤ s + S.C.k → ∀ u ∈ holdersAt S Sched s s', ∀ vote : GoldfishVote V,
    (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) →
    ∃ H_u ∈ (stateBefore x (voteTime S s') u).S.T,
      vote = GoldfishVote.mk u s' H_u.root ∧ B.AncestorEq H_u) ∧
  (¬ VotesOwedInPeriod S b₀ b₁ s' → ∀ u ∈ honestActiveAt S Sched s', ∀ vote : GoldfishVote V,
    (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) →
    ∃ H_u ∈ (stateBefore x (voteTime S s') u).S.T,
      vote = GoldfishVote.mk u s' H_u.root ∧
      (B.AncestorEq H_u ∨ (H_u.compatible B = true ∧
        (chainStateOf S.C B).h + 1 ≤ (stateBefore x (voteTime S s') u).S.h_j)))

/-- `PeriodInvCompatDueByCutoff S Sched x s B H t₀ b₀ b₁ j`: `PeriodInvOfChainBlockDueByCutoff
S Sched x s B H t₀ b₀ b₁ j` with the sixth clause read through `VotesCompatibleAt` and the seventh
clause concluding compatibility with `B`. The invariant at step `j`, for every step from the
hand-over on. Seven clauses: (1) before the lock's deadline, every lock holder honest through `j`
satisfies `HolderInvAt`; (2) every lock holder honest through `j` records `B` or a descendant of
`B` and holds it; (3) the caches of every validator honest at `j` are compatible with `B`; (4)
every certificate at a height greater than `H` on a held chain, for a block of that chain, is for
a block compatible with `B`; (5) the honest attestations sent before `j` are old, or name an entry
compatible with `B` held by an honest validator by their time; (6) at every slot `s' ≥ s + 1`
whose vote time is before `x[j].time`, `VotesCompatibleAt`; (7) at every slot `s' ≥ s + 1` whose
votes are due by its support cutoff (`VotesDueByCutoff S b₀ b₁ s'`) and whose update time is
before `x[j].time`, every confirmation an honest active validator of `s'` saved for `s'` is
compatible with `B`.

 The changes: clause 6 reads
`VotesCompatibleAt` in place of `VotesExtendAt`, and clause 7 concludes `C'.compatible B = true`
in place of `B.AncestorEq C'`. a block conflicting with `B` still has
only the adversary's support, fewer than half the counted voters, so no honest confirmation
conflicts with `B`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot; `B`: the
  protected block; `H`: the height threshold; `t₀`: the time from which the attestations are new;
  `b₀`, `b₁`: the start and the end of the period; `j`: the step.

Read aloud: from the hand-over on, the lock holders keep `B` locked (or have finalized a strict
descendant of `B`) and recorded while the lock lasts, and recorded for ever; nobody's finality
gadget leaves `B`'s side; up to the hand-over lock's deadline the holders vote on `B`'s chain; at
a slot whose previous votes arrived in time every honest active vote is on `B`'s chain, or does
not conflict with `B` and comes from a voter whose finality gadget has justified a block higher
than `B`; and at every slot `s' ≥ s + 1` whose votes are due by its support cutoff and whose
update is before `x[j].time`, no honest confirmation conflicts with `B`. -/
def PeriodInvCompatDueByCutoff (s : ℕ) (B : Block V) (H t₀ b₀ b₁ j : ℕ) : Prop :=
  (x[j].time < voteTime S (s + S.C.k + 1) →
    ∀ w ∈ updaterAt S Sched s, HonestThrough x j w → HolderInvAt S Sched x s B j w) ∧
  (∀ w ∈ updaterAt S Sched s, HonestThrough x j w →
    B.AncestorEq (x[j][w].st).A.latest_confirmed ∧
    (x[j][w].st).A.latest_confirmed ∈ (x[j][w].st).S.T) ∧
  (∀ u : V, u ∉ Sched.adv (x[j].time : Int) → CachesCompatibleWith S B H (x[j][u].st)) ∧
  CertificatesCompatibleWithAtOfChainBlock S Sched x H B j ∧
  AttestationsCompatibleWithBeforeOfHeldEntry S Sched x B H t₀ j ∧
  (∀ s' : ℕ, s + 1 ≤ s' → voteTime S s' < x[j].time → VotesCompatibleAt S Sched x s B b₀ b₁ s') ∧
  (∀ s' : ℕ, s + 1 ≤ s' → VotesDueByCutoff S b₀ b₁ s' →
    supportCutoff S (s' + 1) < x[j].time →
    ∀ v ∈ honestActiveAt S Sched s', ∀ C' : Block V,
      (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C' →
      C'.compatible B = true)

/-- `VotesExtendAt` gives `VotesCompatibleAt`: the holders' conjunct is the original's, read at
the slots `s' ≤ s + k`, and a vote on `B`'s chain is the first disjunct of the second conjunct.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot; `B`: the
  protected block; `b₀`, `b₁`: the start and the end of the period; `s'`: the slot of the votes.

Read aloud: when the holders, and everybody at a slot whose previous votes arrived in time, vote
on `B`'s chain, the weakened clause holds. -/
theorem votesCompatibleAt_of_votesExtendAt {s : ℕ} {B : Block V} {b₀ b₁ s' : ℕ}
    (h : VotesExtendAt S Sched x s B b₀ b₁ s') : VotesCompatibleAt S Sched x s B b₀ b₁ s' := by
  refine ⟨fun _ => h.1, fun hgood u hu vote hsend => ?_⟩
  obtain ⟨H_u, hT, hv, hB⟩ := h.2 hgood u hu vote hsend
  exact ⟨H_u, hT, hv, Or.inl hB⟩

end Period

end GoldilocksCorrectness.Statements.Executions
