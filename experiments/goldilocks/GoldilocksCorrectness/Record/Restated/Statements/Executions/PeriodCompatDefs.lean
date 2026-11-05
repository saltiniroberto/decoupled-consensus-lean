module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.PeriodInductionDefs
public import GoldilocksCorrectness.Statements.Executions.PeriodCompatDefs

@[expose] public section

/-!
# PeriodCompatDefs, over a model

The definitions of `GoldilocksCorrectness/Statements/Executions/PeriodCompatDefs.lean` over a model
`M`, for an execution `x` of `protocolOf M S`: the votes compatible with the protected block, and
the invariant the period carries with the votes due by the support cutoff.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (voteTime supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Record.Statements.Routines (IsEntry CachesCompatibleWith)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)

section Period

variable (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)

/-- `VotesCompatibleAt M S Sched x s B Δs b₀ b₁ s'`: at a slot `s' ≤ s + k`, every slot-`s'` Goldfish
vote that a lock holder `u ∈ holdersAt M S Sched s s'` put on the wire at its tick at the vote time
of `s'` is `u`'s vote for a block it holds that is `B` or a descendant of `B`; and, when the votes
of slot `s' − 1` were not owed inside the period (`VotesOwedInPeriod`), every such vote of a
validator `u ∈ honestActiveAt M S Sched s'` is `u`'s vote for a block `H_u` it holds that is `B` or
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
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot; `B`: the
  protected block; `Δs`: the sync delay; `b₀`, `b₁`: the start and the end of the period; `s'`:
  the slot of the votes.

Read aloud: up to the hand-over lock's deadline the holders vote on `B`'s chain; at a slot whose
previous votes arrived in time, every honest active vote is on `B`'s chain, or does not conflict
with `B` and comes from a voter whose finality gadget has justified a block higher than `B`. -/
def VotesCompatibleAt (s : ℕ) (B : Block V) (Δs b₀ b₁ s' : ℕ) : Prop :=
  (s' ≤ s + S.C.k → ∀ u ∈ holdersAt M S A x s s', ∀ vote : GoldfishVote V,
    (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
    ∃ H_u ∈ (x.tickInput u (M.voteTime S.C s')).tree,
      vote = GoldfishVote.mk u s' H_u.root ∧ B.AncestorEq H_u) ∧
  (¬ VotesOwedInPeriod M S Δs b₀ b₁ s' → ∀ u ∈ honestActiveAt M S A x s', ∀ vote : GoldfishVote V,
    (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
    ∃ H_u ∈ (x.tickInput u (M.voteTime S.C s')).tree,
      vote = GoldfishVote.mk u s' H_u.root ∧
      (B.AncestorEq H_u ∨ (H_u.compatible B = true ∧
        (M.chainStateOf S.C B).h + 1 ≤ (x.tickInput u (M.voteTime S.C s')).justifiedHeight)))

/-- `PeriodInvCompatDueByCutoff M S Sched x s B H t₀ Δs b₀ b₁ j`: `PeriodInvOfChainBlockDueByCutoff
S Sched x s B H t₀ b₀ b₁ j` with the sixth clause read through `VotesCompatibleAt` and the seventh
clause concluding compatibility with `B`. The invariant at step `j`, for every step from the
hand-over on. Seven clauses: (1) every lock holder honest through `j` that has not ticked, before
`j`, to the hand-over lock's deadline, and every slot to whose vote time it has ticked before `j`
has its support cutoff at or before `x[j].time`, satisfies `HolderInvAt`; (2) every lock holder honest through `j` records `B` or a descendant of
`B` and holds it; (3) the caches of every validator honest at `j` are compatible with `B`; (4)
every certificate at a height greater than `H` on a held chain, for a block of that chain, is for
a block compatible with `B`; (5) the honest attestations sent before `j` are old, or name an entry
compatible with `B` held by an honest validator by their time; (6) at every slot `s' ≥ s + 1`
whose support cutoff is at or before `x[j].time`, `VotesCompatibleAt`; (7) at every slot `s' ≥ s + 1` whose
votes are due by its support cutoff (`VotesDueByCutoff M S Δs b₀ b₁ s'`), every confirmation an honest
active validator of `s'` that ticked to the support cutoff of `s' + 1` before `j` saved for `s'` is
compatible with `B`.

Clause 1 is keyed on the support cutoff, as clause 6 is: it holds for a holder at step `j` when the holder
has not ticked, before `j`, to the hand-over lock's deadline, and every slot to whose vote time it
has ticked before `j` has its support cutoff at or before `x[j].time`. A lock holder's revocation at the vote time of a
slot `s'` counts the committee of `s' − 1`, whose sleepiness condition is keyed on the support
cutoff of `s'`; so what clause 1 says at `x[j].time` is decided by the activity up to `x[j].time`.
At the steps from a vote time to before its support cutoff no confirmation update runs, and
clause 2 holds there without clause 1.

 The changes: clause 6 reads
`VotesCompatibleAt` in place of `VotesExtendAt`, and clause 7 concludes `C'.compatible B = true`
in place of `B.AncestorEq C'`. a block conflicting with `B` still has
only the adversary's support, fewer than half the counted voters, so no honest confirmation
conflicts with `B`.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot; `B`: the
  protected block; `H`: the height threshold; `t₀`: the time from which the attestations are new;
  `Δs`: the sync delay; `b₀`, `b₁`: the start and the end of the period; `j`: the step.

Read aloud: from the hand-over on, the lock holders keep `B` locked (or have finalized a strict
descendant of `B`) and recorded while the lock lasts on their own clocks, at every step at which
every slot to whose vote time they have ticked has reached its support cutoff, and recorded for ever; nobody's finality
gadget leaves `B`'s side; up to the hand-over lock's deadline the holders vote on `B`'s chain; at
a slot whose previous votes arrived in time every honest active vote is on `B`'s chain, or does
not conflict with `B` and comes from a voter whose finality gadget has justified a block higher
than `B`; and at every slot `s' ≥ s + 1` whose votes are due by its support cutoff, no confirmation
saved for `s'` by an honest active validator of `s'` that has run its update before `j` conflicts with `B`. -/
def PeriodInvCompatDueByCutoff (s : ℕ) (B : Block V) (H t₀ Δs b₀ b₁ j : ℕ) : Prop :=
  (∀ w ∈ updaterAt M S A x s, x.HonestThrough A j w →
    (∀ (k c : ℕ), k < j → x.lbl k = Event.tick w c → c < M.voteTime S.C (s + S.C.k + 1)) →
    (∀ (k s' : ℕ), k < j → x.lbl k = Event.tick w (M.voteTime S.C s') → M.supportCutoff S.C s' ≤ x.time j) →
    HolderInvAt M S x s B j w) ∧
  (∀ w ∈ updaterAt M S A x s, x.HonestThrough A j w →
    B.AncestorEq (x.st j w).latestConfirmed ∧
    (x.st j w).latestConfirmed ∈ (x.st j w).tree) ∧
  (∀ u : V, u ∉ A.corrupted j → CachesCompatibleWith M S B H (x.st j u)) ∧
  CertificatesCompatibleWithAtOfChainBlock M A x H B j ∧
  AttestationsCompatibleWithBeforeOfHeldEntry M S A x B H t₀ j ∧
  (∀ s' : ℕ, s + 1 ≤ s' → M.supportCutoff S.C s' ≤ x.time j →
      VotesCompatibleAt M S A x s B Δs b₀ b₁ s') ∧
  (∀ s' : ℕ, s + 1 ≤ s' → VotesDueByCutoff M S Δs b₀ b₁ s' →
    ∀ v ∈ honestActiveAt M S A x s', x.tickStep v (M.supportCutoff S.C (s' + 1)) < j → ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' →
      C'.compatible B = true)

/-- `VotesExtendAt` gives `VotesCompatibleAt`: the holders' conjunct is the original's, read at
the slots `s' ≤ s + k`, and a vote on `B`'s chain is the first disjunct of the second conjunct.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot; `B`: the
  protected block; `Δs`: the sync delay; `b₀`, `b₁`: the start and the end of the period; `s'`:
  the slot of the votes.

Read aloud: when the holders, and everybody at a slot whose previous votes arrived in time, vote
on `B`'s chain, the weakened clause holds. -/
theorem votesCompatibleAt_of_votesExtendAt {s : ℕ} {B : Block V} {b₀ b₁ s' Δs : ℕ}
    (h : VotesExtendAt M S A x s B Δs b₀ b₁ s') : VotesCompatibleAt M S A x s B Δs b₀ b₁ s' := by
  refine ⟨fun _ => h.1, fun hgood u hu vote hsend => ?_⟩
  obtain ⟨H_u, hT, hv, hB⟩ := h.2 hgood u hu vote hsend
  exact ⟨H_u, hT, hv, Or.inl hB⟩

end Period

end GoldilocksCorrectness.Record.Statements.Executions

