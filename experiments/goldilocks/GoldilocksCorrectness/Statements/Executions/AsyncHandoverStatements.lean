module
public import GoldilocksCorrectness.Proofs.Executions.AsyncHandover

@[expose] public section

/-! Proved in
`GoldilocksCorrectness/Proofs/Executions/AsyncHandover.lean`.

Lemma 99 was to conclude `HandoverFactsOfChainBlock S Sched x s B H (supportCutoff S (s₀ + 1))` from
the healed facts bounded at the hand-over update. Its last clause speaks of the confirmed tips read
at every step up to that update, from step 0 on; the healed facts speak of the steps from
`x[i₁].time` on only, and before the healing phase an honest validator can record a block that the
healed chain abandons (finding F1 of the brief, a hand argument). The two statements here are what
closes:

- `handoverFacts_six_of_healed_upTo`: the first six clauses of the hand-over facts;
- `confirmed_tips_preceq_handover_upTo`: the last clause for the confirmed tips read at steps at a
  time from `x[i₁].time` to the hand-over update.

Write `c` for `supportCutoff S (s + 1)`, the time of the hand-over update.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff
  proposalWindowStart)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Statements.Routines (confirmedOf)

open GoldilocksCorrectness.Statements.Routines (CachesCompatibleWith)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 99, the first six clauses of the hand-over facts.** In an execution where every time is
reached and corruption is permanent; blocks and Goldfish votes are delivered within `Δ` after `GST`
for every send whose deadline is at most the support cutoff of slot `s` (synchrony from the
receiver's wake and catch-up on wake, up to that bound); roots name blocks among what honest
validators hold by the hand-over update `c`; a block reaches a validator only once it holds the
parent; nobody votes or signs in an honest validator's name; fewer than a quorum of validators are
ever in the adversary set; committee sleepiness holds from `anchor`, at or before `x[i₁].time`;
`GST` is at most the vote time of the healed slot `s₀`, whose update is at or before `x[i₁].time`;
the updaters' confirmations of the slots from `s₀` to before `s − 1` form one chain; the chain
invariant and the lock invariant hold at every slot after `s₀` and at most `s`, and the lock
invariant at `s₀` itself; every honest attestation sent before the update of `s₀` has height at
most `H`; the caches of every validator honest at a step at a time from `x[i₁].time` to `c` are on
the honest chain with justification height greater than `H`; every honest active voter of slot
`s + 1` has its fork-choice root compatible with the honest chain before `s + 1`, and a viable head
on it when its root is an ancestor (`VoterFrameOnChainAt`); the slot `s` starts after `x[i₁].time`,
its proposer is awake and honest from the start of its proposal window to `c`, its tick at the
start of `s` put `B` on the wire, and no block it held then has `B`'s root. Then:

1. `H` is less than `B`'s chain-state height;
2. every updater of slot `s` has, right after `c`, saved `B` as its confirmation of slot `s`,
   records `B`, and satisfies `HolderInvAt` at the step `stepBefore x (c + 1)`: it holds the lock
   entry on `B` with the deadline of a slot-`s` lock, records `B` and holds it, and has every fast
   block and every live lock entry compatible with `B`;
3. every validator honest at `c` has its caches right after `c` compatible with `B`
   (`CachesCompatibleWith`);
4. at the step `stepBefore x (c + 1)`, every progress certificate at a height greater than `H` on
   a held chain, for a block of that chain, is for a block compatible with `B`;
5. every honest attestation sent before that step has height at most `H` when sent before the
   update of `s₀`, and otherwise names an entry compatible with `B`, at its height and by its root,
   that an honest validator held by the attestation's time;
6. for every period `[b₀, b₁)`, every honest active validator of slot `s + 1` voted, at the vote
   time of `s + 1`, for a block it held that is `B` or a descendant of `B`.

Why: `honest_proposal_saved_until_upTo` at `q := s − 2` (every block of the honest chain before `s`
is an ancestor of `B`; every updater saves `B`; `HonestChainExtends` for `B` at slot `s`; the
updaters' revocation of slot `s + 1` keeps no live lock off `B`'s chain), so a block on the honest
chain at a slot at most `s` is an ancestor of `B`. (1) an updater of `s` exists by committee
sleepiness; its justified block at the hand-over step is on the chain at a slot at most `s`
(`justified_onHonestChainAt_of_caches`), so an ancestor of `B`. (2) the inclusion twin
`lem90_included_update_facts_until_upTo`; the fast blocks are ancestors of the saved `B`; a lock
entry live at `stepBefore x (c + 1)` was live before the tick at `c` (its block was held then, the
finalized block only grows). (3) as (1). (5) Lemma 82 (b) puts the entry on the honest chain at the
attestation's slot, at most `s`. (4) Lemma 102 at a step from (5). (6) Lemma 26b's twin at slot `s`,
with the honest active committee members of `s` and the voter condition at `B`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold; `s`: the hand-over slot;
  `B`: its proposal.

Read aloud: after the healed phase, with the network synchronous through the hand-over slot's votes
and the slot-`(s + 1)` voters' fork choice following the honest chain, right after the hand-over
update every updater of slot `s` holds the lock on `B` and records `B`; no honest validator's
caches, certificates or attestations conflict with `B`; and every honest active vote of slot
`s + 1` is on `B`'s chain.

 Against the probe's Lemma 99 (`scratch/goldilocks_async/probe_lanes_1.lean:910`):
the roots bounded at `c`, no `hTicks`, the delivery premises bounded at `supportCutoff S s` (the
measured bound), the chain before `s − 1` (the one read), and the conclusion's last clause left out
(finding F1). -/
theorem handoverFacts_six_of_healed_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H s : ℕ) (B : Block V)
    -- every time is reached; corruption is permanent
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    -- blocks and Goldfish votes are delivered within `Δ` after `GST`, up to the support cutoff of
    -- slot `s`
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    -- roots name blocks among what honest validators hold by the hand-over update
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    -- a block reaches a validator only once it holds the parent; nobody votes or signs in an
    -- honest validator's name
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    -- fewer than a quorum have been corrupted up to any time
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    -- committee sleepiness from `anchor`, at or before `x[i₁].time`
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    -- the healed slot: `GST` at most its vote time, its update at or before `x[i₁].time`
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    -- the updaters' confirmations of the slots from `s₀` to before `s − 1` form one chain
    (hChain : ConfirmationsChainBefore S Sched x s₀ (s - 1))
    -- the chain invariant and the lock invariant at the slots after `s₀` and at most `s`
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor S Sched x (honestActiveAt S Sched s') (OnHonestChainBefore S Sched x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ u ∈ honestActiveAt S Sched s',
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s') s' u)
    -- the lock invariant at the healed slot
    (hLocks₀ : ∀ u ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ u)
    -- the honest attestations sent before the healed slot's update have height at most `H`
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    -- the caches from `x[i₁].time` to the hand-over update are on the honest chain
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ supportCutoff S (s + 1) →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    -- the voter condition at slot `s + 1`
    (hFrames : ∀ w ∈ honestActiveAt S Sched (s + 1), VoterFrameOnChainAt S Sched x s₀ (s + 1) w)
    -- the hand-over slot starts after `x[i₁].time`
    (hs : x[i₁].time < slotStart S s)
    -- its proposer is awake and honest from its proposal window to the hand-over update
    (hp : ∀ t : ℕ, proposalWindowStart S s ≤ t → t ≤ supportCutoff S (s + 1) →
      S.P.proposer s ∈ Sched.awake (t : Int) ∧ S.P.proposer s ∉ Sched.adv (t : Int))
    -- its tick at the start of slot `s` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    -- no block the proposer held then has `B`'s root
    (hNoCollision : ¬ RootCollisionAtProposal S Sched x s B) :
    H < (chainStateOf S.C B).h ∧
    (∀ w ∈ updaterAt S Sched s,
      (stateBefore x (supportCutoff S (s + 1) + 1) w).A.saved_confirmation s = some B ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) w).A.latest_confirmed = B ∧
      HolderInvAt S Sched x s B (stepBefore x (supportCutoff S (s + 1) + 1)) w) ∧
    (∀ u : V, u ∉ Sched.adv ((supportCutoff S (s + 1) : ℕ) : Int) →
      CachesCompatibleWith S B H (stateBefore x (supportCutoff S (s + 1) + 1) u)) ∧
    CertificatesCompatibleWithAtOfChainBlock S Sched x H B
      (stepBefore x (supportCutoff S (s + 1) + 1)) ∧
    AttestationsCompatibleWithBeforeOfHeldEntry S Sched x B H (supportCutoff S (s₀ + 1))
      (stepBefore x (supportCutoff S (s + 1) + 1)) ∧
    (∀ b₀ b₁ : ℕ, VotesExtendAt S Sched x s B b₀ b₁ (s + 1)) :=
  by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    GoldilocksCorrectness.Proofs.Executions.handoverFacts_six_of_healed_upTo S Sched x GST s₀ anchor
      i₁ H s B hDiv hMono hSync hCatch hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST ht₀ hChain
      hInv hLocks hLocks₀ hOld hCaches hFrames hs hp hPropose hNoCollision
  -- clause 3 at the step before the time after the cutoff, whose time is the cutoff
  have ht := GoldilocksCorrectness.Proofs.Executions.time_stepBefore_add_one x hDiv
    (show 1 ≤ supportCutoff S (s + 1) + 1 by omega)
  have ht' : x[stepBefore x (supportCutoff S (s + 1) + 1)].time = supportCutoff S (s + 1) := by
    omega
  exact ⟨h1, h2, fun u hu => h3 _ u ht' (by rw [ht']; exact hu), h4, h5, h6⟩

/-- **Lemma 99, the confirmed tips read from `x[i₁].time` to the hand-over update.** Under the
hypotheses of `handoverFacts_six_of_healed_upTo` without the voter condition at slot `s + 1`, and
with every validator honest at a step at a time from `x[i₁].time` to the hand-over update `c`
holding as its record a block on the honest chain at a slot whose update ran by then: every block
that is, at a step `T` at a time from `x[i₁].time` to `c`, the confirmed tip of a validator `v`
honest through `T`, or an ancestor of it, is `B` or an ancestor of `B`.

Why: the confirmed tip is on the honest chain at a slot whose update ran by `x[T].time`
(`confirmedOf_onHonestChainAt`), so at a slot at most `s`; a block on the honest chain at a slot at
most `s` is `B` or an ancestor of `B` (`honest_proposal_saved_until_upTo`, and every updater of `s`
saved `B`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold; `s`: the hand-over slot;
  `B`: its proposal.

Read aloud: what any honest validator had confirmed from `x[i₁].time` to the hand-over update is an
ancestor of the hand-over proposal.

 The last clause of
`HandoverFactsOfChainBlock` reads every step up to `c`, from step 0 on; this statement reads the
steps from `x[i₁].time` on, the ones the healed facts speak of (finding F1). -/
theorem confirmed_tips_preceq_handover_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H s : ℕ) (B : Block V)
    -- every time is reached; corruption is permanent
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    -- blocks and Goldfish votes are delivered within `Δ` after `GST`, up to the support cutoff of
    -- slot `s`
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    -- roots name blocks among what honest validators hold by the hand-over update
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    -- a block reaches a validator only once it holds the parent; nobody votes or signs in an
    -- honest validator's name
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    -- fewer than a quorum have been corrupted up to any time
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    -- committee sleepiness from `anchor`, at or before `x[i₁].time`
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    -- the healed slot: `GST` at most its vote time, its update at or before `x[i₁].time`
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    -- the updaters' confirmations of the slots from `s₀` to before `s − 1` form one chain
    (hChain : ConfirmationsChainBefore S Sched x s₀ (s - 1))
    -- the chain invariant and the lock invariant at the slots after `s₀` and at most `s`
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor S Sched x (honestActiveAt S Sched s') (OnHonestChainBefore S Sched x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ u ∈ honestActiveAt S Sched s',
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s') s' u)
    -- the lock invariant at the healed slot
    (hLocks₀ : ∀ u ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ u)
    -- the honest attestations sent before the healed slot's update have height at most `H`
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    -- the caches from `x[i₁].time` to the hand-over update are on the honest chain
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ supportCutoff S (s + 1) →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    -- the records from `x[i₁].time` to the hand-over update are on the honest chain at a slot
    -- whose update ran by then, and held
    (hLatest : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ supportCutoff S (s + 1) →
      u ∉ Sched.adv (x[j].time : Int) → (∃ σ : ℕ, supportCutoff S (σ + 1) ≤ x[j].time ∧
        OnHonestChainAt S Sched x s₀ σ (x[j][u].st).A.latest_confirmed) ∧
        (x[j][u].st).A.latest_confirmed ∈ (x[j][u].st).S.T)
    -- the hand-over slot starts after `x[i₁].time`
    (hs : x[i₁].time < slotStart S s)
    -- its proposer is awake and honest from its proposal window to the hand-over update
    (hp : ∀ t : ℕ, proposalWindowStart S s ≤ t → t ≤ supportCutoff S (s + 1) →
      S.P.proposer s ∈ Sched.awake (t : Int) ∧ S.P.proposer s ∉ Sched.adv (t : Int))
    -- its tick at the start of slot `s` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    -- no block the proposer held then has `B`'s root
    (hNoCollision : ¬ RootCollisionAtProposal S Sched x s B) :
    ∀ (v : V) (T : ℕ) (P : Block V), HonestThrough x T v → x[i₁].time ≤ x[T].time →
      x[T].time ≤ supportCutoff S (s + 1) →
      P.AncestorEq (confirmedOf (x[T][v].st)) → P.AncestorEq B :=
  GoldilocksCorrectness.Proofs.Executions.confirmed_tips_preceq_handover_upTo S Sched x GST s₀
    anchor i₁ H s B hDiv hMono hSync hCatch hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST
    ht₀ hChain hInv hLocks hLocks₀ hOld hCaches hLatest hs hp hPropose hNoCollision

end GoldilocksCorrectness.Statements.Executions
