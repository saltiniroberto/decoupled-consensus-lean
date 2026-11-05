module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncHandover
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# AsyncHandoverStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/AsyncHandoverStatements.lean`, over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 99 without the
confirmed tips read before the healing phase, namely the first six clauses of the hand-over facts
from the healed facts bounded at the hand-over update, and the last clause for the confirmed tips
read from the healing phase's start on; each is the theorem of the same name of
`Record/Restated/Proofs/Executions/AsyncHandover.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff
  proposalWindowStart)

open GoldilocksCorrectness.Statements.Routines (confirmedOf)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (CachesCompatibleWith)
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject)

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
2. every updater `w` of slot `s` has, in the state its own tick to `c` leaves (`x.tickOutput w c`, the
   configuration `x.tickStep w c + 1`), saved `B` as its confirmation of slot `s`, records `B`, and
   satisfies `HolderInvAt` there: it holds the lock entry on `B` with the deadline of a slot-`s` lock,
   records `B` and holds it, and has every fast block and every lock entry live at a clock value no
   earlier than `c` compatible with `B`;
3. at every configuration whose time is `c`, every validator outside the adversary set there has its
   caches compatible with `B` (`CachesCompatibleWith`);
4. at every configuration whose time is `c`, every progress certificate at a height greater than `H`
   on a held chain, for a block of that chain, is for a block compatible with `B`;
5. at every configuration whose time is `c`, every honest attestation sent before it has height at
   most `H` when sent before the update of `s₀`, and otherwise names an entry compatible with `B`, at
   its height and by its root, that an honest validator held by the attestation's time;
6. for every period `[b₀, b₁)`, every honest active validator of slot `s + 1` voted, at the vote
   time of `s + 1`, for a block it held that is `B` or a descendant of `B`.

Why: `honest_proposal_saved_until_upTo` at `q := s − 2` (every block of the honest chain before `s`
is an ancestor of `B`; every updater saves `B`; `HonestChainExtends` for `B` at slot `s`; the
updaters' revocation of slot `s + 1` keeps no live lock off `B`'s chain), so a block on the honest
chain at a slot at most `s` is an ancestor of `B`. (1) an updater of `s` exists by committee
sleepiness; its justified block at a configuration whose time is `c` is on the chain at a slot at
most `s` (`justified_onHonestChainAt_of_caches`), so an ancestor of `B`. (2) the inclusion twin
`lem90_included_update_facts_until_upTo`, carried from the state before `c + 1` to the tick output (no
step of the updater in between is a tick, so its confirmation state is kept,
`keepsConfirmation_of_no_tick_between`); the fast blocks are ancestors of the saved `B`; a
lock entry live at a clock value `t ≥ c` at the tick output is live at `c` (`is_live_of_le`) and was
live before the tick at `c` (its block was held then, the finalized block only grows). (3) as (1). (5) Lemma 82 (b) puts the entry on the honest chain at the
attestation's slot, at most `s`. (4) Lemma 102 at a step from (5). (6) Lemma 26b's twin at slot `s`,
with the honest active committee members of `s` and the voter condition at `B`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold; `s`: the hand-over slot;
  `B`: its proposal.

Read aloud: after the healed phase, with the network synchronous through the hand-over slot's votes,
the slot-`(s + 1)` voters' fork choice following the honest chain, and the voters of slots `s - 1` and `s` and
the proposer of `s` active for the sync delay after the times the synchronous delivery reads them, right after the hand-over
update every updater of slot `s` holds the lock on `B` and records `B`; no honest validator's
caches, certificates or attestations conflict with `B`; and every honest active vote of slot
`s + 1` is on `B`'s chain.

 At both clock bounds 0 the first four follow from `hRoots`, `hAdvQ`, `hCaches` and the first part of `hs`.

 Against the probe's Lemma 99
(`scratch/goldilocks_async/probe_lanes_1.lean:910`): the roots bounded at `c`, no `hTicks`, the
delivery premises bounded at `M.supportCutoff S.C s` (the measured bound), the chain before `s − 1`
(the one read), and the conclusion's last clause left out (finding F1). clauses 3 to 5, about the configuration as a whole, at every configuration whose time is `c`
(over real time the configuration before the clock value `c + 1` is at any time in `[c, c + 1)`, after
steps the hypotheses do not bound).   -/
theorem handoverFacts_six_of_healed_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H s : ℕ) (B : Block V)
    -- every time is reached; corruption is permanent
    -- blocks and Goldfish votes are delivered within `Δ` after `GST`, up to the support cutoff of
    -- slot `s`
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- the end of the window clauses 3 to 5 conclude in: at most one behind-bound after the hand-over update
    -- (; at `tW := cut(s + 1) + ΔClockBehind` the window of)
    (tW : ℝ) (htW : tW ≤ (M.supportCutoff S.C (s + 1) : ℝ) + ΔClockBehind)
    -- roots name blocks among what honest validators hold by the hand-over update
    (hRoots : RootsNameBlocksUntil M A x tW)
    -- a block reaches a validator only once it holds the parent; nobody votes or signs in an
    -- honest validator's name
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum of validators have been in the adversary set up to `M.supportCutoff S.C (s + 1)`
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) tW)
    -- committee sleepiness from `anchor` for the slots whose update is at most `M.supportCutoff S.C (s + 1)`, at or before `x[i₁].time`
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s + 1))) (hAnchor : anchor ≤ x.time i₁)
    -- the healed slot: `GST` at most its vote time, its update at or before `x[i₁].time`
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    -- the updaters' confirmations of the slots from `s₀` to before `s − 1` form one chain
    (hChain : ConfirmationsChainBefore M S A x s₀ (s - 1))
    -- the chain invariant and the lock invariant at the slots after `s₀` and at most `s`
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor M S A x (honestActiveAt M S A x s')
        (OnHonestChainBefore M S A x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s',
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' u)
    -- the lock invariant at the healed slot
    (hLocks₀ : ∀ u ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ u)
    -- the honest attestations sent before the healed slot's update have height at most `H`
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the caches from `x[i₁].time` to the hand-over update are on the honest chain
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ tW →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    -- roots name blocks, fewer than a quorum in the adversary set, and the caches on the honest chain, up to the
    -- real time of each updater's tick to the hand-over update
    (hRootsU : ∀ v ∈ updaterAt M S A x s, RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hAdvQU : ∀ v ∈ updaterAt M S A x s, A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hCachesU : ∀ v ∈ updaterAt M S A x s, ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j →
      x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    -- the voter condition at slot `s + 1`
    (hFrames : ∀ w ∈ honestActiveAt M S A x (s + 1), VoterFrameOnChainAt M S A x s₀ (s + 1) w)
    -- the hand-over slot starts after `x[i₁].time`, and its proposer's tick to its start is at or after `x[i₁].time`
    --
    (hs : x.time i₁ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s) (M.slotStart S.C s) → x.time i₁ < x.time k)
    -- the honest voters of slots `s - 1` and `s` are active through the sync delay after Lemma 12's read time of
    -- their slot ( under)
    (hHold : ∀ s' : ℕ, s - 1 ≤ s' → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- its proposer ticks to the hand-over update, awake and honest since the trace's start or since a tick,
    -- after its last restart, to a clock value at most its proposal window's start; honest at that update
    (hp : S.P.proposer s ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C s)
        (M.supportCutoff S.C (s + 1)) ∧
      S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)))
    -- its proposer is active through the sync delay after `M.slotStart S.C s - max (Δ S) Δs` (, the amended
    -- row `hHoldP`,)
    (hHoldP : S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- its tick at the start of slot `s` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    -- no block the proposer held then has `B`'s root
    (hNoCollision : ¬ RootCollisionAtProposal M S A x s B) :
    H < (M.chainStateOf S.C B).h ∧
    (∀ w ∈ updaterAt M S A x s,
      (x.tickOutput w (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B ∧
      (x.tickOutput w (M.supportCutoff S.C (s + 1))).latestConfirmed = B ∧
      HolderInvAt M S x s B (x.tickStep w (M.supportCutoff S.C (s + 1)) + 1) w) ∧
    (∀ (j : ℕ) (u : V), (M.supportCutoff S.C (s + 1) : ℝ) ≤ x.time j → x.time j ≤ tW → u ∉ A.corrupted j →
      CachesCompatibleWith M S B H (x.st j u)) ∧
    (∀ j : ℕ, (M.supportCutoff S.C (s + 1) : ℝ) ≤ x.time j → x.time j ≤ tW → CertificatesCompatibleWithAtOfChainBlock M A x H B j) ∧
    (∀ j : ℕ, (M.supportCutoff S.C (s + 1) : ℝ) ≤ x.time j → x.time j ≤ tW →
      AttestationsCompatibleWithBeforeOfHeldEntry M S A x B H (M.supportCutoff S.C (s₀ + 1)) j) ∧
    (∀ Δs b₀ b₁ : ℕ, VotesExtendAt M S A x s B Δs b₀ b₁ (s + 1)) := by
  exact (GoldilocksCorrectness.Record.Proofs.Executions.handoverFacts_six_of_healed_upTo M F) U Fx S A x R GST s₀
    anchor i₁ H s B E hNet hSkew hRedeliver Sy hΔs tW htW hRoots hParent hAdvQ hSleepK hAnchor hGST ht₀ hChain hInv hLocks hLocks₀ hOld
    hCaches hRootsU hAdvQU hCachesU hFrames hs hHold hp hHoldP hPropose hNoCollision

/-- **Lemma 99, the confirmed tips read from `x[i₁].time` to the hand-over update.** Under the
hypotheses of `handoverFacts_six_of_healed_upTo` without the voter condition at slot `s + 1`, and
with every validator honest at a step at a time from `x[i₁].time` to the hand-over update `c`
holding as its record a block on the honest chain at a slot whose update it ran at its own tick at
an earlier step: every block
that is, at a step `T` at a time from `x[i₁].time` to `c`, the confirmed tip of a validator `v`
outside the adversary set at every time up to the time of `T`, or an ancestor of it, is `B` or an ancestor of `B`.

Why: the confirmed tip is on the honest chain at a slot whose cutoff some validator ticked to at a
step before `T` (`hLatest`, or the finalized branch), so at a slot at most `s` (that tick is at a
time at least the cutoff less `ΔClockAhead`, and `hSkew`); a block on the honest chain at a slot at
most `s` is `B` or an ancestor of `B` (`honest_proposal_saved_until_upTo`, and every updater of `s`
saved `B`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold; `s`: the hand-over slot;
  `B`: its proposal.

Read aloud: with the voters of slots `s - 1` and `s` and the proposer of `s` active for the sync delay after
the times the synchronous delivery reads them, what any honest validator had confirmed from `x[i₁].time` to the
hand-over update is an ancestor of the hand-over proposal.

 At both clock bounds 0 the first four follow from `hRoots`, `hAdvQ`, `hCaches` and the first part of `hs`.

 The last clause of
`HandoverFactsOfChainBlock` reads every step up to `c`, from step 0 on; this statement reads the
steps from `x[i₁].time` on, the ones the healed facts speak of (finding F1). -/
theorem confirmed_tips_preceq_handover_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H s : ℕ) (B : Block V)
    -- every time is reached; corruption is permanent
    -- blocks and Goldfish votes are delivered within `Δ` after `GST`, up to the support cutoff of
    -- slot `s`
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks among what honest validators hold by the hand-over update
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)))
    -- a block reaches a validator only once it holds the parent; nobody votes or signs in an
    -- honest validator's name
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum of validators have been in the adversary set up to `M.supportCutoff S.C (s + 1)`
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (M.supportCutoff S.C (s + 1)))
    -- committee sleepiness from `anchor` for the slots whose update is at most `M.supportCutoff S.C (s + 1)`, at or before `x[i₁].time`
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s + 1))) (hAnchor : anchor ≤ x.time i₁)
    -- the healed slot: `GST` at most its vote time, its update at or before `x[i₁].time`
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    -- the updaters' confirmations of the slots from `s₀` to before `s − 1` form one chain
    (hChain : ConfirmationsChainBefore M S A x s₀ (s - 1))
    -- the chain invariant and the lock invariant at the slots after `s₀` and at most `s`
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor M S A x (honestActiveAt M S A x s')
        (OnHonestChainBefore M S A x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s',
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' u)
    -- the lock invariant at the healed slot
    (hLocks₀ : ∀ u ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ u)
    -- the honest attestations sent before the healed slot's update have height at most `H`
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the caches from `x[i₁].time` to the hand-over update are on the honest chain
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ M.supportCutoff S.C (s + 1) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    -- roots name blocks, fewer than a quorum in the adversary set, and the caches on the honest chain, up to the
    -- real time of each updater's tick to the hand-over update
    (hRootsU : ∀ v ∈ updaterAt M S A x s, RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hAdvQU : ∀ v ∈ updaterAt M S A x s, A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hCachesU : ∀ v ∈ updaterAt M S A x s, ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j →
      x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    -- the records from `x[i₁].time` to the hand-over update are on the honest chain at a slot
    -- whose update the validator itself ran, at its own tick at a step before, and held
    (hLatest : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ M.supportCutoff S.C (s + 1) →
      u ∉ A.corrupted j → (∃ σ : ℕ,
        x.lbl (x.tickStep u (M.supportCutoff S.C (σ + 1))) = Event.tick u (M.supportCutoff S.C (σ + 1)) ∧
        x.tickStep u (M.supportCutoff S.C (σ + 1)) < j ∧
        OnHonestChainAt M S A x s₀ σ (x.st j u).latestConfirmed) ∧
        (x.st j u).latestConfirmed ∈ (x.st j u).tree)
    -- the hand-over slot starts after `x[i₁].time`, and its proposer's tick to its start is at or after `x[i₁].time`
    --
    (hs : x.time i₁ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s) (M.slotStart S.C s) → x.time i₁ < x.time k)
    -- the honest voters of slots `s - 1` and `s` are active through the sync delay after Lemma 12's read time of
    -- their slot ( under)
    (hHold : ∀ s' : ℕ, s - 1 ≤ s' → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- its proposer ticks to the hand-over update, awake and honest since the trace's start or since a tick,
    -- after its last restart, to a clock value at most its proposal window's start; honest at that update
    (hp : S.P.proposer s ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C s)
        (M.supportCutoff S.C (s + 1)) ∧
      S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)))
    -- its proposer is active through the sync delay after `M.slotStart S.C s - max (Δ S) Δs` (, the amended
    -- row `hHoldP`,)
    (hHoldP : S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- its tick at the start of slot `s` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    -- no block the proposer held then has `B`'s root
    (hNoCollision : ¬ RootCollisionAtProposal M S A x s B) :
    ∀ (v : V) (T : ℕ) (P : Block V), A.HonestThroughTime x (x.time T) v → x.time i₁ ≤ x.time T →
      x.time T ≤ M.supportCutoff S.C (s + 1) →
      P.AncestorEq (M.ac_confirmed (x.st T v)) → P.AncestorEq B :=
  (GoldilocksCorrectness.Record.Proofs.Executions.confirmed_tips_preceq_handover_upTo M F) U Fx S A x R GST s₀
    anchor i₁ H s B E hNet hSkew hRedeliver Sy hΔs hRoots hParent hAdvQ hSleepK hAnchor hGST ht₀ hChain hInv hLocks hLocks₀ hOld
    hCaches hRootsU hAdvQU hCachesU hLatest hs hHold hp hHoldP hPropose hNoCollision

end GoldilocksCorrectness.Record.Statements.Executions

