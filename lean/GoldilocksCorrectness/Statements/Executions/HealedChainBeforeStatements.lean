module
public import GoldilocksCorrectness.Proofs.Executions.HealedChainBefore

@[expose] public section

/-!
# The chain before a slot, the caches from the hand-over, the updater frame

The audited statements, proved in `GoldilocksCorrectness/Proofs/Executions/HealedChainBefore.lean`:

- four monotonicity facts in the time: `adversaryFewerThanThirdUntil_mono`,
  `confirmedAgree_mono`, `confirmedMonotone_mono`, `confirmedIncluded_mono`;
- `lem81_chain_before`, Lemma 81 with the frames only at the slots `s` with `s₀ < s < n`: the
  updaters' confirmations of the slots from `s₀` to before `n` form one chain;
- `caches_after_handover`: from the first step one time unit after the hand-over to the steps at
  a time `t`, every honest validator's caches are on the honest chain (Lemmas 82 and 84);
- `updaterFrame_after_handover`: after the hand-over, every updater of slot `s` has the frame
  `UpdaterFinalizedOnChainAt` relative to the honest chain before `s` (Lemmas 46 and 91 (f)).


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## The monotonicity facts in the time -/

omit [DecidableEq V] [RootOrder] in
/-- **Fewer than a third in the adversary set is monotone in the time.** Fewer than a third of the
validators in the adversary set at some time up to `t` implies the same up to `t' ≤ t`.

Why: a set of validators each in the adversary set at some time at most `t'` has each in it at
some time at most `t`.

The variables:
- `Sched`: the schedule; `t'`, `t`: the two times, `t' ≤ t`.



Read aloud: if fewer than a third of the validators have been in the adversary set up to `t`, then
fewer than a third have been up to any earlier time. -/
theorem adversaryFewerThanThirdUntil_mono (Sched : Schedule V) {t' t : Int} (hle : t' ≤ t)
    (h : AdversaryFewerThanThirdUntil Sched (validator_count V) t) : AdversaryFewerThanThirdUntil Sched (validator_count V) t' :=
  GoldilocksCorrectness.Proofs.Executions.adversaryFewerThanThirdUntil_mono Sched hle h

/-- **Agreement after healing is monotone in its start.** Agreement of the confirmed tips of honest
validators from `tE` implies agreement from any later `tE'`.

Why: two steps at times at least `tE'` are at times at least `tE`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`, `tE'`: the two times,
  `tE ≤ tE'`.



Read aloud: if the confirmed tips of honest validators agree from `tE`, they agree from any later
time. -/
theorem confirmedAgree_mono (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    {tE tE' : ℕ} (hle : tE ≤ tE') (h : ConfirmedAgreeAfterHealing S Sched x tE) :
    ConfirmedAgreeAfterHealing S Sched x tE' :=
  GoldilocksCorrectness.Proofs.Executions.confirmedAgree_mono S Sched x hle h

/-- **Growth after healing is monotone in its start.** Growth of an honest validator's confirmed
tip from `tE` implies growth from any later `tE'`.

Why: a step at a time at least `tE'` is at a time at least `tE`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`, `tE'`: the two times,
  `tE ≤ tE'`.



Read aloud: if every honest validator's confirmed tip only extends from `tE`, it only extends from
any later time. -/
theorem confirmedMonotone_mono (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) {tE tE' : ℕ} (hle : tE ≤ tE')
    (h : ConfirmedMonotoneAfterHealing S Sched x tE) :
    ConfirmedMonotoneAfterHealing S Sched x tE' :=
  GoldilocksCorrectness.Proofs.Executions.confirmedMonotone_mono S Sched x hle h

/-- **Inclusion after healing is monotone in its start.** Inclusion for the slots starting at or
after `tE` implies it for the slots starting at or after `tE' ≥ tE`.

Why: a slot starting at or after `tE'` starts at or after `tE`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`, `tE'`: the two times,
  `tE ≤ tE'`.



Read aloud: if inclusion holds for every slot starting at or after `tE`, it holds for every slot
starting at or after any later time. -/
theorem confirmedIncluded_mono (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) {tE tE' : ℕ} (hle : tE ≤ tE')
    (h : ConfirmedIncludedAfterHealing S Sched x tE) :
    ConfirmedIncludedAfterHealing S Sched x tE' :=
  GoldilocksCorrectness.Proofs.Executions.confirmedIncluded_mono S Sched x hle h

/-! ## Lemma 81 bounded -/

/-- **Lemma 81 bounded.** Lemma 81's hypotheses with the frames only at the slots `s` with
`s₀ < s < n`: the updaters' confirmations of the slots from `s₀` to before `n` form one chain.

The hypotheses, in words: every time is reached; corruption is permanent; blocks and Goldfish votes
are delivered within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake);
a root names one block among what honest validators hold; a block
reaches a validator only once it holds the parent; nobody votes in an honest validator's name;
`GST` is at most the vote time of slot `s₀`; committee sleepiness holds from `anchor`, and slot
`s₀ + 1` starts at or after `anchor`; `B₀`'s slot is at least `s₀`; `HonestChainExtends` holds for
`B₀` at slot `s₀` at the honest active validators of slot `s₀`; every updater of slot `s₀` holds
`B₀` as its confirmation of slot `s₀` right after the support cutoff of slot `s₀ + 1`; and at every
slot `s` with `s₀ < s < n`, every honest active validator of slot `s` satisfies
`VoterFrameOnChainAt S Sched x s₀ s` and every updater of slot `s` satisfies
`UpdaterFinalizedOnChainAt S Sched x s₀ s`. The conclusion:
`ConfirmationsChainBefore S Sched x s₀ n`.

Why: Lemma 81's proof, with the induction on the slot stopped before `n`. The step to a slot
`s + 1 < n` reads the voter frame at `s + 1` and the updater frames at `s` and `s + 1`; two
confirmations of slots `s < s'' < n` are ordered by Lemma 78 under the invariant at `s''` and the
updater frame at `s''`; two of one slot are compatible by Lemma 32.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `n`: the bound on the slots; `B₀`: the block every updater of slot `s₀`
  saved.



Read aloud: the frames at the slots before `n` already make the honest confirmations of the slots
before `n` one chain.

Roots name blocks until `supportCutoff S n`: the induction (`lem81_inv_before`) takes blocks as
held up to the support cutoff of slot `n − 1`, and the ordering of two confirmations of slots `s
≤ s' < n` reads Lemma 32 at slot `s`, up to the support cutoff of slot `s + 1`. -/
theorem lem81_chain_before (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor n : ℕ) (B₀ : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S n))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s₀)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ slotStart S (s₀ + 1))
    (hB₀slot : s₀ ≤ B₀.slot)
    (hBase : HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀)
    (hBaseSaved : ∀ v ∈ updaterAt S Sched s₀,
      (stateBefore x (supportCutoff S (s₀ + 1) + 1) v).A.saved_confirmation s₀ = some B₀)
    -- the frames at the slots after `s₀` and before `n`
    (hVoterFrame : ∀ s : ℕ, s₀ < s → s < n → ∀ w ∈ honestActiveAt S Sched s,
      VoterFrameOnChainAt S Sched x s₀ s w)
    (hUpdaterFrame : ∀ s : ℕ, s₀ < s → s < n → ∀ v ∈ updaterAt S Sched s,
      UpdaterFinalizedOnChainAt S Sched x s₀ s v) :
    ConfirmationsChainBefore S Sched x s₀ n :=
  GoldilocksCorrectness.Proofs.Executions.lem81_chain_before S Sched x GST s₀ anchor n B₀ hDiv hMono
    hSync hCatch hRoots hParent hOwner hGST hSleepK hAnchor hB₀slot hBase hBaseSaved
    hVoterFrame hUpdaterFrame

/-! ## The caches from one time unit after the hand-over -/

/-- **The caches from the first step one time unit after the hand-over.** Under Lemma 84's
hypotheses with `t₀ := supportCutoff S (s₀ + 1)` (Lemma 82 supplies its agreement premise): when
every validator honest at step `i₁` has its caches on the honest chain, some step `i₂` is at time
`x[i₁].time + 1`, and every validator honest at a step at a time from `x[i₂].time` to `t` has them.

The hypotheses, in words: every time is reached; corruption is permanent; unforgeability; a root
names one block among what honest validators hold by `t`; fewer than a quorum of validators have
been in the adversary set up to every time; every honest attestation sent before the support
cutoff of slot `s₀ + 1` has height at most `H`; the caches of every validator outside the
adversary set at the time of step `i₁` satisfy `CachesOnChain S Sched x s₀ H`.

Why: `i₂` is the first step at the time `x[i₁].time + 1`, the step after
`stepBefore x (x[i₁].time + 1)`; a step at a time at least `x[i₂].time` is at a time greater than
`x[i₁].time`, so after `i₁`, and Lemma 84 applies there. The step is taken one time unit later
than `i₁` because Lemma 84 concludes for the steps after `i₁`, while the facts after healing read
every step at a time at least the hand-over's.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `H`: the
  threshold; `i₁`: the step at the hand-over; `t`: the bound on the times of the steps; `i₂`: the
  step from which the caches are on the chain.



Read aloud: from one time unit after the hand-over, every honest validator's caches are on the
honest chain, at every step at a time at most `t`.

Roots name blocks until `t`: the conclusion is for the steps at times at most `t`, and at each such step the proof reads Lemma 84 up to `t`. -/
theorem caches_after_handover (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ H i₁ t : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (hRoots : RootsNameBlocksUntil S Sched x t)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hStart : ∀ u : V, u ∉ Sched.adv (x[i₁].time : Int) →
      CachesOnChain S Sched x s₀ H (x[i₁][u].st)) :
    ∃ i₂ : ℕ, x[i₂].time = x[i₁].time + 1 ∧
      ∀ (j : ℕ) (u : V), x[i₂].time ≤ x[j].time → x[j].time ≤ t →
        u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st) :=
  GoldilocksCorrectness.Proofs.Executions.caches_after_handover S Sched x s₀ H i₁ t hDiv hMono hU
    hRoots hAdvQ hOld hStart

/-! ## The updater frame after the hand-over -/

/-- **The updater frame after the hand-over.** With the confirmations of the slots before `s`
forming one chain, the old attestations at most `H`, the caches from `i₂`, fewer than a quorum ever
in the adversary set, and the support cutoff of slot `s + 1` after `x[i₂].time`: every updater of
slot `s` has its finalized block compatible with every block on the honest chain before `s`.

The hypotheses, in words: every time is reached; corruption is permanent; a root names one block
among what honest validators hold; unforgeability; fewer than a quorum of validators have been in
the adversary set up to every time; every honest attestation sent before the support cutoff of
slot `s₀ + 1` has height at most `H`; every validator outside the adversary set at a step at a
time at least `x[i₂].time` has its caches on the honest chain (`CachesOnChain S Sched x s₀ H`);
`x[i₂].time` is less than the support cutoff of slot `s + 1`;
`ConfirmationsChainBefore S Sched x s₀ s`; `v` is an updater of slot `s`. The conclusion:
`UpdaterFinalizedOnChainAt S Sched x s₀ s v`.

Why: at the step before the support cutoff of slot `s + 1`, `v` is honest and the step is at a
time at least `x[i₂].time`; the root of `v`'s fork choice there is on the honest chain before `s`
(Lemma 91 (f): every slot whose next slot's support cutoff is at most that time is less than
`s`), so it is compatible with every block of that chain; the finalized block is the root or an
ancestor of it (Lemma 46).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `i₂`: the step
  from which the caches are on the chain; `H`: the threshold; `s`: the slot; `v`: the updater.



Read aloud: after the hand-over, an updater's finalized block never conflicts with the honest chain
before its slot.

Roots name blocks until `supportCutoff S (s + 1)`: the proof reads Lemma 91 (f) at the step
before that time, whose bound is the time of that step. -/
theorem updaterFrame_after_handover (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ i₂ H s : ℕ) (v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1))) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₂].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hs : x[i₂].time < supportCutoff S (s + 1))
    (hChain : ConfirmationsChainBefore S Sched x s₀ s)
    (hv : v ∈ updaterAt S Sched s) :
    UpdaterFinalizedOnChainAt S Sched x s₀ s v :=
  GoldilocksCorrectness.Proofs.Executions.updaterFrame_after_handover S Sched x s₀ i₂ H s v hDiv
    hMono hRoots hU hAdvQ hOld hCaches hs hChain hv

/-- **The updater frame after the hand-over.** With the confirmations of the slots before `s`
forming one chain, the old attestations at most `H`, the caches from `i₂` to the support cutoff of
slot `s + 1`, fewer than a quorum ever in the adversary set, and the support cutoff of slot `s + 1`
after `x[i₂].time`: every updater of slot `s` has its finalized block compatible with every block on
the honest chain before `s`.

The hypotheses, in words: every time is reached; corruption is permanent; a root names one block
among what honest validators hold; unforgeability; fewer than a quorum of validators have been in
the adversary set up to every time; every honest attestation sent before the support cutoff of slot
`s₀ + 1` has height at most `H`; every validator outside the adversary set at a step at a time from
`x[i₂].time` to `supportCutoff S (s + 1)` has its caches on the honest chain
(`CachesOnChain S Sched x s₀ H`); `x[i₂].time` is less than the support cutoff of slot `s + 1`;
`ConfirmationsChainBefore S Sched x s₀ s`; `v` is an updater of slot `s`. The conclusion:
`UpdaterFinalizedOnChainAt S Sched x s₀ s v`.

Why: at the step before the support cutoff of slot `s + 1`, `v` is honest and the step is at a
time at least `x[i₂].time`; the root of `v`'s fork choice there is on the honest chain before `s`
(Lemma 91 (f): every slot whose next slot's support cutoff is at most that time is less than
`s`), so it is compatible with every block of that chain; the finalized block is the root or an
ancestor of it (Lemma 46).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `i₂`: the step
  from which the caches are on the chain; `H`: the threshold; `s`: the slot; `v`: the updater.



Read aloud: after the hand-over, an updater's finalized block never conflicts with the honest chain
before its slot.

Roots name blocks until `supportCutoff S (s + 1)`: the proof reads Lemma 91 (f) at the step
before that time, whose bound is the time of that step.

Caches up to `supportCutoff S (s + 1)`: the proof reads `v`'s caches before the support cutoff of
slot `s + 1`.  -/
theorem updaterFrame_after_handover_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ i₂ H s : ℕ) (v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1))) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₂].time ≤ x[j].time → x[j].time ≤ supportCutoff S (s + 1) →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hs : x[i₂].time < supportCutoff S (s + 1))
    (hChain : ConfirmationsChainBefore S Sched x s₀ s)
    (hv : v ∈ updaterAt S Sched s) :
    UpdaterFinalizedOnChainAt S Sched x s₀ s v :=
  GoldilocksCorrectness.Proofs.Executions.updaterFrame_after_handover_until S Sched x s₀ i₂ H s v
    hDiv hMono hRoots hU hAdvQ hOld hCaches hs hChain hv

end GoldilocksCorrectness.Statements.Executions
