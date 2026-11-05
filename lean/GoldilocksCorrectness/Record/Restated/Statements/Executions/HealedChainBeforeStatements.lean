module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HealedChainBefore
public import GoldilocksCorrectness.Statements.Executions.HealedChainBeforeStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# HealedChainBeforeStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/HealedChainBeforeStatements.lean`,
over a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the monotonicity of
the confirmation statements in their bound, Lemma 81 on the honest chain before the healed slot, and
the caches and the updaters' frame after the hand-over. Each is the theorem of the same name of
`Record/Restated/Proofs/Executions/HealedChainBefore.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject)

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

/-! ## The monotonicity facts in the time -/

omit [RootOrder] in
/-- **Fewer than a third in the adversary set is monotone in the time.** Fewer than a third of the
validators in the adversary set at some time up to `t` implies the same up to `t' ≤ t`.

Why: a set of validators each in the adversary set at some time at most `t'` has each in it at
some time at most `t`.

The variables:
- `M`: the model; `F`: its facts;
- `Sched`: the schedule; `t'`, `t`: the two times, `t' ≤ t`.



Read aloud: if fewer than a third of the validators have been in the adversary set up to `t`, then
fewer than a third have been up to any earlier time. -/
theorem adversaryFewerThanThirdUntil_mono (A : Activity V) (x : Trace V (NamedObject V) M.N) {t' t : ℕ} (hle : t' ≤ t)
    (h : A.AdversaryFewerThanThirdUntil x (validator_count V) t) : A.AdversaryFewerThanThirdUntil x (validator_count V) t' :=
  (GoldilocksCorrectness.Record.Proofs.Executions.adversaryFewerThanThirdUntil_mono M F) A x hle h

/-- **Inclusion after healing is monotone in its start.** Inclusion for the slots starting at or
after `tE` implies it for the slots starting at or after `tE' ≥ tE`.

Why: a slot starting at or after `tE'` starts at or after `tE`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`, `tE'`: the two times,
  `tE ≤ tE'`.



Read aloud: if inclusion holds for every slot starting at or after `tE`, it holds for every slot
starting at or after any later time. -/
theorem confirmedIncluded_mono (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) {tE tE' : ℕ} (hle : tE ≤ tE')
    (h : ConfirmedIncludedAfterHealing M S A x tE) :
    ConfirmedIncludedAfterHealing M S A x tE' :=
  (GoldilocksCorrectness.Record.Proofs.Executions.confirmedIncluded_mono M F) S A x hle h

/-! ## Lemma 81 bounded -/

/-- **Lemma 81 bounded.** Lemma 81's hypotheses with the frames only at the slots `s` with
`s₀ < s < n`: the updaters' confirmations of the slots from `s₀` to before `n` form one chain.

The hypotheses, in words: every time is reached; corruption is permanent; blocks and Goldfish votes
are delivered within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake);
a root names one block among what honest validators hold, up to every validator's tick to a clock
value at most the support cutoff of slot `n`; a block reaches a validator only once it holds the parent; nobody votes in an honest validator's name;
`GST` is at most the vote time of slot `s₀`; committee sleepiness holds from `anchor`, and slot
`s₀ + 1` starts at or after `anchor`; `B₀`'s slot is at least `s₀`; `HonestChainExtends` holds for
`B₀` at slot `s₀` at the honest active validators of slot `s₀`; every updater of slot `s₀` holds
`B₀` as its confirmation of slot `s₀` right after the support cutoff of slot `s₀ + 1`; and at every
slot `s` with `s₀ < s < n`, every honest active validator of slot `s` satisfies
`VoterFrameOnChainAt M S Sched x s₀ s` and every updater of slot `s` satisfies
`UpdaterFinalizedOnChainAt M S Sched x s₀ s`. The conclusion:
`ConfirmationsChainBefore M S Sched x s₀ n`.

Why: Lemma 81's proof, with the induction on the slot stopped before `n`. The step to a slot
`s + 1 < n` reads the voter frame at `s + 1` and the updater frames at `s` and `s + 1`; two
confirmations of slots `s < s'' < n` are ordered by Lemma 78 under the invariant at `s''` and the
updater frame at `s''`; two of one slot are compatible by Lemma 32.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `n`: the bound on the slots; `B₀`: the block every updater of slot `s₀`
  saved.



Read aloud: the frames at the slots before `n` already make the honest confirmations of the slots
before `n` one chain.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C n`: the
induction (`lem81_inv_before`) takes blocks as held up to the support cutoff of slot `n - 1`, which an
honest committee member's tick to the support cutoff of slot `n` reaches (at a real time at least that
cutoff minus `ΔClockAhead`), and the ordering of two confirmations of one slot `s < n` reads Lemma 32
at `s`, up to the two updaters' ticks to the support cutoff of slot `s + 1`. -/
theorem lem81_chain_before (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor n : ℕ) (B₀ : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C n →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x) (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C n)) (hAnchor : anchor ≤ M.slotStart S.C (s₀ + 1))
    (hB₀slot : s₀ ≤ B₀.slot)
    (hBase : HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀)
    (hBaseSaved : ∀ v ∈ updaterAt M S A x s₀,
      (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀)
    -- the frames at the slots after `s₀` and before `n`
    (hVoterFrame : ∀ s : ℕ, s₀ < s → s < n → ∀ w ∈ honestActiveAt M S A x s,
      VoterFrameOnChainAt M S A x s₀ s w)
    (hUpdaterFrame : ∀ s : ℕ, s₀ < s → s < n → ∀ v ∈ updaterAt M S A x s,
      UpdaterFinalizedOnChainAt M S A x s₀ s v) :
    ConfirmationsChainBefore M S A x s₀ n :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem81_chain_before M F U) S A x R GST s₀ anchor
    n B₀ E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hSleepK hAnchor hB₀slot hBase hBaseSaved
    hVoterFrame hUpdaterFrame

/-! ## The caches from one time unit after the hand-over -/

/-- **The caches after the hand-over.** Under Lemma 84's hypotheses with
`t₀ := M.supportCutoff S.C (s₀ + 1)` (Lemma 82 supplies its agreement premise): when every validator
honest at step `i₁` has its caches on the honest chain, every validator honest at a step at a time
after `x[i₁].time` and at most `t` has them.

The hypotheses, in words: every time is reached; corruption is permanent; unforgeability; a root
names one block among what honest validators hold by `t`; fewer than a quorum of validators have
been in the adversary set up to every time; every honest attestation sent before the support
cutoff of slot `s₀ + 1` has height at most `H`; the caches of every validator outside the
adversary set at the time of step `i₁` satisfy `CachesOnChain M S Sched x s₀ H`.

Why: a step at a time greater than `x[i₁].time` comes after `i₁` (`lt_of_time_lt`), and Lemma 84
applies there; a validator honest after that step is honest after every step whose time is at most
`x[i₁].time`.

 it now reads every step after `x[i₁].time`, which is what the old proof gave.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `H`: the
  threshold; `i₁`: the step at the hand-over; `t`: the bound on the times of the steps.



Read aloud: at every step after the hand-over up to `t`, every honest validator's caches are on the
honest chain.

Roots name blocks until `t`: the conclusion is for the steps at times at most `t`, and at each such step the proof reads Lemma 84 up to `t`. -/
theorem caches_after_handover (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ H i₁ t : ℕ)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
      (hRoots : RootsNameBlocksUntil M A x t)
    -- fewer than a quorum of validators have been in the adversary set up to the later of `t` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max t (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the caches of every validator outside the adversary set after every step whose time is that of
    -- step `i₁` are on the honest chain (B19-2 (a))
    (hStart : ∀ u : V, u ∉ A.corruptedAtTime x (x.time i₁) →
      CachesOnChain M S A x s₀ H (x.st i₁ u)) :
    ∀ (j : ℕ) (u : V), x.time i₁ < x.time j → x.time j ≤ t →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.caches_after_handover M F U Fx) S A x R s₀ H i₁
    t E hRoots hAdvQ hOld hStart

/-! ## The updater frame after the hand-over -/

/-- **The updater frame after the hand-over.** With the confirmations of the slots before `s`
forming one chain, the slot-`s` confirmations of the updaters that ticked to the support cutoff of
slot `s + 1` before `v` extending that chain, the old attestations at most `H`, the caches from
`i₂`, fewer than a quorum in the adversary set up to `v`'s tick to that cutoff, and every tick to
that cutoff after `x[i₂].time`: the updater `v` of slot `s` has its finalized block compatible with
every block on the honest chain before `s`.

The hypotheses, in words: the clock bounds' sum is less than `Δ S`; a root names one block among
what honest validators hold up to the real time of `v`'s tick to the support cutoff of slot `s + 1`;
fewer than a quorum of validators have been in the adversary set up to the later of that real time
and the hand-over cutoff; every honest attestation sent before the support cutoff of slot `s₀ + 1`
has height at most `H`; every validator outside the adversary set at a step at a time after
`x[i₂].time` has its caches on the honest chain (`CachesOnChain M S Sched x s₀ H`); every tick to the
support cutoff of slot `s + 1` is at a real time after `x[i₂].time`;
`ConfirmationsChainBefore M S Sched x s₀ s`; the slot-`s` confirmation saved by every updater of
slot `s` whose tick to that cutoff is at a step before `v`'s has every block of the honest chain
before `s` as an ancestor; `v` is an updater of slot `s`. The conclusion:
`UpdaterFinalizedOnChainAt M S Sched x s₀ s v`.

Why: at `v`'s tick to the support cutoff of slot `s + 1`, `v` is honest and the step is at a time
after `x[i₂].time`; the certificate of `v`'s justified block names, by root, an entry held by an
honest attester at its tick to the support cutoff of a slot `sₐ`, before `v`'s, which is that block,
an ancestor of the attester's confirmation of `sₐ`; the finalized block is an ancestor of the
justified block. For `sₐ < s` it is on the honest chain before `s`; for `sₐ = s` the attester's
confirmation extends that chain; `sₐ > s` is impossible under the clock bounds.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `i₂`: the step
  from which the caches are on the chain; `H`: the threshold; `s`: the slot; `v`: the updater.



Read aloud: after the hand-over, an updater's finalized block never conflicts with the honest chain
before its slot.

Roots name blocks, fewer than a quorum have been in the adversary set, and the caches hold, up to the
real time of `v`'s tick to the support cutoff of slot `s + 1`: the proof reads Lemma 91 (f)'s route
at that tick's step. The confirmations of slot `s` saved by the updaters that ticked to that cutoff
before `v` extend the chain before `s`: a certificate `v` holds at its tick may carry such an
updater's attestation of slot `s`, whose entry is an ancestor of that confirmation. -/
theorem updaterFrame_after_handover (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ i₂ H s : ℕ) (v : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the sum of the two clock bounds is less than `Δ S`
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    -- fewer than a quorum of validators have been in the adversary set up to the later of the real time of `v`'s tick to `M.supportCutoff S.C (s + 1)` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))) (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the caches at every step at a real time after `x[i₂].time`
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₂ < x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    -- every tick to the support cutoff of slot `s + 1` is at a real time after `x[i₂].time`
    (hs : ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (s + 1)) → x.time i₂ < x.time k)
    (hChain : ConfirmationsChainBefore M S A x s₀ s)
    -- the slot-`s` confirmations of the updaters that ticked to that cutoff before `v` extend the chain before `s`
    (hEarlier : ∀ u ∈ updaterAt M S A x s,
      x.tickStep u (M.supportCutoff S.C (s + 1)) < x.tickStep v (M.supportCutoff S.C (s + 1)) →
      ∀ C : Block V, OnHonestChainBefore M S A x s₀ s C → ∀ C' : Block V,
        (x.tickOutput u (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C' → C.AncestorEq C')
    (hv : v ∈ updaterAt M S A x s) :
    UpdaterFinalizedOnChainAt M S A x s₀ s v :=
  (GoldilocksCorrectness.Record.Proofs.Executions.updaterFrame_after_handover M F U Fx) S A x R s₀
    i₂ H s v E hSkew hRoots hAdvQ hOld hCaches hs hChain hEarlier hv

/-- **The updater frame after the hand-over.** With the confirmations of the slots before `s`
forming one chain, the slot-`s` confirmations of the updaters that ticked to the support cutoff of
slot `s + 1` before `v` extending that chain, the old attestations at most `H`, the caches from
`i₂` to `v`'s tick to that cutoff, fewer than a quorum in the adversary set up to that tick, and
every tick to that cutoff after `x[i₂].time`: the updater `v` of slot `s` has its finalized block
compatible with every block on the honest chain before `s`.

The hypotheses, in words: as `updaterFrame_after_handover`'s, with the caches asked only at the steps
at a time after `x[i₂].time` and at most the real time of `v`'s tick to the support cutoff of slot `s + 1`:
the clock bounds' sum is less than `Δ S`; a root names one block among what honest validators hold up
to the real time of `v`'s tick to the support cutoff of slot `s + 1`; fewer than a quorum of
validators have been in the adversary set up to the later of that real time and the hand-over
cutoff; every honest attestation sent before the support cutoff of slot `s₀ + 1` has height at most
`H`; every validator outside the adversary set at a step at a time after `x[i₂].time` and at most that real
time has its caches on the honest chain (`CachesOnChain M S Sched x s₀ H`); every tick to the support
cutoff of slot `s + 1` is at a real time after `x[i₂].time`; `ConfirmationsChainBefore M S Sched x
s₀ s`; the slot-`s` confirmation saved by every updater of slot `s` whose tick to that cutoff is at a
step before `v`'s has every block of the honest chain before `s` as an ancestor; `v` is an updater of
slot `s`. The conclusion: `UpdaterFinalizedOnChainAt M S Sched x s₀ s v`.

Why: as `updaterFrame_after_handover`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `i₂`: the step
  from which the caches are on the chain; `H`: the threshold; `s`: the slot; `v`: the updater.



Read aloud: after the hand-over, an updater's finalized block never conflicts with the honest chain
before its slot.

Roots name blocks, fewer than a quorum have been in the adversary set, and the caches hold, up to the
real time of `v`'s tick to the support cutoff of slot `s + 1`: the proof reads Lemma 91 (f)'s route
at that tick's step. The confirmations of slot `s` saved by the updaters that ticked to that cutoff
before `v` extend the chain before `s`: a certificate `v` holds at its tick may carry such an
updater's attestation of slot `s`, whose entry is an ancestor of that confirmation.  -/
theorem updaterFrame_after_handover_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ i₂ H s : ℕ) (v : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the sum of the two clock bounds is less than `Δ S`
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    -- fewer than a quorum of validators have been in the adversary set up to the later of the real time of `v`'s tick to `M.supportCutoff S.C (s + 1)` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))) (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the caches at every step at a real time after `x[i₂].time`
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₂ < x.time j → x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    -- every tick to the support cutoff of slot `s + 1` is at a real time after `x[i₂].time`
    (hs : ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (s + 1)) → x.time i₂ < x.time k)
    (hChain : ConfirmationsChainBefore M S A x s₀ s)
    -- the slot-`s` confirmations of the updaters that ticked to that cutoff before `v` extend the chain before `s`
    (hEarlier : ∀ u ∈ updaterAt M S A x s,
      x.tickStep u (M.supportCutoff S.C (s + 1)) < x.tickStep v (M.supportCutoff S.C (s + 1)) →
      ∀ C : Block V, OnHonestChainBefore M S A x s₀ s C → ∀ C' : Block V,
        (x.tickOutput u (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C' → C.AncestorEq C')
    (hv : v ∈ updaterAt M S A x s) :
    UpdaterFinalizedOnChainAt M S A x s₀ s v :=
  (GoldilocksCorrectness.Record.Proofs.Executions.updaterFrame_after_handover_until M F U Fx) S
    A x R s₀ i₂ H s v E hSkew hRoots hAdvQ hOld hCaches hs hChain hEarlier hv

end GoldilocksCorrectness.Record.Statements.Executions

