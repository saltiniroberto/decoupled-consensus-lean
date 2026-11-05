module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ConfirmedTipDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma90
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma90Inclusion
public import GoldilocksCorrectness.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# ConfirmedTipStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/ConfirmedTipStatements.lean`, over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the record of the
confirmed tip after the healed slot, Lemma 90's agreement and growth of the confirmed tip, and the
inclusion of the honest proposal, the theorems of the same names of
`Record/Restated/Proofs/Executions/Lemma90.lean` and
`Record/Restated/Proofs/Executions/Lemma90Inclusion.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff
  proposalWindowStart)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated)
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks)
open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax JustifiedInTree)
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

/-! ## The routine facts -/

/-! ## The record after the healed slot -/

open Classical in
/-- **`lem90a_latest_confirmed_honest_at`, the record after the healed round is an honest
confirmation of a slot whose update ran by then.** In an execution where every time is reached
and corruption is permanent, with the two clock bounds together less than one delay: when `B₀`'s slot is at
least `s₀`, `HonestChainExtends` holds for `B₀` at slot `s₀` at the honest active validators of
slot `s₀`, every updater of slot `s₀` holds `B₀` as its confirmation of slot `s₀` right after the
support cutoff of slot `s₀ + 1`, and every validator outside the adversary set at that support
cutoff is an updater of slot `s₀` — then at every step after a validator's own tick to that support
cutoff, the validator honest at that cutoff, at every honest validator's tick to that cutoff and at the step's time has as its record of the confirmed
tip the confirmation of some slot `s ≥ s₀` that an updater of slot `s` saved at its own update, the
validator's tick to the support cutoff of slot `s + 1` being a step before the step read, and the
validator holds its record.

Why: `lem90a_latest_confirmed_honest`'s induction, with the slot of the record kept: right after the
update of slot `s₀` the record is `B₀`, the confirmation of slot `s₀`; afterwards the record changes
only at the validator's own update of a slot `s + 1`, at the support cutoff of slot `s + 1`, to the
confirmation of slot `s` it saves.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `B₀`: the block every updater of slot `s₀` saved.



Read aloud: a validator honest at the healed cutoff and whenever an honest validator ticks to it, after
its own tick to it, and honest after every
step whose time is at most the step's, has as its latest confirmed block the confirmation some updater
of a slot `s ≥ s₀` saved at its own update, an update that ran before the step; and it holds that
block. -/
theorem lem90a_latest_confirmed_honest_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ : ℕ) (B₀ : Block V)
    -- every time is reached
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the two clock bounds together are less than one delay
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    -- corruption is permanent
    -- `B₀`'s slot is at least `s₀`
    (hB₀slot : s₀ ≤ B₀.slot)
    -- the slot invariant restricted to `B₀` at slot `s₀`
    (hBase : HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀)
    -- every updater of slot `s₀` saved `B₀`
    (hBaseSaved : ∀ v ∈ updaterAt M S A x s₀,
      (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀)
    -- every validator honest at the support cutoff of slot `s₀ + 1` is an updater of slot `s₀`
    (hAwake : ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1)) →
      v ∈ updaterAt M S A x s₀) :
    ∀ (i : ℕ) (v : V), v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1)) ∪
      Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
        x.lbl k = Event.tick w (M.supportCutoff S.C (s₀ + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k) →
      x.tickStep v (M.supportCutoff S.C (s₀ + 1)) < i → v ∉ A.corrupted i →
      (∃ s : ℕ, s₀ ≤ s ∧ x.lbl (x.tickStep v (M.supportCutoff S.C (s + 1))) = Event.tick v (M.supportCutoff S.C (s + 1)) ∧
        x.tickStep v (M.supportCutoff S.C (s + 1)) < i ∧ ∃ u ∈ updaterAt M S A x s,
        (x.tickOutput u (M.supportCutoff S.C (s + 1))).savedConfirmation s =
          some (x.st i v).latestConfirmed) ∧
        (x.st i v).latestConfirmed ∈ (x.st i v).tree :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem90a_latest_confirmed_honest_at M F U) S A x R
    s₀ B₀ E hSkew hB₀slot hBase hBaseSaved hAwake

/-! ## Lemma 90 -/

/-- **Lemma 90, agreement, on the chain before a slot.** In an execution where every time is reached
and corruption is permanent, under unforgeability, with fewer than a quorum of validators ever in
the adversary set, every honest attestation sent before the support cutoff of slot `s₀ + 1` of
height at most `H`, and roots naming blocks among what honest validators hold by `t`: when the
updaters' confirmations of the slots whose update some validator ran at a step by the time `t` (a
tick to the support cutoff of the next slot) form one chain from slot `s₀` (`ConfirmationsChainBefore`),
and in the state each step at a time from `x[i₁].time` to `t` leaves every validator outside the
adversary set at the step has as its record a block on the honest chain at a slot whose update it ran
at that step or an earlier one, and
its caches on the honest chain with the threshold `H`:
`ConfirmedAgreeBetween M S Sched x (x[i₁].time) t`, the confirmed tips of two validators honest
through their steps, at times from `x[i₁].time` to `t`, are compatible.

Why: each confirmed tip is the record or the finalized block; the finalized block is the justified
block or an ancestor of it, and the justified block, above the threshold, is on the honest chain at
a slot whose update ran by the step (Lemmas 66 and 83, the roots premise); so both tips are on the
chain at slots whose update is at most `t`, and two such blocks are compatible
(`ConfirmationsChainBefore` at the slot after the later one).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `H`: the threshold of the caches; `i₁`: the step from whose time the facts hold; `t`: the time
  up to which the confirmed tips are read.



Read aloud: when the confirmations of the slots some validator updated by `t` form one chain, from the phase's end
to `t` the confirmed tips of two validators honest at their steps are compatible. -/
theorem lem90_confirmed_agree_before (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ H i₁ t : ℕ)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hRoots : RootsNameBlocksUntil M A x t)
    -- fewer than a quorum of validators have been in the adversary set up to the later of `t` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max t (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the updaters' confirmations of the slots whose update some validator ran at a step by `t` form one chain
    (hChain : ∀ (σ k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1)) →
        x.time k ≤ t → ConfirmationsChainBefore M S A x s₀ (σ + 1))
    -- in the state each step at a time from that of step `i₁` to `t` leaves, an honest validator's record is on the honest chain at a
    -- slot whose update it ran at an earlier step
    (hLatest : ∀ (i : ℕ) (v : V), x.time i₁ ≤ x.time i → x.time i ≤ t →
      v ∉ A.corrupted i → ∃ σ : ℕ, x.lbl (x.tickStep v (M.supportCutoff S.C (σ + 1))) = Event.tick v (M.supportCutoff S.C (σ + 1)) ∧ x.tickStep v (M.supportCutoff S.C (σ + 1)) < i + 1 ∧
        OnHonestChainAt M S A x s₀ σ (x.st (i + 1) v).latestConfirmed)
    -- in the state each step at a time from that of step `i₁` to `t` leaves, an honest validator's caches are on the honest chain
    (hCaches : ∀ (i : ℕ) (v : V), x.time i₁ ≤ x.time i → x.time i ≤ t →
      v ∉ A.corrupted i → CachesOnChain M S A x s₀ H (x.st (i + 1) v)) :
    ConfirmedAgreeBetween M S A x (x.time i₁) t :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem90_confirmed_agree_before M F U Fx) S A x R
    s₀ H i₁ t E hRoots hAdvQ hOld hChain hLatest hCaches

/-- **Lemma 90, growth, on the chain before a slot.** In an execution where every time is reached
and corruption is permanent, under unforgeability, with fewer than a quorum of validators ever in
the adversary set, every honest attestation sent before the support cutoff of slot `s₀ + 1` of
height at most `H`, and roots naming blocks among what honest validators hold by `t`: when the
updaters' confirmations of the slots whose update some validator ran at a step by the time `t` (a
tick to the support cutoff of the next slot) form one chain from slot `s₀` (`ConfirmationsChainBefore`),
and in the state each step at a time from `x[i₁].time` to `t` leaves every validator outside the
adversary set at the step has as its record a block on the honest chain at a slot whose update it ran
at that step or an earlier one,
which it holds, and its caches on the honest chain with the threshold `H`:
`ConfirmedMonotoneBetween M S Sched x (x[i₁].time) t`, the confirmed tip of a validator honest
through the later of two steps, the later at a time at most `t`, only extends.

Why: by induction on the later step: at each step the records and the finalized blocks at the two
steps are on the honest chain at slots whose update is at most `t` (the finalized block through the
justified block, Lemmas 66 and 83), so compatible, and the step lemma of Lemma 90's growth
(`confirmedOf_step_of_compatible`) reads only these compatibilities.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `H`: the threshold of the caches; `i₁`: the step from whose time the facts hold; `t`: the time
  up to which the later confirmed tip is read.



Read aloud: when the confirmations of the slots some validator updated by `t` form one chain, from the phase's end
to `t` the confirmed tip of a validator honest through the later of two steps only extends. -/
theorem lem90_confirmed_monotone_before (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ H i₁ t : ℕ)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hRoots : RootsNameBlocksUntil M A x t)
    -- fewer than a quorum of validators have been in the adversary set up to the later of `t` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max t (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the updaters' confirmations of the slots whose update some validator ran at a step by `t` form one chain
    (hChain : ∀ (σ k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1)) →
        x.time k ≤ t → ConfirmationsChainBefore M S A x s₀ (σ + 1))
    -- in the state each step at a time from that of step `i₁` to `t` leaves, an honest validator's record is on the honest chain at a
    -- slot whose update it ran at an earlier step, and it holds it
    (hLatest : ∀ (i : ℕ) (v : V), x.time i₁ ≤ x.time i → x.time i ≤ t →
      v ∉ A.corrupted i → (∃ σ : ℕ, x.lbl (x.tickStep v (M.supportCutoff S.C (σ + 1))) = Event.tick v (M.supportCutoff S.C (σ + 1)) ∧ x.tickStep v (M.supportCutoff S.C (σ + 1)) < i + 1 ∧
        OnHonestChainAt M S A x s₀ σ (x.st (i + 1) v).latestConfirmed) ∧
        (x.st (i + 1) v).latestConfirmed ∈ (x.st (i + 1) v).tree)
    -- in the state each step at a time from that of step `i₁` to `t` leaves, an honest validator's caches are on the honest chain
    (hCaches : ∀ (i : ℕ) (v : V), x.time i₁ ≤ x.time i → x.time i ≤ t →
      v ∉ A.corrupted i → CachesOnChain M S A x s₀ H (x.st (i + 1) v)) :
    ConfirmedMonotoneBetween M S A x (x.time i₁) t :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem90_confirmed_monotone_before M F U Fx) S A
    x R s₀ H i₁ t E hRoots hAdvQ hOld hChain hLatest hCaches

/-! ## Lemma 90, inclusion

The inclusion of the honest proposal after healing, proved in
`GoldilocksCorrectness/Proofs/Executions/Lemma90Inclusion.lean`: the per-validator export
`lem90_included_update_facts`, the inclusion `lem90_confirmed_included`, both with the lock invariant
at the healed slot (`hLocks₀`), the inclusion read up to a time `t`,
`lem90_confirmed_included_until`, of which `lem90_confirmed_included` is the instance at
every time, and the lock invariant's discharge, `base_locks_on_chain`. -/

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open GoldilocksCorrectness.Statements.Routines (expireLocks)

/-- **The per-validator export of the inclusion, `lem90_included_update_facts`.** In an execution
where every time is reached, corruption is permanent, blocks and Goldfish votes are delivered within
`Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, a block reaches a validator only
once it holds the parent, and nobody votes in an honest validator's name; under unforgeability, with
fewer than a quorum of validators ever in the adversary set (Lemma 87) and committee sleepiness from
`anchor`, at or before `x[i₁].time`; with `GST` at most the vote time of slot `s₀`
 and the support cutoff of slot `s₀ + 1` at or before
`x[i₁].time`; with the honest confirmations forming a chain from slot `s₀` (Lemma 81), the chain
invariant and the lock invariant at every slot after `s₀` (`lem81_inv`), the lock invariant at the
healed slot `s₀` itself (`hLocks₀`: every live lock entry an honest active validator of slot `s₀`
keeps after its revocation of slot `s₀ + 1` is on a block of the honest chain before slot `s₀ + 1`
or on an ancestor of one), every honest attestation sent before the support cutoff of slot `s₀ + 1`
of height at most `H` (Lemma 89), and the caches of every validator honest at a step at a time at
least `x[i₁].time` on the honest chain with justification height greater than `H` (Lemma 84): for a
slot `s` starting after `x[i₁].time` whose proposer is awake and honest from the start of the
proposal window of slot `s` to the support cutoff `c` of slot `s + 1`, whose tick at the start of
slot `s` put `B` on the wire, and no block it held before the start of slot `s` having `B`'s root:
every updater `v` of slot `s`, right after `c`, has saved `B` as the confirmation of slot `s`,
holds `B` among its fast blocks and a lock entry on `B` with the deadline of a slot-`s` lock, has
every lock entry it holds that is live at `c` (on its state before `c`) on `B` or an ancestor of
`B`, and has `B` as its confirmed tip.

The landed statement names the answer `A'` of `v`'s update of slot `s + 1` at `c` and equates `v`'s
state right after `c` with it. The twin states the five facts of that state (D-20A1 (e)); its
recovery takes `A'` from the outcome of `v`'s tick at `c` (`update_state_of_duty`) and Lemma 15.

Why: steps 2 to 5 of the inclusion: the proposal's parent extends
the chain, every honest vote of slot `s` names `B` (Lemma 59 with ordered `head_height_floor` values (the least chain-state height a viable block may have) and Lemma 91),
every updater saves `B` (Lemma 27), fast and locked (Lemma 60), and records it
(`latest_confirmed_after_healed_update`). The brief's `hLatest` is deleted: no step reads it.

Why `hLocks₀`: the route reads the proposer's anchor at the start of slot `s = s₀ + 2`. The anchor
is the root of the proposer's fork choice or a block a live lock entry of the proposer locks, and an
entry left by the proposer's revocation of slot `s₀ + 1` may have been added by an update of a slot
before `s₀`. `hLocks` speaks of slots after `s₀` only, and nothing else in the hypotheses places
such an entry's block on the honest chain; without `hLocks₀` the proposal of slot `s₀ + 2` could
extend a block off the chain and lose the votes. `base_locks_on_chain` derives `hLocks₀` from
Lemma 81's own premises (`HonestChainExtends` at `s₀`, the updaters' saved `B₀`, committee
sleepiness).

The statement of record.

Why `hHold` and `hHoldP`: the votes of
slot `s - 1` reach the proposer, and the votes of slot `s` reach every updater, by the synchrony condition
`SyncedWithin`, which serves a message only while its holder stays active for `Δs` after the real time it
serves at; the honest committee members of those two slots, and the proposer, are those holders.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `s`: the slot; `B`: the proposal; `v`: the updater.

Read aloud: with the lock invariant also at the healed slot, and the honest voters of slots `s - 1` and `s`
and the proposer active for the sync delay after the times the synchrony condition reads them, every updater of the slot confirms the
honest proposal fast, locks it, records it, and keeps no live lock off its chain.



Roots name blocks until `M.supportCutoff S.C (s + 1)`: the proof reads, at slot `s`, the proposer's
and the voters' fork-choice roots up to the vote time of slot `s` and the updaters' up to the
support cutoff of slot `s + 1` (Lemma 91 (f)), and Lemmas 27 and 60 at slot `s`. -/
theorem lem90_included_update_facts (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H s : ℕ) (B : Block V) (v : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s + 1))) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    (hChain : ConfirmationsChain M S A x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hLocks₀ : ∀ u ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    (hs : x.time i₁ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s) (M.slotStart S.C s) → x.time i₁ < x.time k)
    (hp : S.P.proposer s ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C s)
        (M.supportCutoff S.C (s + 1)) ∧
      S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)))
    -- the honest voters of slots `s - 1` and `s` are active through the sync delay after Lemma 12's read time of
    -- their slot, and the proposer through the sync delay after `M.slotStart S.C s - max (Δ S) Δs`
    --, the amended row `hHoldP`, under)
    (hHold : ∀ s' : ℕ, s ≤ s' + 1 → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hNoCollision : ¬ RootCollisionAtProposal M S A x s B)
    (hv : v ∈ updaterAt M S A x s) :
    (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B ∧
      B ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).fastBlocks ∧
      (∃ e ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).lockEntries,
        M.le_B e = B ∧ M.le_d e = S.C.t_ (s + S.C.k) + 5 * S.C.Δ) ∧
      (∀ e ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).lockEntries,
        M.is_live (x.stateBefore (M.supportCutoff S.C (s + 1)) v)
          ((M.supportCutoff S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B) ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).latestConfirmed = B :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem90_included_update_facts M F U Fx) S A x R
    GST s₀ anchor i₁ H s B v E hNet hSkew hRedeliver Sy hΔs hRoots hParent hAdvQ hSleepK hAnchor
    hGST ht₀ hChain hInv hLocks hLocks₀ hOld hCaches hs hp hHold hHoldP hPropose hNoCollision hv

/-- **The per-validator export of the inclusion, on the chain before slot `s − 1`, with the caches
up to the support cutoff of slot `s + 1`.** In an execution where every time is reached, corruption
is permanent, blocks and Goldfish votes are delivered within `Δ` after `GST` (synchrony from the
receiver's wake, and catch-up on wake), a block reaches a validator only
once it holds the parent, and nobody votes in an honest validator's name; under unforgeability, with
fewer than a quorum of validators ever in the adversary set and committee sleepiness from `anchor`,
at or before `x[i₁].time`; with `GST` at most the vote time of slot `s₀` and the support cutoff of
slot `s₀ + 1` at or before `x[i₁].time`; with every honest attestation sent before the support
cutoff of slot `s₀ + 1` of height at most `H`, and the lock invariant at the healed slot `s₀` itself
(`hLocks₀`: every live lock entry an honest active validator of slot `s₀` keeps after its revocation
of slot `s₀ + 1` is on a block of the honest chain before slot `s₀ + 1` or on an ancestor of one);
with roots naming blocks among what honest validators hold by the support cutoff of slot `s + 1`;
with the updaters' confirmations of the slots from `s₀` to before `s − 1` forming one chain
(`ConfirmationsChainBefore`), the chain invariant and the lock invariant at every slot after `s₀`
and at most `s`, and the caches of every validator honest at a step at a time from `x[i₁].time` to
the support cutoff of slot `s + 1` on the honest chain with justification height greater than `H`:
for a slot `s` starting after `x[i₁].time` whose proposer is awake and honest from the start of the
proposal window of slot `s` to the support cutoff `c` of slot `s + 1`, whose tick at the start of
slot `s` put `B` on the wire, and no block it held before the start of slot `s` having `B`'s root:
every updater `v` of slot `s`, right after `c`, has saved `B` as the confirmation of slot `s`,
holds `B` among its fast blocks and a lock entry on `B` with the deadline of a slot-`s` lock, has
every lock entry it holds that is live at `c` (on its state before `c`) on `B` or an ancestor of
`B`, and has `B` as its confirmed tip.

The landed statement names the answer `A'` of `v`'s update of slot `s + 1` at `c` and equates `v`'s
state right after `c` with it. The twin states the five facts of that state (D-20A1 (e)); its
recovery takes `A'` from the outcome of `v`'s tick at `c` (`update_state_of_duty`) and Lemma 15.

Why: steps 2 to 5 of the inclusion, which read the chain only for blocks on it before slot `s − 1`
(the proposer's root and anchor, the voters' roots, the blocks Lemma 91 (b) to (d) compare), the
invariant and the locks only at slots `s − 1` and `s`, and the caches only up to the update.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `s`: the slot; `B`: the proposal; `v`: the updater.



Why `hHold` and `hHoldP`: the votes of
slot `s - 1` reach the proposer, and the votes of slot `s` reach every updater, by the synchrony condition
`SyncedWithin`, which serves a message only while its holder stays active for `Δs` after the real time it
serves at; the honest committee members of those two slots, and the proposer, are those holders.

Read aloud: with the lock invariant also at the healed slot, and the honest voters of slots `s - 1` and `s`
and the proposer active for the sync delay after the times the synchrony condition reads them, every updater of the slot confirms the
honest proposal fast, locks it, records it, and keeps no live lock off its chain, reading nothing
after the slot's update. -/
theorem lem90_included_update_facts_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H s : ℕ) (B : Block V) (v : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s + 1))) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    (hChain : ConfirmationsChainBefore M S A x s₀ (s - 1))
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor M S A x (honestActiveAt M S A x s')
        (OnHonestChainBefore M S A x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s',
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' u)
    (hLocks₀ : ∀ u ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (hs : x.time i₁ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s) (M.slotStart S.C s) → x.time i₁ < x.time k)
    (hp : S.P.proposer s ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C s)
        (M.supportCutoff S.C (s + 1)) ∧
      S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)))
    -- the honest voters of slots `s - 1` and `s` are active through the sync delay after Lemma 12's read time of
    -- their slot, and the proposer through the sync delay after `M.slotStart S.C s - max (Δ S) Δs`
    --, the amended row `hHoldP`, under)
    (hHold : ∀ s' : ℕ, s ≤ s' + 1 → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hNoCollision : ¬ RootCollisionAtProposal M S A x s B)
    (hv : v ∈ updaterAt M S A x s) :
    (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B ∧
      B ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).fastBlocks ∧
      (∃ e ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).lockEntries,
        M.le_B e = B ∧ M.le_d e = S.C.t_ (s + S.C.k) + 5 * S.C.Δ) ∧
      (∀ e ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).lockEntries,
        M.is_live (x.stateBefore (M.supportCutoff S.C (s + 1)) v)
          ((M.supportCutoff S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B) ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).latestConfirmed = B :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem90_included_update_facts_until M F U Fx) S
    A x R GST s₀ anchor i₁ H s B v E hNet hSkew hRedeliver Sy hΔs hRoots hParent hAdvQ hSleepK
    hAnchor hGST ht₀ hChain hInv hLocks hLocks₀ hOld hCaches hs hp hHold hHoldP hPropose hNoCollision hv

/-- **Lemma 90, inclusion, on the chain before a slot.** In an execution where every time is
reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after `GST`
(synchrony from the receiver's wake, and catch-up on wake), a block reaches a validator only once it
holds the parent, and nobody votes in an honest validator's name; under unforgeability, with fewer
than a quorum of validators ever in the adversary set and committee sleepiness from `anchor`, at or
before `x[i₁].time`; with `GST` at most the vote time of slot `s₀` and the support cutoff of slot
`s₀ + 1` at or before `x[i₁].time`; with every honest attestation sent before the support cutoff of
slot `s₀ + 1` of height at most `H`, and the lock invariant at the healed slot `s₀` itself
(`hLocks₀`: every live lock entry an honest active validator of slot `s₀` keeps after its revocation
of slot `s₀ + 1` is on a block of the honest chain before slot `s₀ + 1` or on an ancestor of one);
with roots naming blocks among what honest validators hold by `t`; with the updaters' confirmations
of the slots whose update some validator ran at a step by `t` (a tick to the support cutoff of the
next slot) forming one chain, the chain
invariant and the lock invariant at every slot after `s₀` whose update is at most `t`, the caches of
every validator honest at a step at a time from `x[i₁].time` to `t` on the honest chain with
justification height greater than `H`, and every validator honest at a step at a time from
`x[i₁].time` to `t` holding as its record a block on the honest chain at a slot whose update it ran
at a tick at an earlier step, which it holds: `ConfirmedIncludedBetween M S Sched x tE t`, the inclusion for the slots
starting at or after `tE` whose update is at most `t`, with the confirmed tips read at steps at
times at most `t`.

Why: steps 1 to 6 of the inclusion at each such slot `q + 2`: the update of slot `q + 2` reads the
chain before slot `q + 1` and the invariant and the locks up to slot `q + 2`; a later step at a
time at most `t`, after the update of a slot `s'`, reads the chain before slot `s' + 1`, the
invariant and the locks up to slot `s'`, and the record and the finalized block right after that
update, both on the chain before slot `s' + 1`; Lemma 90's growth on the chain before a slot
(`lem90_confirmed_monotone_before`) carries the confirmed tip to the step.

Why `htE`: at a slot `s`, the proof reads the proposer's caches and record at its tick to the start
of slot `s`, and `hCaches` and `hLatest` speak only of steps at times at least `x[i₁].time`; so the
slots read are those starting at or after `tE`, each of them starts after `x[i₁].time`, and the
proposer's tick to its start is at a step whose time is at least `x[i₁].time`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold; `t`: the time up to
  which the inclusion is read.
- `tE`: the time from which the slots are read.



Read aloud: for the slots starting at or after `tE`, each of which starts after `x[i₁].time` and
whose proposer ticks to its start at a step whose time is at least `x[i₁].time`, when
the confirmations of the slots updated by `t` form one chain, up to `t` the honest proposer's block
is what every honest active validator of its slot confirms, and stays confirmed, unless the proposer
already held a block with its root. -/
theorem lem90_confirmed_included_before (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H t tE : ℕ)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x t)
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) t)
    (hSleepK : CommitteeSleepinessUntil M S A x anchor t) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    (htE : ∀ s : ℕ, tE ≤ M.slotStart S.C s → x.time i₁ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s) (M.slotStart S.C s) → x.time i₁ < x.time k)
    -- the updaters' confirmations of the slots whose update some validator ran at a step by `t` form one chain
    (hChain : ∀ (σ k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1)) →
        x.time k ≤ t → ConfirmationsChainBefore M S A x s₀ (σ + 1))
    (hInv : ∀ s : ℕ, s₀ < s → M.supportCutoff S.C (s + 1) ≤ t →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → M.supportCutoff S.C (s + 1) ≤ t → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hLocks₀ : ∀ u ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- at every slot whose next slot starts at or after `tE` and whose update is at most `t`, the honest active
    -- committee members are active through the sync delay after Lemma 12's read time of the slot; at every slot of
    -- the window with an honest opener, its proposer through the sync delay after one delay or one sync delay before
    -- its start
    (hHold : ∀ s' : ℕ, tE ≤ M.slotStart S.C (s' + 1) → M.supportCutoff S.C (s' + 1) ≤ t →
      ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : ∀ s : ℕ, tE ≤ M.slotStart S.C s → M.supportCutoff S.C (s + 1) ≤ t → HonestOpenerAt M S A x s →
      S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
        (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ t →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st (j + 1) u))
    (hLatest : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ t →
      u ∉ A.corrupted j → (∃ σ : ℕ, x.lbl (x.tickStep u (M.supportCutoff S.C (σ + 1))) = Event.tick u (M.supportCutoff S.C (σ + 1)) ∧ x.tickStep u (M.supportCutoff S.C (σ + 1)) < j + 1 ∧
        OnHonestChainAt M S A x s₀ σ (x.st (j + 1) u).latestConfirmed) ∧
        (x.st (j + 1) u).latestConfirmed ∈ (x.st (j + 1) u).tree)
    : ConfirmedIncludedBetween M S A x tE t :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem90_confirmed_included_before M F U Fx) S A
    x R GST s₀ anchor i₁ H t tE E hNet hSkew hRedeliver Sy hΔs hRoots hParent hAdvQ hSleepK hAnchor
    hGST ht₀ htE hChain hInv hLocks hLocks₀ hOld hHold hHoldP hCaches hLatest

/-- **The lock invariant at the healed slot, from Lemma 81's premises.** In an execution where every
time is reached and corruption is permanent: when committee sleepiness holds from `anchor`, at or
before the start of slot `s₀ + 1`; `B₀`'s slot is at least `s₀`; `HonestChainExtends` holds for `B₀`
at slot `s₀` at the honest active validators of slot `s₀`; and every updater of slot `s₀` saves `B₀`
— then every honest active validator `u` of slot `s₀` satisfies the lock invariant at slot `s₀` for
the honest chain before slot `s₀ + 1`. This is the discharge of the `hLocks₀` of
`lem90_included_update_facts` and `lem90_confirmed_included`.

Why: `liveLocksOnFamilyAt_base` puts every live entry on `B₀` or an ancestor of it, and `B₀` is on
the honest chain at slot `s₀`: some honest committee member of slot `s₀` is an updater that saved
it.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `anchor`: the
  time from which committee sleepiness holds; `B₀`: the healed block; `u`: the validator.

Read aloud: at the healed slot, every honest active validator's live locks are on the chain.

 -/
theorem base_locks_on_chain (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ anchor : ℕ) (B₀ : Block V) (u : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s₀ + 1))) (hAnchor : anchor ≤ M.slotStart S.C (s₀ + 1))
    (hB₀slot : s₀ ≤ B₀.slot)
    (hBase : HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀)
    (hBaseSaved : ∀ v ∈ updaterAt M S A x s₀,
      (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀)
    (hu : u ∈ honestActiveAt M S A x s₀) :
    LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ u :=
  (GoldilocksCorrectness.Record.Proofs.Executions.base_locks_on_chain M F U) S A x R s₀ anchor B₀
    u E hSleepK hAnchor hB₀slot hBase hBaseSaved hu

end GoldilocksCorrectness.Record.Statements.Executions

