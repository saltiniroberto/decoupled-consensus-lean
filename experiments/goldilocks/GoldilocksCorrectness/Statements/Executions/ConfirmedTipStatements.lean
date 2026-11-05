module
public import GoldilocksCorrectness.Proofs.Routines.ConfirmedTip
public import GoldilocksCorrectness.Proofs.Executions.Lemma90
public import GoldilocksCorrectness.Proofs.Executions.Lemma90Inclusion
public import GoldilocksCorrectness.Statements.Routines.ConfirmationStatements

@[expose] public section

/-!
# The confirmed tip after the healed slot

The audited statements about the record of the confirmed tip and the confirmed tip after the
healed slot:

- three routine facts, proved in `GoldilocksCorrectness/Proofs/Routines/ConfirmedTip.lean`:
  `advance_cases`, `ac_confirmed_cases` and `update_confirmation_latest_confirmed`;
- `lem90a_latest_confirmed_honest`, after the update of the healed slot the record of every honest
  validator is an honest confirmation it holds, and Lemma 90's two parts,
  `lem90_confirmed_agree` and `lem90_confirmed_monotone`, the agreement and the growth of the
  confirmed tip, proved in `GoldilocksCorrectness/Proofs/Executions/Lemma90.lean`.

The definitions they read are in `ConfirmedTipDefs.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff
  proposalWindowStart)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## The routine facts -/

/-! ## The record after the healed slot -/

/-- **The record after the healed round is an honest confirmation.** In an execution where every
time is reached and corruption is permanent: if `B₀`'s slot is at
least `s₀`; `HonestChainExtends` holds for `B₀` at slot `s₀` at the honest active validators of
slot `s₀`; every updater of slot `s₀` holds `B₀` as its confirmation of slot `s₀` right after the
support cutoff of slot `s₀ + 1`; and every validator outside the adversary set at that support
cutoff is an updater of slot `s₀` — then at every step at a time after that support cutoff, every
validator outside the adversary set at the step's time has as its record of the confirmed tip an
honest confirmation from slot `s₀`, which it holds.

Why: by induction on the steps. Right after the update of slot `s₀`, the record is `B₀`: no live
lock vetoes `B₀` (the second clause of `HonestChainExtends`, or, for an updater not active at
slot `s₀`, no lock live at the vote time of slot `s₀ + 1`), and `advance` keeps an old record only
when `B₀` is its ancestor or itself, while the old record's slot is at most `s₀`. Afterwards the
record changes only at the validator's own updates, to the confirmation it saves, an honest
confirmation of a later slot. `hB₀slot` is the one hypothesis beyond the plan's signature: without
it, an old record that is a strict descendant of `B₀` could be kept by `advance`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `B₀`: the block every updater of slot `s₀` saved.

Read aloud: after the healed round's action time, the record of the confirmed tip of every
validator honest at the step is an honest confirmation, and the validator holds it. -/
theorem lem90a_latest_confirmed_honest (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ : ℕ) (B₀ : Block V)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- `B₀`'s slot is at least `s₀`
    (hB₀slot : s₀ ≤ B₀.slot)
    -- the slot invariant restricted to `B₀` at slot `s₀`
    (hBase : HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀)
    -- every updater of slot `s₀` saved `B₀`
    (hBaseSaved : ∀ v ∈ updaterAt S Sched s₀,
      (stateBefore x (supportCutoff S (s₀ + 1) + 1) v).A.saved_confirmation s₀ = some B₀)
    -- every validator honest at the support cutoff of slot `s₀ + 1` is an updater of slot `s₀`
    (hAwake : ∀ v : V, v ∉ Sched.adv ((supportCutoff S (s₀ + 1) : ℕ) : Int) →
      v ∈ updaterAt S Sched s₀) :
    -- then after that cutoff every honest record is an honest confirmation held in the tree
    ∀ (i : ℕ) (v : V), supportCutoff S (s₀ + 1) < x[i].time → v ∉ Sched.adv (x[i].time : Int) →
      IsHonestConfirmation S Sched x s₀ (x[i][v].st).A.latest_confirmed ∧
        (x[i][v].st).A.latest_confirmed ∈ (x[i][v].st).S.T :=
  GoldilocksCorrectness.Proofs.Executions.lem90a_latest_confirmed_honest S Sched x s₀ B₀ hDiv
    hMono hB₀slot hBase hBaseSaved hAwake

/-- **`lem90a_latest_confirmed_honest_at`, the record after the healed round is an honest
confirmation of a slot whose update ran by then.** In an execution where every time is reached
and corruption is permanent: when `B₀`'s slot is at
least `s₀`, `HonestChainExtends` holds for `B₀` at slot `s₀` at the honest active validators of
slot `s₀`, every updater of slot `s₀` holds `B₀` as its confirmation of slot `s₀` right after the
support cutoff of slot `s₀ + 1`, and every validator outside the adversary set at that support
cutoff is an updater of slot `s₀` — then at every step at a time after that support cutoff, every
validator outside the adversary set at the step's time has as its record of the confirmed tip the
confirmation of some slot `s ≥ s₀` that an updater of slot `s` holds right after the support
cutoff of slot `s + 1`, that support cutoff being at most the time of the step, and the validator
holds its record.

Why: `lem90a_latest_confirmed_honest`'s induction, with the slot of the record kept: right after the
update of slot `s₀` the record is `B₀`, the confirmation of slot `s₀`; afterwards the record changes
only at the validator's own update of a slot `s + 1`, at the support cutoff of slot `s + 1`, to the
confirmation of slot `s` it saves.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `B₀`: the block every updater of slot `s₀` saved.



Read aloud: after the healed round's action time, the record of the confirmed tip of every
validator honest at the step is an honest confirmation of a slot whose update ran by then, and the
validator holds it. -/
theorem lem90a_latest_confirmed_honest_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ : ℕ) (B₀ : Block V)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- `B₀`'s slot is at least `s₀`
    (hB₀slot : s₀ ≤ B₀.slot)
    -- the slot invariant restricted to `B₀` at slot `s₀`
    (hBase : HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀)
    -- every updater of slot `s₀` saved `B₀`
    (hBaseSaved : ∀ v ∈ updaterAt S Sched s₀,
      (stateBefore x (supportCutoff S (s₀ + 1) + 1) v).A.saved_confirmation s₀ = some B₀)
    -- every validator honest at the support cutoff of slot `s₀ + 1` is an updater of slot `s₀`
    (hAwake : ∀ v : V, v ∉ Sched.adv ((supportCutoff S (s₀ + 1) : ℕ) : Int) →
      v ∈ updaterAt S Sched s₀) :
    ∀ (i : ℕ) (v : V), supportCutoff S (s₀ + 1) < x[i].time → v ∉ Sched.adv (x[i].time : Int) →
      (∃ s : ℕ, s₀ ≤ s ∧ supportCutoff S (s + 1) ≤ x[i].time ∧ ∃ u ∈ updaterAt S Sched s,
        (stateBefore x (supportCutoff S (s + 1) + 1) u).A.saved_confirmation s =
          some (x[i][v].st).A.latest_confirmed) ∧
        (x[i][v].st).A.latest_confirmed ∈ (x[i][v].st).S.T :=
  GoldilocksCorrectness.Proofs.Executions.lem90a_latest_confirmed_honest_at S Sched x s₀ B₀ hDiv
    hMono hB₀slot hBase hBaseSaved hAwake

/-! ## Lemma 90 -/

/-- **Lemma 90, agreement: the confirmed tips of honest validators agree after the healed
round.** When the honest confirmations form a chain from slot `s₀`, and at every step at a time
at least that of step `i₁`, every validator outside the adversary set at the step's time has an
honest confirmation from slot `s₀` as its record and its caches on the honest chain with the
threshold `H`, then `ConfirmedAgreeAfterHealing S Sched x (x[i₁].time)` holds.

Why: each confirmed tip is its node state's record, an honest confirmation, or its finalized
block, an ancestor of a justified block on the honest chain or that block; so both are on the
honest chain, and two blocks on it are compatible (`onHonestChain_compatible`). The step condition
of the two hypotheses is a time condition, `x[i₁].time ≤ x[i].time`, where the plan's signature
had `i₁ ≤ i`: the conclusion reads every step at a time at least `x[i₁].time`, including steps
before `i₁` at that same time. Lemma 84's conclusion, stated for `i₁ ≤ i`, supplies it when `i₁`
is the first step at its time, `stepBefore x t + 1` (`stepBefore_succ_le_of_time_le`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `H`: the threshold of the caches; `i₁`: the step from whose time the facts hold.

Read aloud: from the phase's end, the confirmed tips of two validators honest at their steps are
compatible. -/
theorem lem90_confirmed_agree (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ H i₁ : ℕ)
    -- the honest confirmations form a chain from slot `s₀`
    (hChain : ConfirmationsChain S Sched x s₀)
    -- from the time of step `i₁` on, an honest validator's record is an honest confirmation
    (hLatest : ∀ (i : ℕ) (v : V), x[i₁].time ≤ x[i].time → v ∉ Sched.adv (x[i].time : Int) →
      IsHonestConfirmation S Sched x s₀ (x[i][v].st).A.latest_confirmed)
    -- from the time of step `i₁` on, an honest validator's caches are on the honest chain
    (hCaches : ∀ (i : ℕ) (v : V), x[i₁].time ≤ x[i].time → v ∉ Sched.adv (x[i].time : Int) →
      CachesOnChain S Sched x s₀ H (x[i][v].st)) :
    ConfirmedAgreeAfterHealing S Sched x (x[i₁].time) :=
  GoldilocksCorrectness.Proofs.Executions.lem90_confirmed_agree S Sched x s₀ H i₁ hChain hLatest
    hCaches

/-- **Lemma 90, growth: the confirmed tip of an honest validator only extends after the healed
round.** When the honest confirmations form a chain from slot `s₀`, and at every step at a time
at least that of step `i₁`, every validator outside the adversary set at the step's time has an
honest confirmation from slot `s₀` as its record, holds it, and has its caches on the honest
chain with the threshold `H`, then `ConfirmedMonotoneAfterHealing S Sched x (x[i₁].time)` holds.

Why: step by step. The finalized block only moves to a descendant; the record changes only at the
validator's update, to the saved confirmation `C'` when `advance` does not keep the old record;
the two, both on the honest chain, are compatible, and when `C'` is an ancestor of the old record,
`advance` not keeping it means the old record is not in the frame's tree, hence an ancestor of the
finalized block. Either way the old record is an ancestor of the new record or of the new
finalized block, and the new confirmed tip is a descendant of both. The plan's `hMono` is deleted:
`HonestThrough` at the later step gives the honesty at every earlier step. The step condition of
the two hypotheses is the time condition of `lem90_confirmed_agree`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `H`: the threshold of the caches; `i₁`: the step from whose time the facts hold.

Read aloud: from the phase's end, the confirmed tip of a validator honest through the later of two
steps only extends. -/
theorem lem90_confirmed_monotone (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ H i₁ : ℕ)
    -- the honest confirmations form a chain from slot `s₀`
    (hChain : ConfirmationsChain S Sched x s₀)
    -- from the time of step `i₁` on, an honest validator's record is an honest confirmation it
    -- holds
    (hLatest : ∀ (i : ℕ) (v : V), x[i₁].time ≤ x[i].time → v ∉ Sched.adv (x[i].time : Int) →
      IsHonestConfirmation S Sched x s₀ (x[i][v].st).A.latest_confirmed ∧
        (x[i][v].st).A.latest_confirmed ∈ (x[i][v].st).S.T)
    -- from the time of step `i₁` on, an honest validator's caches are on the honest chain
    (hCaches : ∀ (i : ℕ) (v : V), x[i₁].time ≤ x[i].time → v ∉ Sched.adv (x[i].time : Int) →
      CachesOnChain S Sched x s₀ H (x[i][v].st)) :
    ConfirmedMonotoneAfterHealing S Sched x (x[i₁].time) :=
  GoldilocksCorrectness.Proofs.Executions.lem90_confirmed_monotone S Sched x s₀ H i₁ hChain
    hLatest hCaches

/-- **Lemma 90, agreement, read up to a time `t`, with the caches up to `t`.** When the honest
confirmations form a chain from slot `s₀`, and at every step at a time at least that of step `i₁`
every validator outside the adversary set at the step's time has an honest confirmation from slot
`s₀` as its record, and at every step at a time from that of step `i₁` to `t` its caches on the
honest chain with the threshold `H`: `ConfirmedAgreeBetween S Sched x (x[i₁].time) t`, the
confirmed tips of two validators honest through their steps, at times from `x[i₁].time` to `t`,
are compatible.

Why: `lem90_confirmed_agree`'s proof, which reads the caches at the two steps compared only.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `H`: the threshold of the caches; `i₁`: the step from whose time the facts hold; `t`: the time
  up to which the confirmed tips are read.

Caches up to `t`.

Read aloud: from the phase's end to `t`, the confirmed tips of two validators honest at their steps
are compatible. -/
theorem lem90_confirmed_agree_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ H i₁ t : ℕ)
    -- the honest confirmations form a chain from slot `s₀`
    (hChain : ConfirmationsChain S Sched x s₀)
    -- from the time of step `i₁` on, an honest validator's record is an honest confirmation
    (hLatest : ∀ (i : ℕ) (v : V), x[i₁].time ≤ x[i].time → v ∉ Sched.adv (x[i].time : Int) →
      IsHonestConfirmation S Sched x s₀ (x[i][v].st).A.latest_confirmed)
    -- from the time of step `i₁` to `t`, an honest validator's caches are on the honest chain
    (hCaches : ∀ (i : ℕ) (v : V), x[i₁].time ≤ x[i].time → x[i].time ≤ t →
      v ∉ Sched.adv (x[i].time : Int) → CachesOnChain S Sched x s₀ H (x[i][v].st)) :
    ConfirmedAgreeBetween S Sched x (x[i₁].time) t :=
  GoldilocksCorrectness.Proofs.Executions.lem90_confirmed_agree_until S Sched x s₀ H i₁ t hChain
    hLatest hCaches

/-- **Lemma 90, growth, read up to a time `t`, with the caches up to `t`.** When the honest
confirmations form a chain from slot `s₀`, and at every step at a time at least that of step `i₁`
every validator outside the adversary set at the step's time has an honest confirmation from slot
`s₀` as its record and holds it, and at every step at a time from that of step `i₁` to `t` its
caches on the honest chain with the threshold `H`: `ConfirmedMonotoneBetween S Sched x (x[i₁].time)
t`, the confirmed tip of a validator honest through the later of two steps, the later at a time at
most `t`, only extends.

Why: `lem90_confirmed_monotone`'s induction, which reads the caches at the steps up to the later
one only.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `H`: the threshold of the caches; `i₁`: the step from whose time the facts hold; `t`: the time
  up to which the later confirmed tip is read.

Caches up to `t`.

Read aloud: from the phase's end to `t`, the confirmed tip of a validator honest through the later
of two steps only extends. -/
theorem lem90_confirmed_monotone_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ H i₁ t : ℕ)
    -- the honest confirmations form a chain from slot `s₀`
    (hChain : ConfirmationsChain S Sched x s₀)
    -- from the time of step `i₁` on, an honest validator's record is an honest confirmation it
    -- holds
    (hLatest : ∀ (i : ℕ) (v : V), x[i₁].time ≤ x[i].time → v ∉ Sched.adv (x[i].time : Int) →
      IsHonestConfirmation S Sched x s₀ (x[i][v].st).A.latest_confirmed ∧
        (x[i][v].st).A.latest_confirmed ∈ (x[i][v].st).S.T)
    -- from the time of step `i₁` to `t`, an honest validator's caches are on the honest chain
    (hCaches : ∀ (i : ℕ) (v : V), x[i₁].time ≤ x[i].time → x[i].time ≤ t →
      v ∉ Sched.adv (x[i].time : Int) → CachesOnChain S Sched x s₀ H (x[i][v].st)) :
    ConfirmedMonotoneBetween S Sched x (x[i₁].time) t :=
  GoldilocksCorrectness.Proofs.Executions.lem90_confirmed_monotone_until S Sched x s₀ H i₁ t hChain
    hLatest hCaches

/-- **Lemma 90, agreement, on the chain before a slot.** In an execution where every time is reached
and corruption is permanent, under unforgeability, with fewer than a quorum of validators ever in
the adversary set, every honest attestation sent before the support cutoff of slot `s₀ + 1` of
height at most `H`, and roots naming blocks among what honest validators hold by `t`: when the
updaters' confirmations of the slots whose update, the support cutoff of the next slot, is at most
`t` form one chain from slot `s₀` (`ConfirmationsChainBefore`), and at every step at a time from
`x[i₁].time` to `t` every validator outside the adversary set at the step's time has as its record a
block on the honest chain at a slot whose next slot's support cutoff is at most the step's time, and
its caches on the honest chain with the threshold `H`:
`ConfirmedAgreeBetween S Sched x (x[i₁].time) t`, the confirmed tips of two validators honest
through their steps, at times from `x[i₁].time` to `t`, are compatible.

Why: each confirmed tip is the record or the finalized block; the finalized block is the justified
block or an ancestor of it, and the justified block, above the threshold, is on the honest chain at
a slot whose update ran by the step (Lemmas 66 and 83, the roots premise); so both tips are on the
chain at slots whose update is at most `t`, and two such blocks are compatible
(`ConfirmationsChainBefore` at the slot after the later one).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `H`: the threshold of the caches; `i₁`: the step from whose time the facts hold; `t`: the time
  up to which the confirmed tips are read.



Read aloud: when the confirmations of the slots updated by `t` form one chain, from the phase's end
to `t` the confirmed tips of two validators honest at their steps are compatible. -/
theorem lem90_confirmed_agree_before (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ H i₁ t : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x t) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    -- the updaters' confirmations of the slots whose update is at most `t` form one chain
    (hChain : ∀ σ : ℕ, supportCutoff S (σ + 1) ≤ t → ConfirmationsChainBefore S Sched x s₀ (σ + 1))
    -- from the time of step `i₁` to `t`, an honest validator's record is on the honest chain at a
    -- slot whose update ran by then
    (hLatest : ∀ (i : ℕ) (v : V), x[i₁].time ≤ x[i].time → x[i].time ≤ t →
      v ∉ Sched.adv (x[i].time : Int) → ∃ σ : ℕ, supportCutoff S (σ + 1) ≤ x[i].time ∧
        OnHonestChainAt S Sched x s₀ σ (x[i][v].st).A.latest_confirmed)
    -- from the time of step `i₁` to `t`, an honest validator's caches are on the honest chain
    (hCaches : ∀ (i : ℕ) (v : V), x[i₁].time ≤ x[i].time → x[i].time ≤ t →
      v ∉ Sched.adv (x[i].time : Int) → CachesOnChain S Sched x s₀ H (x[i][v].st)) :
    ConfirmedAgreeBetween S Sched x (x[i₁].time) t :=
  GoldilocksCorrectness.Proofs.Executions.lem90_confirmed_agree_before S Sched x s₀ H i₁ t hDiv
    hMono hRoots hU hAdvQ hOld hChain hLatest hCaches

/-- **Lemma 90, growth, on the chain before a slot.** In an execution where every time is reached
and corruption is permanent, under unforgeability, with fewer than a quorum of validators ever in
the adversary set, every honest attestation sent before the support cutoff of slot `s₀ + 1` of
height at most `H`, and roots naming blocks among what honest validators hold by `t`: when the
updaters' confirmations of the slots whose update, the support cutoff of the next slot, is at most
`t` form one chain from slot `s₀` (`ConfirmationsChainBefore`), and at every step at a time from
`x[i₁].time` to `t` every validator outside the adversary set at the step's time has as its record a
block on the honest chain at a slot whose next slot's support cutoff is at most the step's time,
which it holds, and its caches on the honest chain with the threshold `H`:
`ConfirmedMonotoneBetween S Sched x (x[i₁].time) t`, the confirmed tip of a validator honest through
the later of two steps, the later at a time at most `t`, only extends.

Why: by induction on the later step: at each step the records and the finalized blocks at the two
steps are on the honest chain at slots whose update is at most `t` (the finalized block through the
justified block, Lemmas 66 and 83), so compatible, and the step lemma of Lemma 90's growth
(`confirmedOf_step_of_compatible`) reads only these compatibilities.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `H`: the threshold of the caches; `i₁`: the step from whose time the facts hold; `t`: the time
  up to which the later confirmed tip is read.



Read aloud: when the confirmations of the slots updated by `t` form one chain, from the phase's end
to `t` the confirmed tip of a validator honest through the later of two steps only extends. -/
theorem lem90_confirmed_monotone_before (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ H i₁ t : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x t) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    -- the updaters' confirmations of the slots whose update is at most `t` form one chain
    (hChain : ∀ σ : ℕ, supportCutoff S (σ + 1) ≤ t → ConfirmationsChainBefore S Sched x s₀ (σ + 1))
    -- from the time of step `i₁` to `t`, an honest validator's record is on the honest chain at a
    -- slot whose update ran by then, and it holds it
    (hLatest : ∀ (i : ℕ) (v : V), x[i₁].time ≤ x[i].time → x[i].time ≤ t →
      v ∉ Sched.adv (x[i].time : Int) → (∃ σ : ℕ, supportCutoff S (σ + 1) ≤ x[i].time ∧
        OnHonestChainAt S Sched x s₀ σ (x[i][v].st).A.latest_confirmed) ∧
        (x[i][v].st).A.latest_confirmed ∈ (x[i][v].st).S.T)
    -- from the time of step `i₁` to `t`, an honest validator's caches are on the honest chain
    (hCaches : ∀ (i : ℕ) (v : V), x[i₁].time ≤ x[i].time → x[i].time ≤ t →
      v ∉ Sched.adv (x[i].time : Int) → CachesOnChain S Sched x s₀ H (x[i][v].st)) :
    ConfirmedMonotoneBetween S Sched x (x[i₁].time) t :=
  GoldilocksCorrectness.Proofs.Executions.lem90_confirmed_monotone_before S Sched x s₀ H i₁ t hDiv
    hMono hRoots hU hAdvQ hOld hChain hLatest hCaches

/-! ## Lemma 90, inclusion

The inclusion of the honest proposal after healing, proved in
`GoldilocksCorrectness/Proofs/Executions/Lemma90Inclusion.lean`: the per-validator export
`lem90_included_update_facts`, the inclusion `lem90_confirmed_included`, both with the lock invariant
at the healed slot (`hLocks₀`), the inclusion read up to a time `t`,
`lem90_confirmed_included_until`, of which `lem90_confirmed_included` is the instance at
every time, and the lock invariant's discharge, `base_locks_on_chain`. -/

open Framework.StsMultisetLog (AtomicAction SignedMsg)
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
every updater `v` of slot `s` runs the update of slot `s + 1` at `c` with some answer `A'`, which
saves `B` as the confirmation of slot `s`, has `B` among its fast blocks and the lock entry on `B`
with the deadline of a slot-`s` lock, keeps every lock entry live at `c` on `B` or an ancestor of
`B`, and records `B` as the confirmed tip; and `v`'s state right after `c` has `A'`'s saved
confirmations, fast blocks, lock entries and record.

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

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `s`: the slot; `B`: the proposal; `v`: the updater.

Read aloud: with the lock invariant also at the healed slot, every updater of the slot confirms the
honest proposal fast, locks it, records it, and keeps no live lock off its chain.



Roots name blocks until `supportCutoff S (s + 1)`: the proof reads, at slot `s`, the proposer's
and the voters' fork-choice roots up to the vote time of slot `s` and the updaters' up to the
support cutoff of slot `s + 1` (Lemma 91 (f)), and Lemmas 27 and 60 at slot `s`. -/
theorem lem90_included_update_facts (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H s : ℕ) (B : Block V) (v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (hChain : ConfirmationsChain S Sched x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hLocks₀ : ∀ u ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ u)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hs : x[i₁].time < slotStart S s)
    (hp : ∀ t : ℕ, proposalWindowStart S s ≤ t → t ≤ supportCutoff S (s + 1) →
      S.P.proposer s ∈ Sched.awake (t : Int) ∧ S.P.proposer s ∉ Sched.adv (t : Int))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hNoCollision : ¬ RootCollisionAtProposal S Sched x s B)
    (hv : v ∈ updaterAt S Sched s) :
    ∃ A' : ACState V,
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A' ∧
      A'.saved_confirmation s = some B ∧
      B ∈ A'.fast_blocks ∧
      LockEntry.mk B (S.C.t_ (s + S.C.k) + 5 * S.C.Δ) ∈ A'.lock_entries ∧
      (∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
          ((supportCutoff S (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B) ∧
      A'.latest_confirmed = B ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation =
        A'.saved_confirmation ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.fast_blocks = A'.fast_blocks ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.lock_entries = A'.lock_entries ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.latest_confirmed =
        A'.latest_confirmed :=
  GoldilocksCorrectness.Proofs.Executions.lem90_included_update_facts S Sched x GST s₀
    anchor i₁ H s B v hDiv hMono hSync hCatch hRoots hParent hOwner hU hAdvQ hSleepK hAnchor
    hGST ht₀ hChain hInv hLocks hLocks₀ hOld hCaches hs hp hPropose hNoCollision hv

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
every updater `v` of slot `s` runs the update of slot `s + 1` at `c` with some answer `A'`, which
saves `B` as the confirmation of slot `s`, has `B` among its fast blocks and the lock entry on `B`
with the deadline of a slot-`s` lock, keeps every lock entry live at `c` on `B` or an ancestor of
`B`, and records `B` as the confirmed tip; and `v`'s state right after `c` has `A'`'s saved
confirmations, fast blocks, lock entries and record.

Why: steps 2 to 5 of the inclusion, which read the chain only for blocks on it before slot `s − 1`
(the proposer's root and anchor, the voters' roots, the blocks Lemma 91 (b) to (d) compare), the
invariant and the locks only at slots `s − 1` and `s`, and the caches only up to the update.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `s`: the slot; `B`: the proposal; `v`: the updater.



Read aloud: with the lock invariant also at the healed slot, every updater of the slot confirms the
honest proposal fast, locks it, records it, and keeps no live lock off its chain, reading nothing
after the slot's update. -/
theorem lem90_included_update_facts_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H s : ℕ) (B : Block V) (v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (hChain : ConfirmationsChainBefore S Sched x s₀ (s - 1))
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor S Sched x (honestActiveAt S Sched s') (OnHonestChainBefore S Sched x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ u ∈ honestActiveAt S Sched s',
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s') s' u)
    (hLocks₀ : ∀ u ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ u)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ supportCutoff S (s + 1) →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hs : x[i₁].time < slotStart S s)
    (hp : ∀ t : ℕ, proposalWindowStart S s ≤ t → t ≤ supportCutoff S (s + 1) →
      S.P.proposer s ∈ Sched.awake (t : Int) ∧ S.P.proposer s ∉ Sched.adv (t : Int))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hNoCollision : ¬ RootCollisionAtProposal S Sched x s B)
    (hv : v ∈ updaterAt S Sched s) :
    ∃ A' : ACState V,
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A' ∧
      A'.saved_confirmation s = some B ∧
      B ∈ A'.fast_blocks ∧
      LockEntry.mk B (S.C.t_ (s + S.C.k) + 5 * S.C.Δ) ∈ A'.lock_entries ∧
      (∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
          ((supportCutoff S (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B) ∧
      A'.latest_confirmed = B ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation =
        A'.saved_confirmation ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.fast_blocks = A'.fast_blocks ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.lock_entries = A'.lock_entries ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.latest_confirmed =
        A'.latest_confirmed :=
  GoldilocksCorrectness.Proofs.Executions.lem90_included_update_facts_until S Sched x GST s₀ anchor
    i₁ H s B v hDiv hMono hSync hCatch hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST
    ht₀ hChain hInv hLocks hLocks₀ hOld hCaches hs hp hPropose hNoCollision hv

/-- **Lemma 90, inclusion, `lem90_confirmed_included`.** In an execution where every time is
reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after `GST`
(synchrony from the receiver's wake, and catch-up on wake), a root names
one block among what honest validators hold, a block reaches a validator only once it holds the
parent, and nobody votes in an honest validator's name; under unforgeability, with fewer than a
quorum of validators ever in the adversary set (Lemma 87) and committee sleepiness from `anchor`, at
or before `x[i₁].time`; with `GST` at most the vote time of slot `s₀` and the support cutoff of slot `s₀ + 1` at or before `x[i₁].time`; with the honest
confirmations forming a chain from slot `s₀` (Lemma 81), the chain invariant and the lock invariant
at every slot after `s₀` (`lem81_inv`), the lock invariant at the healed slot `s₀` itself
(`hLocks₀`: every live lock entry an honest active validator of slot `s₀` keeps after its
revocation of slot `s₀ + 1` is on a block of the honest chain before slot `s₀ + 1` or on an
ancestor of one), every honest attestation sent before the support cutoff of slot `s₀ + 1` of
height at most `H` (Lemma 89), and the caches of every validator honest at a step at a time at least
`x[i₁].time` on the honest chain with justification height greater than `H` (Lemma 84), and with
every validator honest at a step at a time at least `x[i₁].time` holding an honest confirmation as
its record (`lem90a`): `ConfirmedIncludedAfterHealing S Sched x tE`. No hypothesis reads
the state of an honest validator beyond these conclusions of Lemmas 81, 84, 89 and `lem90a`, and
the lock invariant at `s₀`.

Why: steps 1 to 6 of the inclusion: the proposer
proposes; the proposal's parent extends the chain; every honest vote names the proposal; every
updater saves, records and holds it as its confirmed tip; and each later update of an honest active
validator saves a descendant of it, so the confirmed tip only grows from it (Lemma 90, growth).

Why `hLocks₀`: the route reads the proposer's anchor at the start of slot `s = s₀ + 2`. The anchor
is the root of the proposer's fork choice or a block a live lock entry of the proposer locks, and an
entry left by the proposer's revocation of slot `s₀ + 1` may have been added by an update of a slot
before `s₀`. `hLocks` speaks of slots after `s₀` only, and nothing else in the hypotheses places
such an entry's block on the honest chain; without `hLocks₀` the proposal of slot `s₀ + 2` could
extend a block off the chain and lose the votes. `base_locks_on_chain` derives `hLocks₀` from
Lemma 81's own premises (`HonestChainExtends` at `s₀`, the updaters' saved `B₀`, committee
sleepiness).

The statement of record.

Why `htE`: at a slot `s`, the proof reads the proposer's caches
and record at the step before the start of slot `s`, and `hCaches` and `hLatest` speak only of steps
at times at least `x[i₁].time`; so the slots read are those starting at or after `tE`, and each of
them starts after `x[i₁].time`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold.
- `tE`: the time from which the slots are read.

Read aloud: for the slots starting at or after `tE`, each of which starts after `x[i₁].time`, with
the lock invariant also at the healed slot, the honest proposer's block is what every honest active
validator of its slot confirms, and stays confirmed, unless the proposer already held a block with
its root.

 -/
theorem lem90_confirmed_included (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H tE : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocks S Sched x)
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (htE : ∀ s : ℕ, tE ≤ slotStart S s → x[i₁].time < slotStart S s)
    (hChain : ConfirmationsChain S Sched x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hLocks₀ : ∀ u ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ u)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hLatest : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      IsHonestConfirmation S Sched x s₀ (x[j][u].st).A.latest_confirmed ∧
        (x[j][u].st).A.latest_confirmed ∈ (x[j][u].st).S.T)
    : ConfirmedIncludedAfterHealing S Sched x tE :=
  GoldilocksCorrectness.Proofs.Executions.lem90_confirmed_included S Sched x GST s₀
    anchor i₁ H tE hDiv hMono hSync hCatch hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST
    ht₀ htE hChain hInv hLocks hLocks₀ hOld hCaches hLatest

/-- **Lemma 90, inclusion, read up to a time `t`, `lem90_confirmed_included_until`**. In
an execution where every time is reached, corruption is permanent, blocks and Goldfish votes are
delivered within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake), roots
name blocks among what honest validators hold up to the time `t`
(`RootsNameBlocksUntil S Sched x t`), a block reaches a validator only once it holds the parent, and
nobody votes in an honest validator's name; under unforgeability, with fewer than a quorum of
validators ever in the adversary set (Lemma 87) and committee sleepiness from `anchor`, at or before
`x[i₁].time`; with `GST` at most the vote time of slot `s₀` and the support cutoff of slot `s₀ + 1` at or before `x[i₁].time`; with the honest
confirmations forming a chain from slot `s₀` (Lemma 81), the chain invariant and the lock invariant
at every slot after `s₀` (`lem81_inv`), the lock invariant at the healed slot `s₀` itself
(`hLocks₀`: every live lock entry an honest active validator of slot `s₀` keeps after its revocation
of slot `s₀ + 1` is on a block of the honest chain before slot `s₀ + 1` or on an ancestor of one),
every honest attestation sent before the support cutoff of slot `s₀ + 1` of height at most `H`
(Lemma 89), and the caches of every validator honest at a step at a time at least `x[i₁].time` on
the honest chain with justification height greater than `H` (Lemma 84), and with every validator
honest at a step at a time at least `x[i₁].time` holding an honest confirmation as its record
(`lem90a`): `ConfirmedIncludedBetween S Sched x tE t`, the inclusion for the slots starting at or
after `tE` whose update, the support cutoff of the next slot, is at most `t`, with the confirmed
tips read at steps at times at most `t`.

Why: `lem90_confirmed_included`'s proof, which at each slot reads blocks held up to the update of a
slot whose support cutoff is before the step read; with the step at a time at most `t`, every
reading is at most `t`. `lem90_confirmed_included` is this at every time `t`
(`confirmedIncludedAfterHealing_iff`).

Why `htE`: at a slot `s`, the proof reads the proposer's caches
and record at the step before the start of slot `s`, and `hCaches` and `hLatest` speak only of steps
at times at least `x[i₁].time`; so the slots read are those starting at or after `tE`, and each of
them starts after `x[i₁].time`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold; `t`: the time up to
  which roots name blocks and the inclusion is read.
- `tE`: the time from which the slots are read.

Read aloud: for the slots starting at or after `tE`, each of which starts after `x[i₁].time`, when
roots name blocks up to `t`, then up to `t` the honest proposer's block is what every honest active
validator of its slot confirms, and stays confirmed, unless the proposer already held a block with
its root.

 -/
theorem lem90_confirmed_included_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H t tE : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x t)
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (htE : ∀ s : ℕ, tE ≤ slotStart S s → x[i₁].time < slotStart S s)
    (hChain : ConfirmationsChain S Sched x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hLocks₀ : ∀ u ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ u)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hLatest : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      IsHonestConfirmation S Sched x s₀ (x[j][u].st).A.latest_confirmed ∧
        (x[j][u].st).A.latest_confirmed ∈ (x[j][u].st).S.T)
    : ConfirmedIncludedBetween S Sched x tE t :=
  GoldilocksCorrectness.Proofs.Executions.lem90_confirmed_included_until S Sched x GST s₀
    anchor i₁ H t tE hDiv hMono hSync hCatch hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST
    ht₀ htE hChain hInv hLocks hLocks₀ hOld hCaches hLatest

/-- **Lemma 90, inclusion, read up to a time `t`, with the caches up to `t`.** In an execution where
every time is reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ`
after `GST` (synchrony from the receiver's wake, and catch-up on wake), a block reaches a validator
only once it holds the parent, and nobody votes in an honest validator's name; under unforgeability,
with fewer than a quorum of validators ever in the adversary set and committee sleepiness from
`anchor`, at or before `x[i₁].time`; with `GST` at most the vote time of slot `s₀` and the support
cutoff of slot `s₀ + 1` at or before `x[i₁].time`; with every honest attestation sent before the
support cutoff of slot `s₀ + 1` of height at most `H`, and the lock invariant at the healed slot
`s₀` itself (`hLocks₀`: every live lock entry an honest active validator of slot `s₀` keeps after
its revocation of slot `s₀ + 1` is on a block of the honest chain before slot `s₀ + 1` or on an
ancestor of one); with roots naming blocks among what honest validators hold by `t`; with the honest
confirmations forming a chain from slot `s₀`, the chain invariant and the lock invariant at every
slot after `s₀`, the caches of every validator honest at a step at a time from `x[i₁].time` to `t`
on the honest chain with justification height greater than `H`, and every validator honest at a step
at a time at least `x[i₁].time` holding an honest confirmation as its record:
`ConfirmedIncludedBetween S Sched x tE t`, the inclusion for the slots starting at or after `tE`
whose update is at most `t`, with the confirmed tips read at steps at times at most `t`.

Why: `lem90_confirmed_included_until`'s proof, which reads the caches at steps at times at most
`t`.

Why `htE`: at a slot `s`, the proof reads the proposer's caches
and record at the step before the start of slot `s`, and `hCaches` and `hLatest` speak only of steps
at times at least `x[i₁].time`; so the slots read are those starting at or after `tE`, and each of
them starts after `x[i₁].time`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold; `t`: the time up to
  which the inclusion is read.
- `tE`: the time from which the slots are read.



Read aloud: for the slots starting at or after `tE`, each of which starts after `x[i₁].time`, up to
`t`, the honest proposer's block is what every honest active validator of its slot confirms, and
stays confirmed, unless the proposer already held a block with its root. -/
theorem lem90_confirmed_included_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H t tE : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x t)
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (htE : ∀ s : ℕ, tE ≤ slotStart S s → x[i₁].time < slotStart S s)
    (hChain : ConfirmationsChain S Sched x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hLocks₀ : ∀ u ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ u)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ t →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hLatest : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      IsHonestConfirmation S Sched x s₀ (x[j][u].st).A.latest_confirmed ∧
        (x[j][u].st).A.latest_confirmed ∈ (x[j][u].st).S.T)
    : ConfirmedIncludedBetween S Sched x tE t :=
  GoldilocksCorrectness.Proofs.Executions.lem90_confirmed_included_upTo S Sched x GST s₀ anchor i₁ H
    t tE hDiv hMono hSync hCatch hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST ht₀ htE hChain
    hInv hLocks hLocks₀ hOld hCaches hLatest

/-- **Lemma 90, inclusion, on the chain before a slot.** In an execution where every time is
reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after `GST`
(synchrony from the receiver's wake, and catch-up on wake), a block
reaches a validator only once it holds the parent, and nobody votes in an honest validator's name;
under unforgeability, with fewer than a quorum of validators ever in the adversary set and committee
sleepiness from `anchor`, at or before `x[i₁].time`; with `GST` at most the vote time of slot `s₀`
and the support cutoff of slot `s₀ + 1` at or before `x[i₁].time`; with every honest attestation
sent before the support cutoff of slot `s₀ + 1` of height at most `H`, and the lock invariant at the
healed slot `s₀` itself (`hLocks₀`: every live lock entry an honest active validator of slot `s₀`
keeps after its revocation of slot `s₀ + 1` is on a block of the honest chain before slot `s₀ + 1`
or on an ancestor of one); with roots naming blocks among what honest validators hold by `t`; with
the updaters' confirmations of the slots whose update is at most `t` forming one chain
(`ConfirmationsChainBefore`), the chain invariant and the lock invariant at every slot after `s₀`
whose update is at most `t`, the caches of every validator honest at a step at a time from
`x[i₁].time` to `t` on the honest chain with justification height greater than `H`, and every
validator honest at a step at a time from `x[i₁].time` to `t` holding as its record a block on the
honest chain at a slot whose update ran by then, which it holds:
`ConfirmedIncludedBetween S Sched x tE t`, the inclusion for the slots starting at or after `tE`
whose update is at most `t`, with the confirmed tips read at steps at times at most `t`.

Why: steps 1 to 6 of the inclusion at each such slot `q + 2`: the update of slot `q + 2` reads the
chain before slot `q + 1` and the invariant and the locks up to slot `q + 2`; a later step at a
time at most `t`, after the update of a slot `s'`, reads the chain before slot `s' + 1`, the
invariant and the locks up to slot `s'`, and the record and the finalized block right after that
update, both on the chain before slot `s' + 1`; Lemma 90's growth on the chain before a slot
(`lem90_confirmed_monotone_before`) carries the confirmed tip to the step.

Why `htE`: at a slot `s`, the proof reads the proposer's caches
and record at the step before the start of slot `s`, and `hCaches` and `hLatest` speak only of steps
at times at least `x[i₁].time`; so the slots read are those starting at or after `tE`, and each of
them starts after `x[i₁].time`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold; `t`: the time up to
  which the inclusion is read.
- `tE`: the time from which the slots are read.



Read aloud: for the slots starting at or after `tE`, each of which starts after `x[i₁].time`, when
the confirmations of the slots updated by `t` form one chain, up to `t` the honest proposer's block
is what every honest active validator of its slot confirms, and stays confirmed, unless the proposer
already held a block with its root. -/
theorem lem90_confirmed_included_before (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₁ H t tE : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x t)
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₁].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (htE : ∀ s : ℕ, tE ≤ slotStart S s → x[i₁].time < slotStart S s)
    (hChain : ∀ σ : ℕ, supportCutoff S (σ + 1) ≤ t →
      ConfirmationsChainBefore S Sched x s₀ (σ + 1))
    (hInv : ∀ s : ℕ, s₀ < s → supportCutoff S (s + 1) ≤ t →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → supportCutoff S (s + 1) ≤ t → ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hLocks₀ : ∀ u ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ u)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ t →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hLatest : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ t →
      u ∉ Sched.adv (x[j].time : Int) → (∃ σ : ℕ, supportCutoff S (σ + 1) ≤ x[j].time ∧
        OnHonestChainAt S Sched x s₀ σ (x[j][u].st).A.latest_confirmed) ∧
        (x[j][u].st).A.latest_confirmed ∈ (x[j][u].st).S.T)
    : ConfirmedIncludedBetween S Sched x tE t :=
  GoldilocksCorrectness.Proofs.Executions.lem90_confirmed_included_before S Sched x GST s₀ anchor i₁
    H t tE hDiv hMono hSync hCatch hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST ht₀ htE
    hChain hInv hLocks hLocks₀ hOld hCaches hLatest

/-- **The lock invariant at the healed slot, from Lemma 81's premises.** In an execution where every
time is reached and corruption is permanent: when committee sleepiness holds from `anchor`, at or
before the start of slot `s₀ + 1`; `B₀`'s slot is at least `s₀`; `HonestChainExtends` holds for `B₀`
at slot `s₀` at the honest active validators of slot `s₀`; and every updater of slot `s₀` saves `B₀`
— then every honest active validator `u` of slot `s₀` satisfies the lock invariant at slot `s₀` for
the honest chain before slot `s₀ + 1`. This is the discharge of the `hLocks₀` of `lem90_included_update_facts` and
`lem90_confirmed_included`.

Why: `liveLocksOnFamilyAt_base` puts every live entry on `B₀` or an ancestor of it, and `B₀` is on
the honest chain at slot `s₀`: some honest committee member of slot `s₀` is an updater that saved
it.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `anchor`: the
  time from which committee sleepiness holds; `B₀`: the healed block; `u`: the validator.

Read aloud: at the healed slot, every honest active validator's live locks are on the chain.

 -/
theorem base_locks_on_chain (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ anchor : ℕ) (B₀ : Block V) (u : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ slotStart S (s₀ + 1))
    (hB₀slot : s₀ ≤ B₀.slot)
    (hBase : HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀)
    (hBaseSaved : ∀ v ∈ updaterAt S Sched s₀,
      (stateBefore x (supportCutoff S (s₀ + 1) + 1) v).A.saved_confirmation s₀ = some B₀)
    (hu : u ∈ honestActiveAt S Sched s₀) :
    LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ u :=
  GoldilocksCorrectness.Proofs.Executions.base_locks_on_chain S Sched x s₀ anchor B₀ u hDiv hMono
    hSleepK hAnchor hB₀slot hBase hBaseSaved hu

end GoldilocksCorrectness.Statements.Executions
