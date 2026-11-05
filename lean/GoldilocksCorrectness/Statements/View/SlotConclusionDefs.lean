module
public import GoldilocksCorrectness.Statements.View.ConclusionDefs
public import GoldilocksCorrectness.Statements.Executions.FinalityWindowDefs

@[expose] public section

/-!
# The conclusions read on a run's views that read Goldilocks's slots

The conclusions of the top statements that read, beside the views (`NodeView B`) and the times, the
slots of a Goldilocks setup `S`: their start times, their proposers, their support cutoffs, the
validators active at a slot and the validators that ran a slot's update. Blocks and messages are
read through a vocabulary `W : ViewVocab V B M`, so the block type is any protocol's; the slot
structure is Goldilocks's.

- `ProposalAtV`, `RootCollisionAtProposalV`, `RootCollisionAtOpeningV`: a slot's proposal, a
  proposal carrying the root of a block its proposer already held, and such a proposal at one of
  the honest round opening slots `r 0 < … < r m`;
- `ConfirmedIncludedBetweenV`: Lemma 90's inclusion read between two times, without the clause on
  the validator's saved confirmation of the slot, which `NodeView` does not keep, and
  `ConfirmedIncludedAfterHealingV`, the same with no upper end;
- `ConfirmedExtendedByHonestProposalsBetweenV`: Lemma 90's fourth conclusion read up to a time,
  every honest proposal a strict descendant of the confirmed tips honest validators had from the
  phase's end until its slot started, and `ConfirmedExtendedByHonestProposalsV`, the same with no
  upper end;
- `ConfirmedPersistsBetweenV`, `FinalizedCompatibleBetweenV`, `ConfirmedPersistsFromV`,
  `FinalizedCompatibleFromV`: the asynchrony statement's two conclusions, read up to a time and
  with no upper end;
- `FinalityIncludedBetweenV`: Lemma 98's conclusion read up to a time, for the rounds whose fourth
  opening slot is updated by then and the readers whose step is at or before some support cutoff by
  then, and `FinalityIncludedAfterHealingV`, the same with no
  upper end;

- `FinalizedExtendedByHonestProposalsBetweenV`: Lemma 98's second conclusion read up to a time, as
  `FinalityIncludedBetweenV` reads it, the readers' finalized blocks strict descendants of the
  finalized blocks honest validators had from the phase's end until the proposal's slot started
.
-/

set_option autoImplicit false

open GoldilocksCorrectness.Statements.Routines (slotStart supportCutoff)

namespace GoldilocksCorrectness.Statements.View

open Framework.StsMultisetLog (AtomicAction Schedule)
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Network
open GoldilocksCorrectness.Statements.Executions (honestActiveAt updaterAt HonestOpenerAt
  FinalityWindowAt AwakeForDelayWithin)

variable {V : Type} [DecidableEq V] [Fintype V] {B M Ev : Type} [DecidableEq M]
  (W : ViewVocab V B M) (S : Setup V) (Sched : Schedule V) (x : Trace V M (NodeView B) Ev)

/-! ## Proposals and root collisions -/

/-- `ProposalAtV W S x s b`: the proposer of slot `s` puts the block `b` on the wire at the step
of `x` that is the tick of every awake validator at the start of slot `s`.

The variables:
- `W`: the vocabulary; `S`: the setup; `x`: the trace of views; `s`: the slot; `b`: the block.

Read aloud: `b` is slot `s`'s proposal. -/
def ProposalAtV (s : ℕ) (b : B) : Prop :=
  ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
    PutsBlockV W x i (S.P.proposer s) b

/-- `RootCollisionAtProposalV W S x s b`: some block the proposer of slot `s` holds when the run
moves to the start of slot `s` carries the root of `b` (`W.sameRoot`).

The variables:
- `W`: the vocabulary; `S`: the setup; `x`: the trace of views; `s`: the slot; `b`: the
  proposal.

Read aloud: a block the proposer held before the proposal's slot has the proposal's root. -/
def RootCollisionAtProposalV (s : ℕ) (b : B) : Prop :=
  ∃ b' ∈ (stateBeforeV x (slotStart S s) (S.P.proposer s)).T, W.sameRoot b' b

/-- `RootCollisionAtOpeningV W S x r m`: for some `i ≤ m`, the proposer of slot `r i * R` puts a
block `b` on the wire at its tick at that slot's start, and some block that proposer held then
carries the root of `b`.

The variables:
- `W`: the vocabulary; `S`: the setup; `x`: the trace of views; `r`: the rounds of the honest
  round opening slots; `m`: the index of the last one.

Read aloud: some honest round opening slot's proposal has the root of a block its proposer already
held. -/
def RootCollisionAtOpeningV (r : ℕ → ℕ) (m : ℕ) : Prop :=
  ∃ i : ℕ, i ≤ m ∧ ∃ b : B, ProposalAtV W S x (r i * S.C.R) b ∧
    RootCollisionAtProposalV W S x (r i * S.C.R) b

/-! ## Lemma 90's inclusion -/

/-- `ConfirmedIncludedBetweenV W S Sched x tE t`: for every slot `s` starting at or after `tE` whose
support cutoff of slot `s + 1` is at most `t`, and whose proposer is awake and outside the
adversary set at every time from the start of its proposal window to that support cutoff
(`HonestOpenerAt`): slot `s` has a proposal; and every proposal `b` of slot `s` either carries the
root of a block its proposer held when the run moved to the start of slot `s`, or is the confirmed
tip of every honest active validator of slot `s` when the run moves to the time after the support
cutoff of slot `s + 1`, and is the confirmed tip or an ancestor of the confirmed tip (`W.anc`) of
every validator `v` honest and active at a slot `s' ≥ s`, at every step `j` at a time after the
support cutoff of slot `s' + 1` and at most `t` through which `v` has been honest.

The variables:
- `W`: the vocabulary; `S`: the setup; `Sched`: the schedule; `x`: the trace of views; `tE`: the
  time from which the slots are read; `t`: the time up to which the updates and the confirmed
  tips are read.

Read aloud: from `tE` and up to `t`, every honest proposal becomes the confirmed tip of every
honest active validator of its slot and stays confirmed, unless its proposer already held a block
with its root. -/
def ConfirmedIncludedBetweenV (tE t : ℕ) : Prop :=
  ∀ s : ℕ, tE ≤ slotStart S s → supportCutoff S (s + 1) ≤ t → HonestOpenerAt S Sched s →
    (∃ b : B, ProposalAtV W S x s b) ∧
    ∀ b : B, ProposalAtV W S x s b →
      RootCollisionAtProposalV W S x s b ∨
      ((∀ v ∈ honestActiveAt S Sched s, (stateBeforeV x (supportCutoff S (s + 1) + 1) v).C = b) ∧
       (∀ (v : V) (j s' : ℕ), HonestThroughV Sched x j v → s ≤ s' →
          v ∈ honestActiveAt S Sched s' → supportCutoff S (s' + 1) < x[j].time → x[j].time ≤ t →
          W.anc b x[j][v].st.C))

/-- `ConfirmedIncludedAfterHealingV W S Sched x tE`: `ConfirmedIncludedBetweenV` with no upper end.
For every slot `s` starting at or after `tE` whose proposer is awake and outside the adversary set
at every time from the start of its proposal window to the support cutoff of slot `s + 1`
(`HonestOpenerAt`): slot `s` has a proposal; and every proposal `b` of slot `s` either carries the
root of a block its proposer held when the run moved to the start of slot `s`, or is the confirmed
tip of every honest active validator of slot `s` when the run moves to the time after the support
cutoff of slot `s + 1`, and is the confirmed tip or an ancestor of the confirmed tip (`W.anc`) of
every validator `v` honest and active at a slot `s' ≥ s`, at every step `j` at a time after the
support cutoff of slot `s' + 1` through which `v` has been honest.

The variables:
- `W`: the vocabulary; `S`: the setup; `Sched`: the schedule; `x`: the trace of views; `tE`: the
  time from which the slots are read.

Read aloud: from `tE`, every honest proposal becomes the confirmed tip of every honest active
validator of its slot and stays confirmed, unless its proposer already held a block with its
root. -/
def ConfirmedIncludedAfterHealingV (tE : ℕ) : Prop :=
  ∀ s : ℕ, tE ≤ slotStart S s → HonestOpenerAt S Sched s →
    (∃ b : B, ProposalAtV W S x s b) ∧
    ∀ b : B, ProposalAtV W S x s b →
      RootCollisionAtProposalV W S x s b ∨
      ((∀ v ∈ honestActiveAt S Sched s, (stateBeforeV x (supportCutoff S (s + 1) + 1) v).C = b) ∧
       (∀ (v : V) (j s' : ℕ), HonestThroughV Sched x j v → s ≤ s' →
          v ∈ honestActiveAt S Sched s' → supportCutoff S (s' + 1) < x[j].time →
          W.anc b x[j][v].st.C))

/-- `ConfirmedExtendedByHonestProposalsBetweenV W S Sched x tE t`: for every slot `s` starting at or
after `tE` whose support cutoff of slot `s + 1` is at most `t`, and whose proposer is awake and
outside the adversary set at every time from the start of its proposal window to that support cutoff
(`HonestOpenerAt`): every proposal `b` of slot `s` either carries the root of a block its proposer
held when the run moved to the start of slot `s`, or is a strict descendant of the confirmed tip of
every validator `v` after every step `i` through which `v` has been honest, at a time from `tE` to
before the start of slot `s`: that confirmed tip is an ancestor of `b` or `b` (`W.anc`), and is not
`b`.

The variables:
- `W`: the vocabulary; `S`: the setup; `Sched`: the schedule; `x`: the trace of views; `tE`: the
  time from which the slots are read; `t`: the time up to which the updates are read.

Read aloud: from `tE` and up to `t`, every honest proposal strictly extends every confirmed tip
an honest validator had from `tE` until the proposal's slot started, unless its proposer already
held a block with its root. -/
def ConfirmedExtendedByHonestProposalsBetweenV (tE t : ℕ) : Prop :=
  ∀ s : ℕ, tE ≤ slotStart S s → supportCutoff S (s + 1) ≤ t → HonestOpenerAt S Sched s →
    ∀ b : B, ProposalAtV W S x s b →
      RootCollisionAtProposalV W S x s b ∨
      ∀ (v : V) (i : ℕ), HonestThroughV Sched x i v → tE ≤ x[i].time →
        x[i].time < slotStart S s → W.anc x[i][v].st.C b ∧ x[i][v].st.C ≠ b

/-- `ConfirmedExtendedByHonestProposalsV W S Sched x tE`:
`ConfirmedExtendedByHonestProposalsBetweenV` with no upper end. For every slot `s` starting at or
after `tE` whose proposer is awake and outside the adversary set at every time from the start of its
proposal window to the support cutoff of slot `s + 1` (`HonestOpenerAt`): every proposal `b` of slot
`s` either carries the root of a block its proposer held when the run moved to the start of slot
`s`, or is a strict descendant of the confirmed tip of every validator `v` after every step `i`
through which `v` has been honest, at a time from `tE` to before the start of slot `s`: that
confirmed tip is an ancestor of `b` or `b` (`W.anc`), and is not `b`.

The variables:
- `W`: the vocabulary; `S`: the setup; `Sched`: the schedule; `x`: the trace of views; `tE`: the
  time from which the slots are read.

Read aloud: from `tE`, every honest proposal strictly extends every confirmed tip an honest
validator had from `tE` until the proposal's slot started, unless its proposer already held a
block with its root. -/
def ConfirmedExtendedByHonestProposalsV (tE : ℕ) : Prop :=
  ∀ s : ℕ, tE ≤ slotStart S s → HonestOpenerAt S Sched s →
    ∀ b : B, ProposalAtV W S x s b →
      RootCollisionAtProposalV W S x s b ∨
      ∀ (v : V) (i : ℕ), HonestThroughV Sched x i v → tE ≤ x[i].time →
        x[i].time < slotStart S s → W.anc x[i][v].st.C b ∧ x[i][v].st.C ≠ b

/-! ## The asynchrony statement's conclusions -/

/-- `ConfirmedPersistsBetweenV W S Sched x s tAwakeEnd b₀ t`: every block `P` that is, after a step
`i` at a time from `tAwakeEnd` to the support cutoff of slot `s + 1`, the confirmed tip of a
validator honest through `i`, or an ancestor of it (`W.anc`), is, after every step `j` at a time
from `b₀` to `t`, the confirmed tip or an ancestor of the confirmed tip of every validator of
`updaterAt S Sched s` honest through `j`.

The variables:
- `W`: the vocabulary; `S`: the setup; `Sched`: the schedule; `x`: the trace of views; `s`: the
  hand-over slot; `tAwakeEnd`: the time from which the confirmed tips are protected; `b₀`: the
  start of the asynchronous period; `t`: the time up to which the later steps are read.

Read aloud: every block confirmed by an honest validator from `tAwakeEnd` to the hand-over update
stays, from `b₀` up to `t`, an ancestor of or equal to the confirmed tip of every honest validator
that ran that update. -/
def ConfirmedPersistsBetweenV (s tAwakeEnd b₀ t : ℕ) : Prop :=
  ∀ (v : V) (i : ℕ) (P : B),
    HonestThroughV Sched x i v → tAwakeEnd ≤ x[i].time → x[i].time ≤ supportCutoff S (s + 1) →
    W.anc P x[i][v].st.C →
    ∀ (v' : V) (j : ℕ), HonestThroughV Sched x j v' → v' ∈ updaterAt S Sched s →
      b₀ ≤ x[j].time → x[j].time ≤ t → W.anc P x[j][v'].st.C

/-- `FinalizedCompatibleBetweenV W S Sched x s tAwakeEnd b₀ t`: every block `P` that is, after a
step `i` at a time from `tAwakeEnd` to the support cutoff of slot `s + 1`, the confirmed tip of a
validator honest through `i`, or an ancestor of it, is compatible (`W.Compatible`) with the
finalized block of every validator honest through any step `j` at a time from `b₀` to `t`.

The variables:
- `W`: the vocabulary; `S`: the setup; `Sched`: the schedule; `x`: the trace of views; `s`: the
  hand-over slot; `tAwakeEnd`: the time from which the confirmed tips are protected; `b₀`: the
  start of the asynchronous period; `t`: the time up to which the later steps are read.

Read aloud: from `b₀` up to `t`, no honest validator finalizes a block conflicting with what was
confirmed from `tAwakeEnd` to the hand-over update. -/
def FinalizedCompatibleBetweenV (s tAwakeEnd b₀ t : ℕ) : Prop :=
  ∀ (v : V) (i : ℕ) (P : B),
    HonestThroughV Sched x i v → tAwakeEnd ≤ x[i].time → x[i].time ≤ supportCutoff S (s + 1) →
    W.anc P x[i][v].st.C →
    ∀ (v' : V) (j : ℕ), HonestThroughV Sched x j v' → b₀ ≤ x[j].time → x[j].time ≤ t →
      W.Compatible P x[j][v'].st.F

/-- `ConfirmedPersistsFromV W S Sched x s tAwakeEnd b₀`: `ConfirmedPersistsBetweenV` with no upper
end: every block `P` that is, after a step `i` at a time from `tAwakeEnd` to the support cutoff of
slot `s + 1`, the confirmed tip of a validator honest through `i`, or an ancestor of it, is, after
every step `j` at a time at least `b₀`, the confirmed tip or an ancestor of the confirmed tip of
every validator of `updaterAt S Sched s` honest through `j`.

The variables:
- `W`: the vocabulary; `S`: the setup; `Sched`: the schedule; `x`: the trace of views; `s`: the
  hand-over slot; `tAwakeEnd`: the time from which the confirmed tips are protected; `b₀`: the
  start of the asynchronous period.

Read aloud: every block confirmed by an honest validator from `tAwakeEnd` to the hand-over update
stays, from `b₀` on, an ancestor of or equal to the confirmed tip of every honest validator that
ran that update. -/
def ConfirmedPersistsFromV (s tAwakeEnd b₀ : ℕ) : Prop :=
  ∀ (v : V) (i : ℕ) (P : B),
    HonestThroughV Sched x i v → tAwakeEnd ≤ x[i].time → x[i].time ≤ supportCutoff S (s + 1) →
    W.anc P x[i][v].st.C →
    ∀ (v' : V) (j : ℕ), HonestThroughV Sched x j v' → v' ∈ updaterAt S Sched s →
      b₀ ≤ x[j].time → W.anc P x[j][v'].st.C

/-- `FinalizedCompatibleFromV W S Sched x s tAwakeEnd b₀`: `FinalizedCompatibleBetweenV` with no
upper end: every block `P` that is, after a step `i` at a time from `tAwakeEnd` to the support
cutoff of slot `s + 1`, the confirmed tip of a validator honest through `i`, or an ancestor of it,
is compatible with the finalized block of every validator honest through any step `j` at a time at
least `b₀`.

The variables:
- `W`: the vocabulary; `S`: the setup; `Sched`: the schedule; `x`: the trace of views; `s`: the
  hand-over slot; `tAwakeEnd`: the time from which the confirmed tips are protected; `b₀`: the
  start of the asynchronous period.

Read aloud: from `b₀` on, no honest validator finalizes a block conflicting with what was confirmed
from `tAwakeEnd` to the hand-over update. -/
def FinalizedCompatibleFromV (s tAwakeEnd b₀ : ℕ) : Prop :=
  ∀ (v : V) (i : ℕ) (P : B),
    HonestThroughV Sched x i v → tAwakeEnd ≤ x[i].time → x[i].time ≤ supportCutoff S (s + 1) →
    W.anc P x[i][v].st.C →
    ∀ (v' : V) (j : ℕ), HonestThroughV Sched x j v' → b₀ ≤ x[j].time →
      W.Compatible P x[j][v'].st.F

/-! ## Lemma 98's conclusion -/

/-- `FinalityIncludedBetweenV W S Sched x Δw tE t`: for every slot `s` starting at or after `tE`
with `HonestOpenerAt S Sched s`, and every round `r` with `s ≤ r * R`, `FinalityWindowAt S Sched r`
and the update of slot `(r + 3) * R` at most `t`: slot
`s` has a proposal; and every proposal `b` of slot `s` either carries the root of a block its
proposer held when the run moved to the start of slot `s`, or one of the proposals of the rounds
`r` to `r + 3` carries the root of a block its proposer held (`RootCollisionAtOpeningV`), or every
validator `v` honest through a step `j` at or before some support cutoff at most `t` (some slot
`s'` with `x[j].time ≤ supportCutoff S s' ≤ t`), awake for one whole delay or one whole catch-up
delay `Δw`, whichever is longer, between the start of slot `(r + 3) * R` and the time of step `j`,
has after step `j` a finalized block of which `b` is an ancestor or which is `b` (`W.anc`), and
which no validator had as its finalized block after a step at a time before the start of slot `s`.

The window and the reader are the restated statement's. The reading with every reader whose step is at a time
at most `t`, and the window from the fourth opening slot's support cutoff, is
`FinalityIncludedBetweenEveryReaderV`.

The variables:
- `W`: the vocabulary; `S`: the setup; `Sched`: the schedule; `x`: the trace of views; `Δw`: the
  catch-up delay, which with `Δ S` sets how long a reader is awake (`AwakeForDelayWithin`); `tE`:
  the time from which the slots are read; `t`: the time that decides the rounds and the readers: a
  round's fourth opening slot is updated by `t`, and a reader's step is at or before some support
  cutoff at most `t`.

Read aloud: from `tE`, for the readers whose step is at or before some support cutoff at most `t`,
whenever four consecutive honest round opening slots with quorums at the first three follow an
honest proposal, and the update of the fourth opening slot is at most `t`, everyone awake for a
delay after the fourth opening slot has finalized that proposal or a descendant of it, a block no
validator had finalized before the proposal, unless a root collision hit one of the five
proposals. -/
def FinalityIncludedBetweenV (Δw tE t : ℕ) : Prop :=
  ∀ (s r : ℕ), tE ≤ slotStart S s → HonestOpenerAt S Sched s → s ≤ r * S.C.R →
    FinalityWindowAt S Sched r → supportCutoff S ((r + 3) * S.C.R + 1) ≤ t →
    (∃ b : B, ProposalAtV W S x s b) ∧
    ∀ b : B, ProposalAtV W S x s b →
      RootCollisionAtProposalV W S x s b ∨
      RootCollisionAtOpeningV W S x (fun i => r + i) 3 ∨
      ∀ (v : V) (j : ℕ), HonestThroughV Sched x j v →
        (∃ s' : ℕ, x[j].time ≤ supportCutoff S s' ∧ supportCutoff S s' ≤ t) →
        AwakeForDelayWithin S Sched Δw v (slotStart S ((r + 3) * S.C.R)) x[j].time →
        W.anc b x[j][v].st.F ∧
        ∀ (v' : V) (i' : ℕ), x[i'].time < slotStart S s → x[i'][v'].st.F ≠ x[j][v].st.F

/-- For every slot `s` starting at or after `tE` with `HonestOpenerAt S Sched s`, and every
round `r` with `s ≤ r * R`, `FinalityWindowAt S Sched r` and the support cutoff of slot `(r + 3) * R`
at most `t`: slot `s` has a proposal; and every proposal `b` of slot `s` either carries the root of
a block its proposer held when the run moved to the start of slot `s`, or one of the proposals of
the rounds `r` to `r + 3` carries the root of a block its proposer held
(`RootCollisionAtOpeningV`), or every validator `v` honest through a step `j` at a time at most `t`,
awake for one whole delay or one whole catch-up delay `Δw`, whichever is longer, between the start
of slot `(r + 3) * R` and the time of step `j`, has after step `j` a finalized block of which `b`
is an ancestor or which is `b` (`W.anc`), and which no validator had as its finalized block after a
step at a time before the start of slot `s`.

At the same `t` it reads every round and every reader `FinalityIncludedBetweenV` reads, and more:
the rounds whose fourth opening slot's support cutoff is at most `t` while the next slot's is
after `t`, and the readers whose step has no support cutoff between it and `t`. It is the first
conclusion of `lem98_healed_finality_liveness_everyReader`.

The variables:
- `W`: the vocabulary; `S`: the setup; `Sched`: the schedule; `x`: the trace of views; `Δw`: the
  catch-up delay, which with `Δ S` sets how long a reader is awake (`AwakeForDelayWithin`); `tE`:
  the time from which the slots are read; `t`: the time up to which the readers' steps are read.

Read aloud: from `tE` and up to `t`, whenever four consecutive honest round opening slots with
quorums at the first three follow an honest proposal, everyone awake for a delay after the fourth
opening slot has finalized that proposal or a descendant of it, a block no validator had finalized
before the proposal, unless a root collision hit one of the five proposals. -/
def FinalityIncludedBetweenEveryReaderV (Δw tE t : ℕ) : Prop :=
  ∀ (s r : ℕ), tE ≤ slotStart S s → HonestOpenerAt S Sched s → s ≤ r * S.C.R →
    FinalityWindowAt S Sched r → supportCutoff S ((r + 3) * S.C.R) ≤ t →
    (∃ b : B, ProposalAtV W S x s b) ∧
    ∀ b : B, ProposalAtV W S x s b →
      RootCollisionAtProposalV W S x s b ∨
      RootCollisionAtOpeningV W S x (fun i => r + i) 3 ∨
      ∀ (v : V) (j : ℕ), HonestThroughV Sched x j v → x[j].time ≤ t →
        AwakeForDelayWithin S Sched Δw v (slotStart S ((r + 3) * S.C.R)) x[j].time →
        W.anc b x[j][v].st.F ∧
        ∀ (v' : V) (i' : ℕ), x[i'].time < slotStart S s → x[i'][v'].st.F ≠ x[j][v].st.F

/-- `FinalityIncludedAfterHealingV W S Sched x Δw tE`: `FinalityIncludedBetweenV` with no upper end.
For every slot `s` starting at or after `tE` with `HonestOpenerAt S Sched s`, and every round `r`
with `s ≤ r * R` and `FinalityWindowAt S Sched r`: slot `s` has a proposal; and every proposal `b`
of slot `s` either carries the root of a block its proposer held when the run moved to the start of
slot `s`, or one of the proposals of the rounds `r` to `r + 3` carries the root of a block its
proposer held (`RootCollisionAtOpeningV`), or every validator `v` honest through a step `j`, awake
for one whole delay or one whole catch-up delay `Δw`, whichever is longer, between the start of slot
`(r + 3) * R` and the time of step `j`, has after step `j` a finalized block of which `b` is an
ancestor or which is `b` (`W.anc`), and which no validator had as its finalized block after a step
at a time before the start of slot `s`.

The variables:
- `W`: the vocabulary; `S`: the setup; `Sched`: the schedule; `x`: the trace of views; `Δw`: the
  catch-up delay, which with `Δ S` sets how long a reader is awake (`AwakeForDelayWithin`); `tE`:
  the time from which the slots are read.

Read aloud: from `tE`, whenever four consecutive honest round opening slots with quorums at the
first three follow an honest proposal, everyone awake for a delay after the fourth opening slot
has finalized that proposal or a descendant of it, a block no validator had finalized before the
proposal, unless a root collision hit one of the five proposals. -/
def FinalityIncludedAfterHealingV (Δw tE : ℕ) : Prop :=
  ∀ (s r : ℕ), tE ≤ slotStart S s → HonestOpenerAt S Sched s → s ≤ r * S.C.R →
    FinalityWindowAt S Sched r →
    (∃ b : B, ProposalAtV W S x s b) ∧
    ∀ b : B, ProposalAtV W S x s b →
      RootCollisionAtProposalV W S x s b ∨
      RootCollisionAtOpeningV W S x (fun i => r + i) 3 ∨
      ∀ (v : V) (j : ℕ), HonestThroughV Sched x j v →
        AwakeForDelayWithin S Sched Δw v (slotStart S ((r + 3) * S.C.R)) x[j].time →
        W.anc b x[j][v].st.F ∧
        ∀ (v' : V) (i' : ℕ), x[i'].time < slotStart S s → x[i'][v'].st.F ≠ x[j][v].st.F

/-- `FinalizedExtendedByHonestProposalsBetweenV W S Sched x Δw tE t`: for every slot `s` starting at
or after `tE` with `HonestOpenerAt S Sched s`, and every round `r` with `s ≤ r * R`,
`FinalityWindowAt S Sched r` and the update of slot `(r + 3) * R` at most `t`
: every proposal `b` of
slot `s` either carries the root of a block its proposer held when the run moved to the start of
slot `s`, or one of the proposals of the rounds `r` to `r + 3` carries the root of a block its
proposer held (`RootCollisionAtOpeningV`), or every validator `v` honest through a step `j` at or
before some support cutoff at most `t` (some slot `s'` with `x[j].time ≤ supportCutoff S s' ≤ t`),
awake for one whole delay or one whole catch-up delay `Δw`, whichever is longer, between the start
of slot `(r + 3) * R` and the time of step `j`, has after step `j` a finalized block that strictly
extends the finalized block of every validator `w` after every step `i` through which `w` has been
honest, at a time from `tE` to before the start of slot `s`: `w`'s finalized block is an ancestor
of `v`'s or `v`'s (`W.anc`), and is not `v`'s.

The window and the reader are the restated statement's. The
reading with every reader whose step is at a time at most `t`, and the window from the fourth
opening slot's support cutoff, is `FinalizedExtendedByHonestProposalsBetweenEveryReaderV`.

The variables:
- `W`: the vocabulary; `S`: the setup; `Sched`: the schedule; `x`: the trace of views; `Δw`: the
  catch-up delay, which with `Δ S` sets how long a reader is awake (`AwakeForDelayWithin`); `tE`:
  the time from which the slots are read; `t`: the time that decides the rounds and the readers
.

Read aloud: from `tE`, for the readers whose step is at or before some support cutoff at most `t`,
whenever four consecutive honest round opening slots with quorums at the first three follow an
honest proposal, and the update of the fourth opening slot is at most `t`, everyone awake for a
delay after the fourth opening slot has a finalized block that strictly extends every finalized
block an honest validator had from `tE` until the proposal's slot started, unless a root collision
hit one of the five proposals. -/
def FinalizedExtendedByHonestProposalsBetweenV (Δw tE t : ℕ) : Prop :=
  ∀ (s r : ℕ), tE ≤ slotStart S s → HonestOpenerAt S Sched s → s ≤ r * S.C.R →
    FinalityWindowAt S Sched r → supportCutoff S ((r + 3) * S.C.R + 1) ≤ t →
    ∀ b : B, ProposalAtV W S x s b →
      RootCollisionAtProposalV W S x s b ∨
      RootCollisionAtOpeningV W S x (fun i => r + i) 3 ∨
      ∀ (v : V) (j : ℕ), HonestThroughV Sched x j v →
        (∃ s' : ℕ, x[j].time ≤ supportCutoff S s' ∧ supportCutoff S s' ≤ t) →
        AwakeForDelayWithin S Sched Δw v (slotStart S ((r + 3) * S.C.R)) x[j].time →
        ∀ (w : V) (i : ℕ), HonestThroughV Sched x i w → tE ≤ x[i].time →
          x[i].time < slotStart S s →
          W.anc x[i][w].st.F x[j][v].st.F ∧ x[i][w].st.F ≠ x[j][v].st.F

/-- For every slot `s` starting at or after `tE` with
`HonestOpenerAt S Sched s`, and every round `r` with `s ≤ r * R`, `FinalityWindowAt S Sched r` and
the support cutoff of slot `(r + 3) * R` at most `t`: every proposal `b` of slot `s` either carries
the root of a block its proposer held when the run moved to the start of slot `s`, or one of the
proposals of the rounds `r` to `r + 3` carries the root of a block its proposer held
(`RootCollisionAtOpeningV`), or every validator `v` honest through a step `j` at a time at most `t`,
awake for one whole delay or one whole catch-up delay `Δw`, whichever is longer, between the start
of slot `(r + 3) * R` and the time of step `j`, has after step `j` a finalized block that strictly
extends the finalized block of every validator `w` after every step `i` through which `w` has been
honest, at a time from `tE` to before the start of slot `s`: `w`'s finalized block is an ancestor
of `v`'s or `v`'s (`W.anc`), and is not `v`'s.

At the same `t` it reads every round and every reader `FinalizedExtendedByHonestProposalsBetweenV`
reads, and more: the rounds whose fourth opening slot's support cutoff is at most `t` while the
next slot's is after `t`, and the readers whose step has no support cutoff between it and `t`. It
is the second conclusion of `lem98_healed_finality_liveness_everyReader`.

The variables:
- `W`: the vocabulary; `S`: the setup; `Sched`: the schedule; `x`: the trace of views; `Δw`: the
  catch-up delay, which with `Δ S` sets how long a reader is awake (`AwakeForDelayWithin`); `tE`:
  the time from which the slots are read; `t`: the time up to which the readers' steps are read.

Read aloud: from `tE` and up to `t`, whenever four consecutive honest round opening slots with
quorums at the first three follow an honest proposal, everyone awake for a delay after the fourth
opening slot has a finalized block that strictly extends every finalized block an honest validator
had from `tE` until the proposal's slot started, unless a root collision hit one of the five
proposals. -/
def FinalizedExtendedByHonestProposalsBetweenEveryReaderV (Δw tE t : ℕ) : Prop :=
  ∀ (s r : ℕ), tE ≤ slotStart S s → HonestOpenerAt S Sched s → s ≤ r * S.C.R →
    FinalityWindowAt S Sched r → supportCutoff S ((r + 3) * S.C.R) ≤ t →
    ∀ b : B, ProposalAtV W S x s b →
      RootCollisionAtProposalV W S x s b ∨
      RootCollisionAtOpeningV W S x (fun i => r + i) 3 ∨
      ∀ (v : V) (j : ℕ), HonestThroughV Sched x j v → x[j].time ≤ t →
        AwakeForDelayWithin S Sched Δw v (slotStart S ((r + 3) * S.C.R)) x[j].time →
        ∀ (w : V) (i : ℕ), HonestThroughV Sched x i w → tE ≤ x[i].time →
          x[i].time < slotStart S s →
          W.anc x[i][w].st.F x[j][v].st.F ∧ x[i][w].st.F ≠ x[j][v].st.F

end GoldilocksCorrectness.Statements.View
