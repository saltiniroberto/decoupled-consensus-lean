module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.FinalityWindowDefs
public import GoldilocksCorrectness.Statements.View.SlotConclusionDefs
public import GoldilocksCorrectness.Statements.AbstractTrace.ViewDefs
public import GoldilocksCorrectness.Statements.AbstractTrace.ViewDefs
public import GoldilocksCorrectness.Statements.AbstractTrace.ViewDefs

@[expose] public section

/-!
# SlotConclusionDefs, over a model

The definitions of `GoldilocksCorrectness/Statements/View/SlotConclusionDefs.lean` over a model `M`:
the conclusions read on a run's views that read the slots, read at the model's times (`M.slotStart
S.C`, `M.supportCutoff S.C`) and over the model's sets of active and updating validators. The landed
page's message type `M` is `Msg` here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open GoldilocksCorrectness.Statements.Routines (slotStart supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.View

open GoldilocksCorrectness.Statements.View (NodeView)
open GoldilocksCorrectness.Statements.AbstractTrace.View (PutsBlockV)

open GoldilocksCorrectness.Record.Statements.Executions (honestActiveAt updaterAt
  HonestOpenerAt FinalityWindowAt)

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Network
open GoldilocksCorrectness.Statements.AbstractTrace.View (AwakeForDelayWithin)

variable {V : Type} [DecidableEq V] [Fintype V] {B Msg : Type} [DecidableEq Msg]
variable (M : GoldilocksModel V)
variable (W : ViewVocab V B Msg) (S : Setup V) (A : Activity V) (x : Trace V Msg (NodeView B))

/-! ## Proposals and root collisions -/

/-- `ProposalAtV M W S x s b`: the proposer of slot `s` puts the block `b` on the wire at its own
tick to the start of slot `s`.

The variables:
- `M`: the model;
- `W`: the vocabulary; `S`: the setup; `x`: the trace of views; `s`: the slot; `b`: the block.

Read aloud: `b` is slot `s`'s proposal. -/
def ProposalAtV (s : ℕ) (b : B) : Prop :=
  ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) ∧
    PutsBlockV W x i (S.P.proposer s) b

/-- `RootCollisionAtProposalV M W S x s b`: some block of the view the proposer of slot `s` has at its
tick to the start of slot `s` (the state that tick starts from) carries the root of `b`
(`W.sameRoot`). The read is at the proposer's own tick, the state its proposal is computed from: a
delivery and a tick at one time have no order, and the tick may be up to `ΔClockAhead` before or
`ΔClockBehind` after the slot's start in real time.

The variables:
- `M`: the model;
- `W`: the vocabulary; `S`: the setup; `x`: the trace of views; `s`: the slot; `b`: the
  proposal.

Read aloud: a block the proposer held when its tick to the proposal's slot started has the proposal's
root. -/
def RootCollisionAtProposalV (s : ℕ) (b : B) : Prop :=
  ∃ b' ∈ (x.tickInput (S.P.proposer s) (M.slotStart S.C s)).T, W.sameRoot b' b

/-- `RootCollisionAtOpeningV M W S x r m`: for some `i ≤ m`, the proposer of slot `r i * R` puts a
block `b` on the wire at its tick at that slot's start, and some block that proposer held then
carries the root of `b`.

The variables:
- `M`: the model;
- `W`: the vocabulary; `S`: the setup; `x`: the trace of views; `r`: the rounds of the honest
  round opening slots; `m`: the index of the last one.

Read aloud: some honest round opening slot's proposal has the root of a block its proposer already
held. -/
def RootCollisionAtOpeningV (r : ℕ → ℕ) (m : ℕ) : Prop :=
  ∃ i : ℕ, i ≤ m ∧ ∃ b : B, ProposalAtV M W S x (r i * S.C.R) b ∧
    RootCollisionAtProposalV M W S x (r i * S.C.R) b

/-! ## Lemma 90's inclusion -/

/-- `ConfirmedIncludedBetweenV M W S Sched x tE t`: for every slot `s` starting at or after `tE`
whose support cutoff of slot `s + 1` is at most `t`, and whose proposer is awake and outside the
adversary set at every time from the start of its proposal window to that support cutoff
(`HonestOpenerAt`): slot `s` has a proposal; and every proposal `b` of slot `s` either carries the
root of a block its proposer held when the run moved to the start of slot `s`, or is the confirmed
tip of every honest active validator `v` of slot `s` whose own tick to the support cutoff `c` of slot
`s + 1` is at a real time at most `t`, in the state that tick leaves
(`x.tickOutput v c`, the configuration right after that tick), and is the confirmed tip or an
ancestor of the confirmed tip (`W.anc`) of
every validator `v` honest and active at a slot `s' ≥ s`, in the state every step `j` leaves
 that is `v`'s own tick to the support cutoff of slot
`s' + 1` or a later step, at a time at most `t`, with `v` outside the adversary set at every time up to the time of that step.

The variables:
- `M`: the model;
- `W`: the vocabulary; `S`: the setup; `Sched`: the schedule; `x`: the trace of views; `tE`: the
  time from which the slots are read; `t`: the time up to which the updates and the confirmed
  tips are read.

Read aloud: from `tE` and up to `t`, every honest proposal becomes the confirmed tip of every
honest active validator of its slot and stays confirmed, unless its proposer already held a block
with its root. -/
def ConfirmedIncludedBetweenV (tE t : ℕ) : Prop :=
  ∀ s : ℕ, tE ≤ M.slotStart S.C s → M.supportCutoff S.C (s + 1) ≤ t → HonestOpenerAt M S A x s →
    (∃ b : B, ProposalAtV M W S x s b) ∧
    ∀ b : B, ProposalAtV M W S x s b →
      RootCollisionAtProposalV M W S x s b ∨
      ((∀ v ∈ honestActiveAt M S A x s,
          (x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) : ℝ) ≤ t →
          (x.tickOutput v (M.supportCutoff S.C (s + 1))).C = b) ∧
       (∀ (v : V) (j s' : ℕ), A.HonestThroughTime x (x.time j) v → s ≤ s' →
          v ∈ honestActiveAt M S A x s' → x.tickStep v (M.supportCutoff S.C (s' + 1)) ≤ j →
            M.supportCutoff S.C (s' + 1) ≤ t → x.time j ≤ t →
          W.anc b (x.st (j + 1) v).C))

/-- `ConfirmedIncludedAfterHealingV M W S Sched x tE`: `ConfirmedIncludedBetweenV` with no upper
end. For every slot `s` starting at or after `tE` whose proposer is awake and outside the adversary
set at every time from the start of its proposal window to the support cutoff of slot `s + 1`
(`HonestOpenerAt`): slot `s` has a proposal; and every proposal `b` of slot `s` either carries the
root of a block its proposer held when the run moved to the start of slot `s`, or is the confirmed
tip of every honest active validator `v` of slot `s` in the state `v`'s own tick to the support
cutoff `c` of slot `s + 1` leaves (`x.tickOutput v c`, the configuration right after that tick, at the
time `c`), and is the confirmed tip or an ancestor of the confirmed tip (`W.anc`) of
every validator `v` honest and active at a slot `s' ≥ s`, in the state every step `j` leaves
 that is `v`'s own tick to the support cutoff of slot
`s' + 1` or a later step, with
`v` outside the adversary set at every time up to the time of that step.

The variables:
- `M`: the model;
- `W`: the vocabulary; `S`: the setup; `Sched`: the schedule; `x`: the trace of views; `tE`: the
  time from which the slots are read.

Read aloud: from `tE`, every honest proposal becomes the confirmed tip of every honest active
validator of its slot and stays confirmed, unless its proposer already held a block with its
root. -/
def ConfirmedIncludedAfterHealingV (tE : ℕ) : Prop :=
  ∀ s : ℕ, tE ≤ M.slotStart S.C s → HonestOpenerAt M S A x s →
    (∃ b : B, ProposalAtV M W S x s b) ∧
    ∀ b : B, ProposalAtV M W S x s b →
      RootCollisionAtProposalV M W S x s b ∨
      ((∀ v ∈ honestActiveAt M S A x s,
          (x.tickOutput v (M.supportCutoff S.C (s + 1))).C = b) ∧
       (∀ (v : V) (j s' : ℕ), A.HonestThroughTime x (x.time j) v → s ≤ s' →
          v ∈ honestActiveAt M S A x s' → x.tickStep v (M.supportCutoff S.C (s' + 1)) ≤ j →
          W.anc b (x.st (j + 1) v).C))

/-! ## The asynchrony statement's conclusions -/

/-- `ConfirmedPersistsBetweenV M W S Sched x s tAwakeEnd b₀ t`: every block `P` that is, after a
step `i` at a time from `tAwakeEnd` to the support cutoff of slot `s + 1`, the confirmed tip of a
validator outside the adversary set at every time up to the time of `i`, or an ancestor of it (`W.anc`), is, after every step `j` at a time
from `b₀` to `t`, the confirmed tip or an ancestor of the confirmed tip of every validator of
`updaterAt M S Sched s` honest through `j`.



Each updater's confirmed tip is read only after its own tick to the hand-over cutoff
: before that tick it is still
the tip its update of slot `s − 1` wrote.

The variables:
- `M`: the model;
- `W`: the vocabulary; `S`: the setup; `Sched`: the schedule; `x`: the trace of views; `s`: the
  hand-over slot; `tAwakeEnd`: the time from which the confirmed tips are protected; `b₀`: the
  start of the asynchronous period; `t`: the time up to which the later steps are read.

Read aloud: every block confirmed by an honest validator from `tAwakeEnd` to the hand-over update,
read once that validator had processed the step's time, stays, from `b₀` up to `t`, an ancestor of
or equal to the confirmed tip of every honest validator that ran that update. -/
def ConfirmedPersistsBetweenV (s tAwakeEnd b₀ t : ℕ) : Prop :=
  ∀ (v : V) (i : ℕ) (P : B),
    A.HonestThroughTime x (x.time i) v → tAwakeEnd ≤ x.time i → x.time i ≤ M.supportCutoff S.C (s + 1) →
    (∀ (t : ℕ), (t : ℝ) ≤ x.time i → ∀ i' : ℕ, i ≤ i' → x.lbl i' ≠ Event.tick v t) →
    W.anc P (x.st i v).C →
    ∀ (v' : V) (j : ℕ), x.HonestThrough A j v' → v' ∈ updaterAt M S A x s →
      x.tickStep v' (M.supportCutoff S.C (s + 1)) < j → 
      b₀ ≤ x.time j → x.time j ≤ t → W.anc P (x.st j v').C

/-- `FinalizedCompatibleBetweenV M W S Sched x s tAwakeEnd b₀ t`: every block `P` that is, after a
step `i` at a time from `tAwakeEnd` to the support cutoff of slot `s + 1`, the confirmed tip of a
validator outside the adversary set at every time up to the time of `i`, or an ancestor of it, is compatible (`W.Compatible`) with the
finalized block of every validator honest through any step `j` at a time from `b₀` to `t`.



The variables:
- `M`: the model;
- `W`: the vocabulary; `S`: the setup; `Sched`: the schedule; `x`: the trace of views; `s`: the
  hand-over slot; `tAwakeEnd`: the time from which the confirmed tips are protected; `b₀`: the
  start of the asynchronous period; `t`: the time up to which the later steps are read.

Read aloud: from `b₀` up to `t`, no honest validator finalizes a block conflicting with what was
confirmed from `tAwakeEnd` to the hand-over update, read once the confirming validator had
processed the step's time. -/
def FinalizedCompatibleBetweenV (s tAwakeEnd b₀ t : ℕ) : Prop :=
  ∀ (v : V) (i : ℕ) (P : B),
    A.HonestThroughTime x (x.time i) v → tAwakeEnd ≤ x.time i → x.time i ≤ M.supportCutoff S.C (s + 1) →
    (∀ (t : ℕ), (t : ℝ) ≤ x.time i → ∀ i' : ℕ, i ≤ i' → x.lbl i' ≠ Event.tick v t) →
    W.anc P (x.st i v).C →
    ∀ (v' : V) (j : ℕ), x.HonestThrough A j v' → b₀ ≤ x.time j → x.time j ≤ t →
      W.Compatible P (x.st j v').F

/-- `ConfirmedPersistsFromV M W S Sched x s tAwakeEnd b₀`: `ConfirmedPersistsBetweenV` with no upper
end: every block `P` that is, after a step `i` at a time from `tAwakeEnd` to the support cutoff of
slot `s + 1`, the confirmed tip of a validator outside the adversary set at every time up to the time of `i`, or an ancestor of it, is, after
every step `j` at a time at least `b₀`, the confirmed tip or an ancestor of the confirmed tip of
every validator of `updaterAt M S Sched s` honest through `j`.



Each updater's confirmed tip is read only after its own tick to the hand-over cutoff
: before that tick it is still
the tip its update of slot `s − 1` wrote.

The variables:
- `M`: the model;
- `W`: the vocabulary; `S`: the setup; `Sched`: the schedule; `x`: the trace of views; `s`: the
  hand-over slot; `tAwakeEnd`: the time from which the confirmed tips are protected; `b₀`: the
  start of the asynchronous period.

Read aloud: every block confirmed by an honest validator from `tAwakeEnd` to the hand-over update,
read once that validator had processed the step's time, stays, from `b₀` on, an ancestor of or
equal to the confirmed tip of every honest validator that ran that update. -/
def ConfirmedPersistsFromV (s tAwakeEnd b₀ : ℕ) : Prop :=
  ∀ (v : V) (i : ℕ) (P : B),
    A.HonestThroughTime x (x.time i) v → tAwakeEnd ≤ x.time i → x.time i ≤ M.supportCutoff S.C (s + 1) →
    (∀ (t : ℕ), (t : ℝ) ≤ x.time i → ∀ i' : ℕ, i ≤ i' → x.lbl i' ≠ Event.tick v t) →
    W.anc P (x.st i v).C →
    ∀ (v' : V) (j : ℕ), x.HonestThrough A j v' → v' ∈ updaterAt M S A x s →
      x.tickStep v' (M.supportCutoff S.C (s + 1)) < j → 
      b₀ ≤ x.time j → W.anc P (x.st j v').C

/-- `FinalizedCompatibleFromV M W S Sched x s tAwakeEnd b₀`: `FinalizedCompatibleBetweenV` with no
upper end: every block `P` that is, after a step `i` at a time from `tAwakeEnd` to the support
cutoff of slot `s + 1`, the confirmed tip of a validator outside the adversary set at every time up to the time of `i`, or an ancestor of it,
is compatible with the finalized block of every validator honest through any step `j` at a time at
least `b₀`.



The variables:
- `M`: the model;
- `W`: the vocabulary; `S`: the setup; `Sched`: the schedule; `x`: the trace of views; `s`: the
  hand-over slot; `tAwakeEnd`: the time from which the confirmed tips are protected; `b₀`: the
  start of the asynchronous period.

Read aloud: from `b₀` on, no honest validator finalizes a block conflicting with what was confirmed
from `tAwakeEnd` to the hand-over update, read once the confirming validator had processed the
step's time. -/
def FinalizedCompatibleFromV (s tAwakeEnd b₀ : ℕ) : Prop :=
  ∀ (v : V) (i : ℕ) (P : B),
    A.HonestThroughTime x (x.time i) v → tAwakeEnd ≤ x.time i → x.time i ≤ M.supportCutoff S.C (s + 1) →
    (∀ (t : ℕ), (t : ℝ) ≤ x.time i → ∀ i' : ℕ, i ≤ i' → x.lbl i' ≠ Event.tick v t) →
    W.anc P (x.st i v).C →
    ∀ (v' : V) (j : ℕ), x.HonestThrough A j v' → b₀ ≤ x.time j →
      W.Compatible P (x.st j v').F

/-! ## Lemma 98's conclusion -/

/-- `FinalityIncludedBetweenV M W S Sched x tE t`: for every slot `s` starting at or after `tE` with
`HonestOpenerAt M S Sched s`, and every round `r` with `s ≤ r * R`, `FinalityWindowAt M S Sched r`
and the update of slot `(r + 3) * R` at most `t`:
slot `s` has a proposal; and every
proposal `b` of slot `s` either carries the root of a block its proposer held when the run moved to
the start of slot `s`, or one of the proposals of the rounds `r` to `r + 3` carries the root of a
block its proposer held (`RootCollisionAtOpeningV`), or every validator `v` outside the adversary set at every time up to the time of a step `j` at or before some support cutoff at most `t` (some slot `s'` with
`x[j].time ≤ M.supportCutoff S.C s' ≤ t`), that ticks, at a step at or before `j`, to a clock value at least one whole delay or one whole sync delay,
whichever is longer, after some natural `τ` at or after the start of slot `(r + 3) * R`, is awake at every step
from the real time `τ` up to that tick, and had ticked earlier to a clock value at least that start and at least
one delay before that clock value, has after step `j` a finalized block of which `b` is an
ancestor or which is `b` (`W.anc`), and which no validator had as its finalized block after a step
at a time before the start of slot `s`.

The variables:
- `M`: the model;
- `W`: the vocabulary; `S`: the setup; `Sched`: the schedule; `x`: the trace of views; `tE`: the
  time from which the slots are read; `t`: the time that decides the readers: a reader's step is at
  or before some support cutoff at most `t`.

Read aloud: from `tE`, for the readers whose step is at or before some support cutoff at most `t`,
whenever four consecutive honest round opening slots with quorums at the first three follow an
honest proposal, and the update of the fourth opening slot is at most `t`, everyone awake from a time
at or after the fourth opening slot's start up to its own tick a delay later has finalized that proposal or a descendant of it, a block no
validator had finalized before the proposal, unless a root collision hit one of the five
proposals. -/
def FinalityIncludedBetweenV (Δs tE t : ℕ) : Prop :=
  ∀ (s r : ℕ), tE ≤ M.slotStart S.C s → HonestOpenerAt M S A x s → s ≤ r * S.C.R →
    FinalityWindowAt M S A x r → M.supportCutoff S.C ((r + 3) * S.C.R + 1) ≤ t →
    (∃ b : B, ProposalAtV M W S x s b) ∧
    ∀ b : B, ProposalAtV M W S x s b →
      RootCollisionAtProposalV M W S x s b ∨
      RootCollisionAtOpeningV M W S x (fun i => r + i) 3 ∨
      ∀ (v : V) (j : ℕ), A.HonestThroughTime x (x.time j) v →
        (∃ s' : ℕ, x.time j ≤ M.supportCutoff S.C s' ∧ M.supportCutoff S.C s' ≤ t) →
        AwakeForDelayWithin S A x Δs v (M.slotStart S.C ((r + 3) * S.C.R)) j →
        W.anc b (x.st j v).F ∧
        ∀ (v' : V) (i' : ℕ), x.time i' < M.slotStart S.C s → (x.st i' v').F ≠ (x.st j v).F

/-- `FinalityIncludedAfterHealingV M W S Sched x tE`: `FinalityIncludedBetweenV` with no upper end.
For every slot `s` starting at or after `tE` with `HonestOpenerAt M S Sched s`, and every round `r`
with `s ≤ r * R` and `FinalityWindowAt M S Sched r`: slot `s` has a proposal; and every proposal `b`
of slot `s` either carries the root of a block its proposer held when the run moved to the start of
slot `s`, or one of the proposals of the rounds `r` to `r + 3` carries the root of a block its
proposer held (`RootCollisionAtOpeningV`), or every validator `v` outside the adversary set at every time up to the time of a step `j`, that ticks, at a step at or before `j`, to a clock value at least one whole delay or one whole sync delay,
whichever is longer, after some natural `τ` at or after the start of slot `(r + 3) * R`, is awake at every step
from the real time `τ` up to that tick, and had ticked earlier to a clock value at least that start and at least
one delay before that clock value, has after step
`j` a finalized block of which `b` is an ancestor or which is `b` (`W.anc`), and which no validator
had as its finalized block after a step at a time before the start of slot `s`.

The variables:
- `M`: the model;
- `W`: the vocabulary; `S`: the setup; `Sched`: the schedule; `x`: the trace of views; `tE`: the
  time from which the slots are read.

Read aloud: from `tE`, whenever four consecutive honest round opening slots with quorums at the
first three follow an honest proposal, everyone awake from a time
at or after the fourth opening slot's start up to its own tick a delay later
has finalized that proposal or a descendant of it, a block no validator had finalized before the
proposal, unless a root collision hit one of the five proposals. -/
def FinalityIncludedAfterHealingV (Δs tE : ℕ) : Prop :=
  ∀ (s r : ℕ), tE ≤ M.slotStart S.C s → HonestOpenerAt M S A x s → s ≤ r * S.C.R →
    FinalityWindowAt M S A x r →
    (∃ b : B, ProposalAtV M W S x s b) ∧
    ∀ b : B, ProposalAtV M W S x s b →
      RootCollisionAtProposalV M W S x s b ∨
      RootCollisionAtOpeningV M W S x (fun i => r + i) 3 ∨
      ∀ (v : V) (j : ℕ), A.HonestThroughTime x (x.time j) v →
        AwakeForDelayWithin S A x Δs v (M.slotStart S.C ((r + 3) * S.C.R)) j →
        W.anc b (x.st j v).F ∧
        ∀ (v' : V) (i' : ℕ), x.time i' < M.slotStart S.C s → (x.st i' v').F ≠ (x.st j v).F

end GoldilocksCorrectness.Record.Statements.View

