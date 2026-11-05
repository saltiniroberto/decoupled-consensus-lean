module
public import GoldilocksCorrectness.Statements.AbstractTrace.TraceDefs
public import GoldilocksCorrectness.Statements.View.NodeViewDefs
public import GoldilocksCorrectness.Statements.Executions.FinalityWindowDefs

@[expose] public section

/-!
# The view predicates, over a trace

The conclusions the top statements read, stated over a trace of views `x : Trace V M (NodeView B)` and
an activity `A`: the twins of the predicates of `GoldilocksCorrectness/Statements/View/ConclusionDefs.lean`
and `GoldilocksCorrectness/Statements/View/SlotConclusionDefs.lean`, which read the sts framework's run
and schedule, with the activity's readings in place of the schedule's. A record statement reads them at
`x.map (nodeView M)`.

The page defines, in this order:
- the schedule readings at the spec's times that the slot conclusions read, on the activity: the
  validators awake through a slot's duties (`activeAt`), those of them honest at its update
  (`honestActiveAt`), the validators running a slot's update (`updaterAt`), an honest round opening slot
  (`HonestOpenerAt`), a quorum active at a slot (`QuorumActiveAt`), a finality window
  (`FinalityWindowAt`), and a validator awake for one delay inside an interval (`AwakeForDelayWithin`);
- a step's block send (`PutsBlockV`);
- the conclusions: finalized compatibility, confirmed agreement and growth, blocks held by honest
  validators and root collisions, a slot's proposal (the proposer's own tick to the start of the slot),
  Lemma 90's inclusion, the asynchrony statement's persistence, Lemma 98's finality.

This page reads no protocol.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart
  proposalWindowStart)

namespace GoldilocksCorrectness.Statements.AbstractTrace.View

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity)
open GoldilocksCorrectness.Statements.Network (ViewVocab)
open GoldilocksCorrectness.Statements.View (NodeView)
open Framework.StsMultisetLog (SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)

/-! ## The activity at the spec's times -/

section Activity

variable {V : Type} [DecidableEq V] [Fintype V] {Msg N : Type}

/-- `activeAt S A x s`: the validators counted awake throughout the interval from the duty window's
start of slot `s` to the support cutoff of slot `s + 1`, where their confirmation update that
evaluates slot `s` runs.

The variables:
- `S`: the setup; `A`: the schedule; `x`: the trace; `s`: the slot.

Read aloud: the validators awake through the duties of slot `s`. -/
noncomputable def activeAt (S : Setup V) (A : Activity V) (x : Trace V Msg N) (s : ℕ) : Finset V :=
  A.awakeThroughout x (dutyWindowStart S s) (supportCutoff S (s + 1))

/-- `honestActiveAt S A x s`: the validators of `activeAt S A x s` outside the adversary set after
every step whose time is the support cutoff of slot `s + 1`.

The variables:
- `S`: the setup; `A`: the schedule; `x`: the trace; `s`: the slot.

Read aloud: the validators awake through the duties of slot `s` and honest at its update. -/
noncomputable def honestActiveAt (S : Setup V) (A : Activity V) (x : Trace V Msg N) (s : ℕ) :
    Finset V :=
  activeAt S A x s \ A.corruptedAtTime x (supportCutoff S (s + 1))

/-- `updaterAt S A x s`: the validators counted awake throughout the interval from the duty
window's start of slot `s + 1` to the support cutoff of slot `s + 1`, the window of the confirmation
update that evaluates slot `s`, and outside the adversary set after every step whose time is that
cutoff.

The variables:
- `S`: the setup; `A`: the schedule; `x`: the trace; `s`: the slot the update evaluates.

Read aloud: the validators awake and honest through the update of slot `s`. -/
noncomputable def updaterAt (S : Setup V) (A : Activity V) (x : Trace V Msg N) (s : ℕ) :
    Finset V :=
  A.awakeThroughout x (dutyWindowStart S (s + 1)) (supportCutoff S (s + 1)) \
    A.corruptedAtTime x (supportCutoff S (s + 1))

/-- `HonestOpenerAt S A x s`: the proposer of slot `s` is counted active throughout the interval from
`proposalWindowStart S s` to `supportCutoff S (s + 1)`. When `s` is the first slot of a round, `s`
is an honest round opening slot.

The variables:
- `S`: the setup; `A`: the schedule; `x`: the trace; `s`: the slot.

Read aloud: the proposer of `s` is awake and honest from its proposal window to the slot's
update. -/
def HonestOpenerAt (S : Setup V) (A : Activity V) (x : Trace V Msg N) (s : ℕ) : Prop :=
  S.P.proposer s ∈ A.activeThroughout x (proposalWindowStart S s) (supportCutoff S (s + 1))

/-- `QuorumActiveAt S A x s`: at least `quorum V` validators are in `honestActiveAt S A x s`.

The variables:
- `S`: the setup; `A`: the schedule; `x`: the trace; `s`: the slot.

Read aloud: a quorum of validators runs slot `s`'s duties honestly, the attestation of the round
whose first slot is `s` included. -/
def QuorumActiveAt (S : Setup V) (A : Activity V) (x : Trace V Msg N) (s : ℕ) : Prop :=
  quorum V ≤ |honestActiveAt S A x s|

/-- `FinalityWindowAt S A x r`: for the four consecutive rounds `r`, `r + 1`, `r + 2`, `r + 3`,
each first slot `(r + i) * R` has `HonestOpenerAt`, and the first three have `QuorumActiveAt`.

The variables:
- `S`: the setup; `A`: the schedule; `x`: the trace; `r`: the first round of the window.

Read aloud: four consecutive honest round opening slots, the proposer of each awake and honest from
its proposal window to its slot's update, with a quorum of honest active validators at the first
three. -/
def FinalityWindowAt (S : Setup V) (A : Activity V) (x : Trace V Msg N) (r : ℕ) : Prop :=
  (∀ i : ℕ, i < 4 → HonestOpenerAt S A x ((r + i) * S.C.R)) ∧
  (∀ i : ℕ, i < 3 → QuorumActiveAt S A x ((r + i) * S.C.R))

/-- `AwakeForDelayWithin S A x Δs v t j`: for some natural `τ ≥ t`, `v` ticks, at a step `k` at or
before step `j`, to a clock value `c` at least `τ + max (Δ S) Δs`, is counted awake at every step from
the real time `τ` up to step `k`, and had ticked, at a step `k₂`, to a clock value `c₂` with `t ≤ c₂`
and `c₂ + Δ S ≤ c`.

The variables:
- `S`: the setup; `A`: the schedule; `x`: the trace; `Δs`: the sync delay; `v`: the validator; `t`:
  the real time the interval starts at or after; `j`: the step at or before which `v`'s tick is.

Read aloud: between `t` and step `j`, `v` ticks to a clock value one whole delay or one whole sync
delay, whichever is longer, after some natural `τ ≥ t`, at a step at or before `j`, having been awake
at every step from the real time `τ` up to that tick, and had ticked earlier to a clock value at least
`t` and at least one delay before that clock value. -/
def AwakeForDelayWithin (S : Setup V) (A : Activity V) (x : Trace V Msg N) (Δs : ℕ) (v : V)
    (t : ℝ) (j : ℕ) : Prop :=
  ∃ τ c c₂ k k₂ : ℕ, t ≤ τ ∧ τ + max (Δ S) Δs ≤ c ∧ x.lbl k = Event.tick v c ∧ k ≤ j ∧
    (∀ i : ℕ, (τ : ℝ) ≤ x.time i → i ≤ k → v ∈ A.awake i) ∧
    x.lbl k₂ = Event.tick v c₂ ∧ t ≤ c₂ ∧ c₂ + Δ S ≤ c

end Activity

/-! ## A step's block send -/

section Reading

variable {Node Msg St : Type}

/-- `PutsBlockV W x i v b`: the step `i` of `x` adds to the sent log a message signed by `v` that
carries the block `b` (`W.blockOf`).

The variables:
- `W`: the vocabulary; `x`: the trace; `i`: the step; `v`: the signer; `b`: the block.

Read aloud: at the step `i`, `v` puts the block `b` on the wire. -/
def PutsBlockV {B : Type} [DecidableEq Node] [DecidableEq Msg] (W : ViewVocab Node B Msg)
    (x : Trace Node Msg St) (i : ℕ) (v : Node) (b : B) : Prop :=
  ∃ sm ∈ x.sent (i + 1) - x.sent i, sm.sender = v ∧ W.blockOf sm.msg = some b

end Reading

/-! ## The conclusions -/

section Conclusions

variable {V B M : Type} [DecidableEq V] (W : ViewVocab V B M) (A : Activity V)
  (x : Trace V M (NodeView B))

/-- `FinalizedCompatibleUpToV W A x t`: for every two validators `v₁`, `v₂` and steps `i`, `j`
at times at most `t`, with `v₁` outside the adversary set at every time up to the time of step `i`
and `v₂` at every time up to the time of step `j`, `v₁`'s finalized block after `i` steps and
`v₂`'s after `j` steps are compatible (`W.Compatible`).

The variables:
- `W`: the vocabulary; `A`: the schedule; `x`: the trace of views; `t`: the time up to which
  the steps are read.

Read aloud: up to `t`, two honest validators never hold conflicting finalized blocks. -/
def FinalizedCompatibleUpToV (t : ℕ) : Prop :=
  ∀ (v₁ v₂ : V) (i j : ℕ), x.HonestThrough A i v₁ → x.HonestThrough A j v₂ →
    x.time i ≤ t → x.time j ≤ t →
    W.Compatible (x.st i v₁).F (x.st j v₂).F

/-- `ConfirmedAgreeBetweenV W A x tE t`: for every two validators `v₁`, `v₂` and steps `i`, `j`
at times at least `tE` and at most `t`, with `v₁` outside the adversary set at every time up to the
time of step `i` and `v₂` at every time up to the time of step `j`, `v₁`'s confirmed tip in the
state step `i` leaves and `v₂`'s in the state step `j` leaves are compatible (`W.Compatible`).

The state read for a step is the one the step leaves, `x.st (i + 1)`, read at the step's own time
`x.time i`: the state a tick leaves is read at the tick's real time.

The variables:
- `W`: the vocabulary; `A`: the schedule; `x`: the trace of views; `tE`: the time from which
  the agreement holds; `t`: the time up to which the steps are read.

Read aloud: from `tE` up to `t`, the confirmed tips of two honest validators are on one chain. -/
def ConfirmedAgreeBetweenV (tE : ℝ) (t : ℕ) : Prop :=
  ∀ (v₁ v₂ : V) (i j : ℕ), A.HonestThroughTime x (x.time i) v₁ → A.HonestThroughTime x (x.time j) v₂ →
    tE ≤ x.time i → tE ≤ x.time j → x.time i ≤ t → x.time j ≤ t →
    W.Compatible (x.st (i + 1) v₁).C (x.st (j + 1) v₂).C

/-- `ConfirmedMonotoneBetweenV W A x tE t`: for every validator `v` and steps `i ≤ j` with the
time of step `i` at least `tE`, the time of step `j` at most `t`, and `v` outside the adversary set
at every time up to the time of step `j`, `v`'s confirmed tip in the state step `i` leaves is its
confirmed tip in the state step `j` leaves or an ancestor of it (`W.anc`).

The state read for a step is the one the step leaves, `x.st (i + 1)`, read at the step's own time
`x.time i`: the state a tick leaves is read at the tick's real time.

The variables:
- `W`: the vocabulary; `A`: the schedule; `x`: the trace of views; `tE`: the time from which
  the growth holds; `t`: the time up to which the later step is read.

Read aloud: from `tE` up to `t`, an honest validator's confirmed tip only extends. -/
def ConfirmedMonotoneBetweenV (tE : ℝ) (t : ℕ) : Prop :=
  ∀ (v : V) (i j : ℕ), i ≤ j → A.HonestThroughTime x (x.time j) v → tE ≤ x.time i → x.time j ≤ t →
    W.anc (x.st (i + 1) v).C (x.st (j + 1) v).C

/-- `ConfirmedAgreeAfterHealingV W A x tE`: `ConfirmedAgreeBetweenV` with no upper end. For
every two validators `v₁`, `v₂` and steps `i`, `j` at times at least `tE`, with `v₁` outside the
adversary set at every time up to the time of step `i` and `v₂` at every time up to the time of
step `j`, `v₁`'s confirmed tip in the state step `i` leaves and `v₂`'s in the state step `j` leaves
are compatible (`W.Compatible`).

The state read for a step is the one the step leaves, `x.st (i + 1)`, read at the step's own time
`x.time i`: the state a tick leaves is read at the tick's real time.

The variables:
- `W`: the vocabulary; `A`: the schedule; `x`: the trace of views; `tE`: the time from which
  the agreement holds.

Read aloud: from `tE` on, the confirmed tips of two honest validators are on one chain. -/
def ConfirmedAgreeAfterHealingV (tE : ℕ) : Prop :=
  ∀ (v₁ v₂ : V) (i j : ℕ), A.HonestThroughTime x (x.time i) v₁ → A.HonestThroughTime x (x.time j) v₂ →
    tE ≤ x.time i → tE ≤ x.time j →
    W.Compatible (x.st (i + 1) v₁).C (x.st (j + 1) v₂).C

/-- `ConfirmedMonotoneAfterHealingV W A x tE`: `ConfirmedMonotoneBetweenV` with no upper end.
For every validator `v` and steps `i ≤ j` with the time of step `i` at least `tE` and `v` outside
the adversary set at every time up to the time of step `j`, `v`'s confirmed tip in the state step
`i` leaves is its confirmed tip in the state step `j` leaves or an ancestor of it (`W.anc`).

The state read for a step is the one the step leaves, `x.st (i + 1)`, read at the step's own time
`x.time i`: the state a tick leaves is read at the tick's real time.

The variables:
- `W`: the vocabulary; `A`: the schedule; `x`: the trace of views; `tE`: the time from which
  the growth holds.

Read aloud: from `tE` on, an honest validator's confirmed tip only extends. -/
def ConfirmedMonotoneAfterHealingV (tE : ℕ) : Prop :=
  ∀ (v : V) (i j : ℕ), i ≤ j → A.HonestThroughTime x (x.time j) v → tE ≤ x.time i →
    W.anc (x.st (i + 1) v).C (x.st (j + 1) v).C

/-- `InHonestTreeByV A x t b`: some validator holds the block `b` in the state some step `i` of `x`
leaves (`x.st (i + 1) v`), where step `i` is at a time at most `t` and the validator is outside the
adversary set at step `i`.

The variables:
- `A`: the schedule; `x`: the trace of views; `t`: the bound on the time; `b`: the block.

Read aloud: an honest validator holds `b` right after some step at a time at most `t`. -/
def InHonestTreeByV (t : ℕ) (b : B) : Prop :=
  ∃ (i : ℕ) (v : V), v ∉ A.corrupted i ∧ x.time i ≤ t ∧ b ∈ (x.st (i + 1) v).T

/-- `RootCollisionHeldByV W A x t`: two distinct blocks that honest validators hold at steps at
times at most `t` carry the same root (`W.sameRoot`).

The variables:
- `W`: the vocabulary; `A`: the schedule; `x`: the trace of views; `t`: the bound on the time.

Read aloud: by the time `t`, a root collision has hit two blocks honest validators hold. -/
def RootCollisionHeldByV (t : ℕ) : Prop :=
  ∃ b b' : B, InHonestTreeByV A x t b ∧ InHonestTreeByV A x t b' ∧ W.sameRoot b b' ∧
    b ≠ b'

end Conclusions

section SlotConclusions

variable {V : Type} [DecidableEq V] [Fintype V] {B M : Type} [DecidableEq M]
  (W : ViewVocab V B M) (S : Setup V) (A : Activity V) (x : Trace V M (NodeView B))

/-- `ProposalAtV W S x s b`: the proposer of slot `s` puts the block `b` on the wire at its own
tick to the start of slot `s`.

The variables:
- `W`: the vocabulary; `S`: the setup; `x`: the trace of views; `s`: the slot; `b`: the block.

Read aloud: `b` is slot `s`'s proposal. -/
def ProposalAtV (s : ℕ) (b : B) : Prop :=
  ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer s) (slotStart S s) ∧
    PutsBlockV W x i (S.P.proposer s) b

/-- `RootCollisionAtProposalV W S x s b`: some block the proposer of slot `s` holds when the run
moves to the start of slot `s` carries the root of `b` (`W.sameRoot`).

The variables:
- `W`: the vocabulary; `S`: the setup; `x`: the trace of views; `s`: the slot; `b`: the
  proposal.

Read aloud: a block the proposer held before the proposal's slot has the proposal's root. -/
def RootCollisionAtProposalV (s : ℕ) (b : B) : Prop :=
  ∃ b' ∈ (x.stateBefore (slotStart S s) (S.P.proposer s)).T, W.sameRoot b' b

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

/-- `ConfirmedIncludedBetweenV W S A x tE t`: for every slot `s` starting at or after `tE` whose
support cutoff of slot `s + 1` is at most `t`, and whose proposer is awake and outside the
adversary set at every time from the start of its proposal window to that support cutoff
(`HonestOpenerAt`): slot `s` has a proposal; and every proposal `b` of slot `s` either carries the
root of a block its proposer held when the run moved to the start of slot `s`, or is the confirmed
tip of every honest active validator of slot `s` when the run moves to the time after the support
cutoff of slot `s + 1`, and is the confirmed tip or an ancestor of the confirmed tip (`W.anc`) of
every validator `v` honest and active at a slot `s' ≥ s`, at every step `j` at a time after the
support cutoff of slot `s' + 1` and at most `t` with `v` outside the adversary set at every time up to the time of that step.

The variables:
- `W`: the vocabulary; `S`: the setup; `A`: the schedule; `x`: the trace of views; `tE`: the
  time from which the slots are read; `t`: the time up to which the updates and the confirmed
  tips are read.

Read aloud: from `tE` and up to `t`, every honest proposal becomes the confirmed tip of every
honest active validator of its slot and stays confirmed, unless its proposer already held a block
with its root. -/
def ConfirmedIncludedBetweenV (tE t : ℕ) : Prop :=
  ∀ s : ℕ, tE ≤ slotStart S s → supportCutoff S (s + 1) ≤ t → HonestOpenerAt S A x s →
    (∃ b : B, ProposalAtV W S x s b) ∧
    ∀ b : B, ProposalAtV W S x s b →
      RootCollisionAtProposalV W S x s b ∨
      ((∀ v ∈ honestActiveAt S A x s, (x.stateBefore (supportCutoff S (s + 1) + 1) v).C = b) ∧
       (∀ (v : V) (j s' : ℕ), A.HonestThroughTime x (x.time j) v → s ≤ s' →
          v ∈ honestActiveAt S A x s' → supportCutoff S (s' + 1) < x.time j → x.time j ≤ t →
          W.anc b (x.st j v).C))

/-- `ConfirmedIncludedAfterHealingV W S A x tE`: `ConfirmedIncludedBetweenV` with no upper end. For
every slot `s` starting at or after `tE` whose proposer is awake and outside the adversary set at
every time from the start of its proposal window to the support cutoff of slot `s + 1`
(`HonestOpenerAt`): slot `s` has a proposal; and every proposal `b` of slot `s` either carries the
root of a block its proposer held when the run moved to the start of slot `s`, or is the confirmed
tip of every honest active validator of slot `s` when the run moves to the time after the support
cutoff of slot `s + 1`, and is the confirmed tip or an ancestor of the confirmed tip (`W.anc`) of
every validator `v` honest and active at a slot `s' ≥ s`, at every step `j` at a time after the
support cutoff of slot `s' + 1` with `v` outside the adversary set at every time up to the time of that step.

The variables:
- `W`: the vocabulary; `S`: the setup; `A`: the schedule; `x`: the trace of views; `tE`: the
  time from which the slots are read.

Read aloud: from `tE`, every honest proposal becomes the confirmed tip of every honest active
validator of its slot and stays confirmed, unless its proposer already held a block with its
root. -/
def ConfirmedIncludedAfterHealingV (tE : ℕ) : Prop :=
  ∀ s : ℕ, tE ≤ slotStart S s → HonestOpenerAt S A x s →
    (∃ b : B, ProposalAtV W S x s b) ∧
    ∀ b : B, ProposalAtV W S x s b →
      RootCollisionAtProposalV W S x s b ∨
      ((∀ v ∈ honestActiveAt S A x s, (x.stateBefore (supportCutoff S (s + 1) + 1) v).C = b) ∧
       (∀ (v : V) (j s' : ℕ), A.HonestThroughTime x (x.time j) v → s ≤ s' →
          v ∈ honestActiveAt S A x s' → supportCutoff S (s' + 1) < x.time j →
          W.anc b (x.st j v).C))

/-- `ConfirmedPersistsBetweenV W S A x s tAwakeEnd b₀ t`: every block `P` that is, after a step
`i` at a time from `tAwakeEnd` to the support cutoff of slot `s + 1`, the confirmed tip of a
validator outside the adversary set at every time up to the time of `i`, or an ancestor of it (`W.anc`), is, after every step `j` at a time
from `b₀` to `t`, the confirmed tip or an ancestor of the confirmed tip of every validator of
`updaterAt S A x s` honest through `j`.

The variables:
- `W`: the vocabulary; `S`: the setup; `A`: the schedule; `x`: the trace of views; `s`: the
  hand-over slot; `tAwakeEnd`: the time from which the confirmed tips are protected; `b₀`: the
  start of the asynchronous period; `t`: the time up to which the later steps are read.

Read aloud: every block confirmed by an honest validator from `tAwakeEnd` to the hand-over update
stays, from `b₀` up to `t`, an ancestor of or equal to the confirmed tip of every honest validator
that ran that update. -/
def ConfirmedPersistsBetweenV (s tAwakeEnd b₀ t : ℕ) : Prop :=
  ∀ (v : V) (i : ℕ) (P : B),
    A.HonestThroughTime x (x.time i) v → tAwakeEnd ≤ x.time i → x.time i ≤ supportCutoff S (s + 1) →
    W.anc P (x.st i v).C →
    ∀ (v' : V) (j : ℕ), x.HonestThrough A j v' → v' ∈ updaterAt S A x s →
      b₀ ≤ x.time j → x.time j ≤ t → W.anc P (x.st j v').C

/-- `FinalizedCompatibleBetweenV W S A x s tAwakeEnd b₀ t`: every block `P` that is, after a
step `i` at a time from `tAwakeEnd` to the support cutoff of slot `s + 1`, the confirmed tip of a
validator outside the adversary set at every time up to the time of `i`, or an ancestor of it, is compatible (`W.Compatible`) with the
finalized block of every validator honest through any step `j` at a time from `b₀` to `t`.

The variables:
- `W`: the vocabulary; `S`: the setup; `A`: the schedule; `x`: the trace of views; `s`: the
  hand-over slot; `tAwakeEnd`: the time from which the confirmed tips are protected; `b₀`: the
  start of the asynchronous period; `t`: the time up to which the later steps are read.

Read aloud: from `b₀` up to `t`, no honest validator finalizes a block conflicting with what was
confirmed from `tAwakeEnd` to the hand-over update. -/
def FinalizedCompatibleBetweenV (s tAwakeEnd b₀ t : ℕ) : Prop :=
  ∀ (v : V) (i : ℕ) (P : B),
    A.HonestThroughTime x (x.time i) v → tAwakeEnd ≤ x.time i → x.time i ≤ supportCutoff S (s + 1) →
    W.anc P (x.st i v).C →
    ∀ (v' : V) (j : ℕ), x.HonestThrough A j v' → b₀ ≤ x.time j → x.time j ≤ t →
      W.Compatible P (x.st j v').F

/-- `ConfirmedPersistsFromV W S A x s tAwakeEnd b₀`: `ConfirmedPersistsBetweenV` with no upper
end: every block `P` that is, after a step `i` at a time from `tAwakeEnd` to the support cutoff of
slot `s + 1`, the confirmed tip of a validator outside the adversary set at every time up to the time of `i`, or an ancestor of it, is, after
every step `j` at a time at least `b₀`, the confirmed tip or an ancestor of the confirmed tip of
every validator of `updaterAt S A x s` honest through `j`.

The variables:
- `W`: the vocabulary; `S`: the setup; `A`: the schedule; `x`: the trace of views; `s`: the
  hand-over slot; `tAwakeEnd`: the time from which the confirmed tips are protected; `b₀`: the
  start of the asynchronous period.

Read aloud: every block confirmed by an honest validator from `tAwakeEnd` to the hand-over update
stays, from `b₀` on, an ancestor of or equal to the confirmed tip of every honest validator that
ran that update. -/
def ConfirmedPersistsFromV (s tAwakeEnd b₀ : ℕ) : Prop :=
  ∀ (v : V) (i : ℕ) (P : B),
    A.HonestThroughTime x (x.time i) v → tAwakeEnd ≤ x.time i → x.time i ≤ supportCutoff S (s + 1) →
    W.anc P (x.st i v).C →
    ∀ (v' : V) (j : ℕ), x.HonestThrough A j v' → v' ∈ updaterAt S A x s →
      b₀ ≤ x.time j → W.anc P (x.st j v').C

/-- `FinalizedCompatibleFromV W S A x s tAwakeEnd b₀`: `FinalizedCompatibleBetweenV` with no
upper end: every block `P` that is, after a step `i` at a time from `tAwakeEnd` to the support
cutoff of slot `s + 1`, the confirmed tip of a validator outside the adversary set at every time up to the time of `i`, or an ancestor of it,
is compatible with the finalized block of every validator honest through any step `j` at a time at
least `b₀`.

The variables:
- `W`: the vocabulary; `S`: the setup; `A`: the schedule; `x`: the trace of views; `s`: the
  hand-over slot; `tAwakeEnd`: the time from which the confirmed tips are protected; `b₀`: the
  start of the asynchronous period.

Read aloud: from `b₀` on, no honest validator finalizes a block conflicting with what was confirmed
from `tAwakeEnd` to the hand-over update. -/
def FinalizedCompatibleFromV (s tAwakeEnd b₀ : ℕ) : Prop :=
  ∀ (v : V) (i : ℕ) (P : B),
    A.HonestThroughTime x (x.time i) v → tAwakeEnd ≤ x.time i → x.time i ≤ supportCutoff S (s + 1) →
    W.anc P (x.st i v).C →
    ∀ (v' : V) (j : ℕ), x.HonestThrough A j v' → b₀ ≤ x.time j →
      W.Compatible P (x.st j v').F

/-- `FinalityIncludedBetweenV W S A x tE t`: for every slot `s` starting at or after `tE` with
`HonestOpenerAt S A x s`, and every round `r` with `s ≤ r * R`, `FinalityWindowAt S A x r` and
the support cutoff of slot `(r + 3) * R` at most `t`: slot `s` has a proposal; and every proposal
`b` of slot `s` either carries the root of a block its proposer held when the run moved to the
start of slot `s`, or one of the proposals of the rounds `r` to `r + 3` carries the root of a block
its proposer held (`RootCollisionAtOpeningV`), or every validator `v` outside the adversary set at every time up to the time of a step `j` at
a time at most `t`, that ticks, at a step at or before `j`, to a clock value at least one whole delay or one whole sync delay,
whichever is longer, after some natural `τ` at or after the start of slot `(r + 3) * R`, is awake at every step
from the real time `τ` up to that tick, and had ticked earlier to a clock value at least that start and at least
one delay before that clock value, has after step `j` a finalized block of which `b` is an ancestor or which is `b`
(`W.anc`), and which no validator had as its finalized block after a step at a time before the
start of slot `s`.

The variables:
- `W`: the vocabulary; `S`: the setup; `A`: the schedule; `x`: the trace of views; `tE`: the
  time from which the slots are read; `t`: the time up to which the readers' steps are read.

Read aloud: from `tE` and up to `t`, whenever four consecutive honest round opening slots with
quorums at the first three follow an honest proposal, everyone awake from a time
at or after the fourth opening slot's start up to its own tick a delay later has finalized that proposal or a descendant of it, a block no validator had finalized
before the proposal, unless a root collision hit one of the five proposals. -/
def FinalityIncludedBetweenV (Δs tE t : ℕ) : Prop :=
  ∀ (s r : ℕ), tE ≤ slotStart S s → HonestOpenerAt S A x s → s ≤ r * S.C.R →
    FinalityWindowAt S A x r → supportCutoff S ((r + 3) * S.C.R) ≤ t →
    (∃ b : B, ProposalAtV W S x s b) ∧
    ∀ b : B, ProposalAtV W S x s b →
      RootCollisionAtProposalV W S x s b ∨
      RootCollisionAtOpeningV W S x (fun i => r + i) 3 ∨
      ∀ (v : V) (j : ℕ), A.HonestThroughTime x (x.time j) v → x.time j ≤ t →
        AwakeForDelayWithin S A x Δs v (slotStart S ((r + 3) * S.C.R)) j →
        W.anc b (x.st j v).F ∧
        ∀ (v' : V) (i' : ℕ), x.time i' < slotStart S s → (x.st i' v').F ≠ (x.st j v).F

/-- `FinalityIncludedAfterHealingV W S A x tE`: `FinalityIncludedBetweenV` with no upper end.
For every slot `s` starting at or after `tE` with `HonestOpenerAt S A x s`, and every round `r` with
`s ≤ r * R` and `FinalityWindowAt S A x r`: slot `s` has a proposal; and every proposal `b` of
slot `s` either carries the root of a block its proposer held when the run moved to the start of
slot `s`, or one of the proposals of the rounds `r` to `r + 3` carries the root of a block its
proposer held (`RootCollisionAtOpeningV`), or every validator `v` outside the adversary set at every time up to the time of a step `j`, that ticks, at a step at or before `j`, to a clock value at least one whole delay or one whole sync delay,
whichever is longer, after some natural `τ` at or after the start of slot `(r + 3) * R`, is awake at every step
from the real time `τ` up to that tick, and had ticked earlier to a clock value at least that start and at least
one delay before that clock value, has after
step `j` a finalized block of which `b` is an ancestor or which is `b` (`W.anc`), and which no
validator had as its finalized block after a step at a time before the start of slot `s`.

The variables:
- `W`: the vocabulary; `S`: the setup; `A`: the schedule; `x`: the trace of views; `tE`: the
  time from which the slots are read.

Read aloud: from `tE`, whenever four consecutive honest round opening slots with quorums at the
first three follow an honest proposal, everyone awake from a time
at or after the fourth opening slot's start up to its own tick a delay later
has finalized that proposal or a descendant of it, a block no validator had finalized before the
proposal, unless a root collision hit one of the five proposals. -/
def FinalityIncludedAfterHealingV (Δs tE : ℕ) : Prop :=
  ∀ (s r : ℕ), tE ≤ slotStart S s → HonestOpenerAt S A x s → s ≤ r * S.C.R →
    FinalityWindowAt S A x r →
    (∃ b : B, ProposalAtV W S x s b) ∧
    ∀ b : B, ProposalAtV W S x s b →
      RootCollisionAtProposalV W S x s b ∨
      RootCollisionAtOpeningV W S x (fun i => r + i) 3 ∨
      ∀ (v : V) (j : ℕ), A.HonestThroughTime x (x.time j) v →
        AwakeForDelayWithin S A x Δs v (slotStart S ((r + 3) * S.C.R)) j →
        W.anc b (x.st j v).F ∧
        ∀ (v' : V) (i' : ℕ), x.time i' < slotStart S s → (x.st i' v').F ≠ (x.st j v).F

end SlotConclusions

end GoldilocksCorrectness.Statements.AbstractTrace.View
