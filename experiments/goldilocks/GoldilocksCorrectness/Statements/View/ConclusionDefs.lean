module
public import GoldilocksCorrectness.Statements.View.NodeViewDefs

@[expose] public section

/-!
# The conclusions read on a run's views, for any protocol

The conclusions of the top statements that read only the views (`NodeView B`), the times and the
schedule, stated for any protocol over a trace whose node states are views, with the blocks
compared through a vocabulary `W : ViewVocab V B M`:

- `FinalizedCompatibleUpToV`: Lemma 86's conclusion read up to a time;
- `ConfirmedAgreeBetweenV`, `ConfirmedMonotoneBetweenV`: Lemma 90's agreement and growth read
  between two times, and `ConfirmedAgreeAfterHealingV`, `ConfirmedMonotoneAfterHealingV`: the two
  with no upper end;
- `InHonestTreeByV`, `RootCollisionHeldByV`: a block held by an honest validator by a time, and two
  distinct such blocks carrying the same root.

This page imports only the sts framework, the vocabulary and the view page, so that it reads no
protocol. The conclusions that read a protocol's slots are on `SlotConclusionDefs.lean`.
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Statements.View

open Framework.StsMultisetLog (Schedule)
open GoldilocksCorrectness.Statements.Network

variable {V B M Ev : Type} (W : ViewVocab V B M) (Sched : Schedule V)
  (x : Trace V M (NodeView B) Ev)

/-- `FinalizedCompatibleUpToV W Sched x t`: for every two validators `v₁`, `v₂` and steps `i`, `j`
at times at most `t`, with `v₁` outside the adversary set at every time up to the time of step `i`
and `v₂` at every time up to the time of step `j`, `v₁`'s finalized block after `i` steps and
`v₂`'s after `j` steps are compatible (`W.Compatible`).

The variables:
- `W`: the vocabulary; `Sched`: the schedule; `x`: the trace of views; `t`: the time up to which
  the steps are read.

Read aloud: up to `t`, two honest validators never hold conflicting finalized blocks. -/
def FinalizedCompatibleUpToV (t : ℕ) : Prop :=
  ∀ (v₁ v₂ : V) (i j : ℕ), HonestThroughV Sched x i v₁ → HonestThroughV Sched x j v₂ →
    x[i].time ≤ t → x[j].time ≤ t →
    W.Compatible x[i][v₁].st.F x[j][v₂].st.F

/-- `ConfirmedAgreeBetweenV W Sched x tE t`: for every two validators `v₁`, `v₂` and steps `i`, `j`
at times at least `tE` and at most `t`, with `v₁` outside the adversary set at every time up to the
time of step `i` and `v₂` at every time up to the time of step `j`, `v₁`'s confirmed tip after `i`
steps and `v₂`'s after `j` steps are compatible (`W.Compatible`).

The variables:
- `W`: the vocabulary; `Sched`: the schedule; `x`: the trace of views; `tE`: the time from which
  the agreement holds; `t`: the time up to which the steps are read.

Read aloud: from `tE` up to `t`, the confirmed tips of two honest validators are on one chain. -/
def ConfirmedAgreeBetweenV (tE t : ℕ) : Prop :=
  ∀ (v₁ v₂ : V) (i j : ℕ), HonestThroughV Sched x i v₁ → HonestThroughV Sched x j v₂ →
    tE ≤ x[i].time → tE ≤ x[j].time → x[i].time ≤ t → x[j].time ≤ t →
    W.Compatible x[i][v₁].st.C x[j][v₂].st.C

/-- `ConfirmedMonotoneBetweenV W Sched x tE t`: for every validator `v` and steps `i ≤ j` with the
time of step `i` at least `tE`, the time of step `j` at most `t`, and `v` outside the adversary set
at every time up to the time of step `j`, `v`'s confirmed tip after `i` steps is its confirmed tip
after `j` steps or an ancestor of it (`W.anc`).

The variables:
- `W`: the vocabulary; `Sched`: the schedule; `x`: the trace of views; `tE`: the time from which
  the growth holds; `t`: the time up to which the later step is read.

Read aloud: from `tE` up to `t`, an honest validator's confirmed tip only extends. -/
def ConfirmedMonotoneBetweenV (tE t : ℕ) : Prop :=
  ∀ (v : V) (i j : ℕ), i ≤ j → HonestThroughV Sched x j v → tE ≤ x[i].time → x[j].time ≤ t →
    W.anc x[i][v].st.C x[j][v].st.C

/-- `ConfirmedAgreeAfterHealingV W Sched x tE`: `ConfirmedAgreeBetweenV` with no upper end. For
every two validators `v₁`, `v₂` and steps `i`, `j` at times at least `tE`, with `v₁` outside the
adversary set at every time up to the time of step `i` and `v₂` at every time up to the time of
step `j`, `v₁`'s confirmed tip after `i` steps and `v₂`'s after `j` steps are compatible
(`W.Compatible`).

The variables:
- `W`: the vocabulary; `Sched`: the schedule; `x`: the trace of views; `tE`: the time from which
  the agreement holds.

Read aloud: from `tE` on, the confirmed tips of two honest validators are on one chain. -/
def ConfirmedAgreeAfterHealingV (tE : ℕ) : Prop :=
  ∀ (v₁ v₂ : V) (i j : ℕ), HonestThroughV Sched x i v₁ → HonestThroughV Sched x j v₂ →
    tE ≤ x[i].time → tE ≤ x[j].time →
    W.Compatible x[i][v₁].st.C x[j][v₂].st.C

/-- `ConfirmedMonotoneAfterHealingV W Sched x tE`: `ConfirmedMonotoneBetweenV` with no upper end.
For every validator `v` and steps `i ≤ j` with the time of step `i` at least `tE` and `v` outside
the adversary set at every time up to the time of step `j`, `v`'s confirmed tip after `i` steps is
its confirmed tip after `j` steps or an ancestor of it (`W.anc`).

The variables:
- `W`: the vocabulary; `Sched`: the schedule; `x`: the trace of views; `tE`: the time from which
  the growth holds.

Read aloud: from `tE` on, an honest validator's confirmed tip only extends. -/
def ConfirmedMonotoneAfterHealingV (tE : ℕ) : Prop :=
  ∀ (v : V) (i j : ℕ), i ≤ j → HonestThroughV Sched x j v → tE ≤ x[i].time →
    W.anc x[i][v].st.C x[j][v].st.C

/-- `InHonestTreeByV Sched x t b`: some validator holds the block `b` after some step of `x` whose
time is at most `t`, and is outside the adversary set at that step's time.

The variables:
- `Sched`: the schedule; `x`: the trace of views; `t`: the bound on the time; `b`: the block.

Read aloud: an honest validator holds `b` at some step at a time at most `t`. -/
def InHonestTreeByV (t : ℕ) (b : B) : Prop :=
  ∃ (i : ℕ) (v : V), v ∉ Sched.adv (x[i].time : Int) ∧ x[i].time ≤ t ∧ b ∈ x[i][v].st.T

/-- `RootCollisionHeldByV W Sched x t`: two distinct blocks that honest validators hold at steps at
times at most `t` carry the same root (`W.sameRoot`).

The variables:
- `W`: the vocabulary; `Sched`: the schedule; `x`: the trace of views; `t`: the bound on the time.

Read aloud: by the time `t`, a root collision has hit two blocks honest validators hold. -/
def RootCollisionHeldByV (t : ℕ) : Prop :=
  ∃ b b' : B, InHonestTreeByV Sched x t b ∧ InHonestTreeByV Sched x t b' ∧ W.sameRoot b b' ∧
    b ≠ b'

end GoldilocksCorrectness.Statements.View
