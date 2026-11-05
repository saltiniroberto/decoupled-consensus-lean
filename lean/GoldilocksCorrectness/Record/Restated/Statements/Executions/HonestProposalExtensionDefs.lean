module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ConfirmedTipDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.FinalityLivenessDefs

@[expose] public section

/-!

- the view forms, on a trace of views and an activity, at the model's times:
  `ConfirmedExtendedByHonestProposalsBetweenV`, `ConfirmedExtendedByHonestProposalsV`,
  `FinalizedExtendedByHonestProposalsBetweenV`;
- the forms on a trace of the model's node states, each its view form on the view
  `x.map (nodeView M)` with Goldilocks's vocabulary: `ConfirmedExtendedByHonestProposals`,
  `ConfirmedExtendedByHonestProposalsBetween`, `FinalizedExtendedByHonestProposalsBetween`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.View

open GoldilocksCorrectness.Statements.View (NodeView)
open GoldilocksCorrectness.Record.Statements.Executions (HonestOpenerAt FinalityWindowAt)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity)
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Network
open GoldilocksCorrectness.Statements.AbstractTrace.View (AwakeForDelayWithin)

variable {V : Type} [DecidableEq V] [Fintype V] {B Msg : Type} [DecidableEq Msg]
variable (M : GoldilocksModel V)
variable (W : ViewVocab V B Msg) (S : Setup V) (A : Activity V) (x : Trace V Msg (NodeView B))

/-- `ConfirmedExtendedByHonestProposalsBetweenV M W S A x tE t`: for every slot `s` starting at or
after `tE` whose support cutoff of slot `s + 1` is at most `t` and whose proposer's tick to that
cutoff is at a step whose time is at most `t`, and whose
proposer is awake and
outside the adversary set at every time from the start of its proposal window to that support cutoff
(`HonestOpenerAt`): every proposal `b` of slot `s` either carries the root of a block its proposer
held when the run moved to the start of slot `s`, or is a strict descendant of the confirmed tip of
every validator `v` in the state every step `i` leaves, with `v`
outside the adversary set at every time up to the time of `i`, at a time from `tE` on, when `v`'s
own clock value in that state (`x.clockValue (i + 1) v`) is less than the start of slot `s`
: that confirmed tip is an ancestor of `b` or `b` (`W.anc`), and is not `b`.

The variables:
- `M`: the model;
- `W`: the vocabulary; `S`: the setup; `A`: the activity; `x`: the trace of views; `tE`: the time
  from which the slots are read; `t`: the time up to which the updates are read.

Read aloud: from `tE` and up to `t`, every honest proposal strictly extends every confirmed tip
an honest validator had from `tE` on while its own clock was before the proposal's slot, unless its proposer already
held a block with its root. -/
def ConfirmedExtendedByHonestProposalsBetweenV (tE t : ℕ) : Prop :=
  ∀ s : ℕ, tE ≤ M.slotStart S.C s → M.supportCutoff S.C (s + 1) ≤ t →
    (x.time (x.tickStep (S.P.proposer s) (M.supportCutoff S.C (s + 1))) : ℝ) ≤ t →
    HonestOpenerAt M S A x s →
    ∀ b : B, ProposalAtV M W S x s b →
      RootCollisionAtProposalV M W S x s b ∨
      ∀ (v : V) (i : ℕ), A.HonestThroughTime x (x.time i) v → tE ≤ x.time i →
        x.clockValue (i + 1) v < M.slotStart S.C s → W.anc (x.st (i + 1) v).C b ∧ (x.st (i + 1) v).C ≠ b

/-- `ConfirmedExtendedByHonestProposalsV M W S A x tE`: `ConfirmedExtendedByHonestProposalsBetweenV`
with no upper end. For every slot `s` starting at or after `tE` whose proposer is awake and outside
the adversary set at every time from the start of its proposal window to the support cutoff of slot
`s + 1` (`HonestOpenerAt`): every proposal `b` of slot `s` either carries the root of a block its
proposer held when the run moved to the start of slot `s`, or is a strict descendant of the
confirmed tip of every validator `v` in the state every step `i` leaves,
with `v` outside the adversary set at every time up to the time of `i`, at a time from `tE` on, when
`v`'s own clock value in that state (`x.clockValue (i + 1) v`) is less than the start of slot `s`
: that confirmed tip is an ancestor of `b` or `b` (`W.anc`), and is not `b`.

The variables:
- `M`: the model;
- `W`: the vocabulary; `S`: the setup; `A`: the activity; `x`: the trace of views; `tE`: the time
  from which the slots are read.

Read aloud: from `tE`, every honest proposal strictly extends every confirmed tip an honest
validator had from `tE` on while its own clock was before the proposal's slot, unless its proposer already held a
block with its root. -/
def ConfirmedExtendedByHonestProposalsV (tE : ℕ) : Prop :=
  ∀ s : ℕ, tE ≤ M.slotStart S.C s → HonestOpenerAt M S A x s →
    ∀ b : B, ProposalAtV M W S x s b →
      RootCollisionAtProposalV M W S x s b ∨
      ∀ (v : V) (i : ℕ), A.HonestThroughTime x (x.time i) v → tE ≤ x.time i →
        x.clockValue (i + 1) v < M.slotStart S.C s → W.anc (x.st (i + 1) v).C b ∧ (x.st (i + 1) v).C ≠ b

/-- `FinalizedExtendedByHonestProposalsBetweenV M W S A x Δs tE t`: for every slot `s` starting at or
after `tE` with `HonestOpenerAt M S A x s`, and every round `r` with `s ≤ r * R`,
`FinalityWindowAt M S A x r` and the update of slot `(r + 3) * R` at most `t`: every proposal `b` of slot `s` either carries the root of a block its proposer held when the run moved to the start
of slot `s`, or one of the proposals of the rounds `r` to `r + 3` carries the root of a block its
proposer held (`RootCollisionAtOpeningV`), or every validator `v` outside the adversary set at every time up to the time of a step `j` at or
before some support cutoff at most `t` (some slot `s'` with `x[j].time ≤ M.supportCutoff S.C s' ≤
t`), that ticks, at a step at or before `j`, to a clock value at least one whole delay or one whole sync delay,
whichever is longer, after some natural `τ` at or after the start of slot `(r + 3) * R`, is awake at every step
from the real time `τ` up to that tick, and had ticked earlier to a clock value at least that start and at least
one delay before that clock value, has
after step `j` a finalized block that strictly extends the finalized block of every validator `w`
after every step `i` through which `w` has been honest, at a time from `tE` on, after which `w`'s own clock value
(`x.clockValue i w`) is less than the start of slot `s`: `w`'s finalized block is an ancestor of `v`'s or `v`'s (`W.anc`), and is not `v`'s.

The variables:
- `M`: the model;
- `W`: the vocabulary; `S`: the setup; `A`: the activity; `x`: the trace of views; `tE`: the time
  from which the slots are read; `t`: the time that decides the readers: a reader's step is at or
  before some support cutoff at most `t`.

Read aloud: from `tE`, for the readers whose step is at or before some support cutoff at most `t`,
whenever four consecutive honest round opening slots with quorums at the first three follow an
honest proposal, and the update of the fourth opening slot is at most `t`, everyone awake from a time
at or after the fourth opening slot's start up to its own tick a delay later has a finalized block that strictly extends every finalized block an honest validator had from `tE` on while its own clock was before the proposal's
slot, unless a root collision hit one of the five proposals. -/
def FinalizedExtendedByHonestProposalsBetweenV (Δs tE t : ℕ) : Prop :=
  ∀ (s r : ℕ), tE ≤ M.slotStart S.C s → HonestOpenerAt M S A x s → s ≤ r * S.C.R →
    FinalityWindowAt M S A x r → M.supportCutoff S.C ((r + 3) * S.C.R + 1) ≤ t →
    ∀ b : B, ProposalAtV M W S x s b →
      RootCollisionAtProposalV M W S x s b ∨
      RootCollisionAtOpeningV M W S x (fun i => r + i) 3 ∨
      ∀ (v : V) (j : ℕ), A.HonestThroughTime x (x.time j) v →
        (∃ s' : ℕ, x.time j ≤ M.supportCutoff S.C s' ∧ M.supportCutoff S.C s' ≤ t) →
        AwakeForDelayWithin S A x Δs v (M.slotStart S.C ((r + 3) * S.C.R)) j →
        ∀ (w : V) (i : ℕ), x.HonestThrough A i w → tE ≤ x.time i →
          x.clockValue i w < M.slotStart S.C s →
          W.anc (x.st i w).F (x.st j v).F ∧ (x.st i w).F ≠ (x.st j v).F

end GoldilocksCorrectness.Record.Statements.View

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.View

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)

/-- `ConfirmedExtendedByHonestProposals M S A x tE`: for every slot `s` starting at or after `tE`
whose proposer is awake and outside the adversary set at every time from
`M.proposalWindowStart S.C s` to the support cutoff of slot `s + 1` (`HonestOpenerAt`), and every
block `B` the proposer's tick at the start of slot `s` puts on the wire: either a block the proposer
held before the start of slot `s` has `B`'s root (`RootCollisionAtProposal`), or, for every
validator `v` and every step `i` at a time from `tE` on, after which `v`'s own clock value is less than
the start of slot `s`, through which `v` has been honest, `v`'s confirmed tip (`M.ac_confirmed`) after step `i` is an ancestor of `B`
other than `B`.

Defined as its view form: `ConfirmedExtendedByHonestProposalsV` with Goldilocks's
vocabulary `GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks`, on the view of `x`,
`x.map (nodeView M)`.

The variables:
- `M`: the model;
- `S`: the setup; `A`: the activity; `x`: the trace; `tE`: the time from which the slots are
  read.

Read aloud: from `tE`, every honest proposal strictly extends every confirmed tip an honest
validator had from `tE` on while its own clock was before the proposal's slot, unless its proposer already held a
block with its root. -/
def ConfirmedExtendedByHonestProposals (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (tE : ℕ) : Prop :=
  ConfirmedExtendedByHonestProposalsV M GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks S
    A (x.map (nodeView M)) tE

/-- `ConfirmedExtendedByHonestProposalsBetween M S A x tE t`:
`ConfirmedExtendedByHonestProposals M S A x tE` read up to the time `t`, for the slots `s` whose
update time, the support cutoff of slot `s + 1`, is at most `t`. For every such slot `s` starting at
or after `tE` with `HonestOpenerAt M S A x s`, and every block `B` the proposer's tick at the start of
slot `s` puts on the wire: either a block the proposer held before the start of slot `s` has `B`'s
root (`RootCollisionAtProposal`), or, for every validator `v` and every step `i` at a time from `tE`
on, after which `v`'s own clock value is less than the start of slot `s`, through which
`v` has been honest, `v`'s confirmed tip
(`M.ac_confirmed`) after step `i` is an ancestor of `B` other than `B`.

Defined as its view form: `ConfirmedExtendedByHonestProposalsBetweenV` with
Goldilocks's vocabulary, on the view of `x`, `x.map (nodeView M)`.

The variables:
- `M`: the model;
- `S`: the setup; `A`: the activity; `x`: the trace; `tE`: the time from which the slots are
  read; `t`: the time up to which the updates are read.

Read aloud: from `tE` and up to `t`, every honest proposal strictly extends every confirmed tip an
honest validator had from `tE` on while its own clock was before the proposal's slot, unless its proposer already held
a block with its root. -/
def ConfirmedExtendedByHonestProposalsBetween (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (tE t : ℕ) : Prop :=
  ConfirmedExtendedByHonestProposalsBetweenV M
    GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks S A (x.map (nodeView M)) tE t

/-- `FinalizedExtendedByHonestProposalsBetween M S A x Δs tE t`: Lemma 98's second conclusion
. For every slot `s` starting at or after `tE` with
`HonestOpenerAt M S A x s`, and every round `r` with `s ≤ r * R`, `FinalityWindowAt M S A x r` and the
update of the window's last opening slot `(r + 3) * R` at most `t`, and for every block `B`
the proposer's tick at the start of slot `s` puts on the wire: either a block the proposer held
before the start of slot `s` has `B`'s root (`RootCollisionAtProposal`), or one of the four rounds'
proposals has the root of a block its proposer held (`RootCollisionAtOpening` on the rounds
`r, r + 1, r + 2, r + 3`), or every validator `v` outside the adversary set at every time up to the time of a step `j` at or before some
support cutoff at most `t` (some slot `s'` with `x[j].time ≤ M.supportCutoff S.C s' ≤ t`), awake for
one whole delay between the start of slot `(r + 3) * R` and the time of step `j`, has at step `j` a
finalized block that strictly extends the finalized block of every validator `w` at every step `i`
at a time from `tE` on, after which `w`'s own clock value is less than the start of slot `s`
, through which `w` has been honest: `w`'s
finalized block is an ancestor of `v`'s other than `v`'s.

Defined as its view form: `FinalizedExtendedByHonestProposalsBetweenV` with
Goldilocks's vocabulary, on the view of `x`, `x.map (nodeView M)`.

The variables:
- `M`: the model;
- `S`: the setup; `A`: the activity; `x`: the trace; `tE`: the time from which the slots are
  read; `t`: the time that decides the readers: a reader's step is at or before some support
  cutoff at most `t`.

Read aloud: from `tE`, for the readers whose step is at or before some support cutoff at most `t`,
whenever four consecutive honest round opening slots with quorums at the first three follow an
honest proposal, and the update of the fourth is at most `t`, everyone awake for a delay after the
fourth has a finalized block that strictly extends every finalized block an honest validator had
from `tE` on while its own clock was before the proposal's slot, unless a root collision hit one of the five
proposals. -/
def FinalizedExtendedByHonestProposalsBetween (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (Δs tE t : ℕ) : Prop :=
  FinalizedExtendedByHonestProposalsBetweenV M
    GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks S A (x.map (nodeView M)) Δs tE t

end GoldilocksCorrectness.Record.Statements.Executions
