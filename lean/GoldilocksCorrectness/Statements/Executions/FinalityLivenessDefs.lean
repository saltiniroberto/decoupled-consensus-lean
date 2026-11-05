module
public import GoldilocksCorrectness.Statements.Executions.FinalityWindowDefs
public import GoldilocksCorrectness.Statements.Executions.Lemma89Defs
public import GoldilocksCorrectness.Proofs.Routines.Schedule

@[expose] public section

/-!
# The conditions of finality liveness after healing

The definitions the finality-liveness statements read (`FinalityLivenessStatements.lean`), beside
`HonestOpenerAt`, `QuorumActiveAt`, `FinalityWindowAt` and `AwakeForDelayWithin`, which are on
`FinalityWindowDefs.lean`:

- `FinalityIncludedBetween S Sched x Δw tE t`, from `tE`, every honest proposal followed by a
  window of `FinalityWindowAt` whose last opening slot is updated by `t` is an ancestor of, or
  equal to, the finalized block of every validator awake for `max (Δ S) Δw` after the window's last
  opening slot whose step is at or before some support cutoff at most `t`, and that finalized block
  is one no validator had as its finalized block before the proposal;
- `FinalityIncludedAfterHealing S Sched x Δw tE`, the same with no upper end, and
  `finalityIncludedAfterHealing_iff`, that it is the bounded form at every time;
- `FinalizedExtendedByHonestProposalsBetween S Sched x Δw tE t`, under the same conditions, the
  readers' finalized blocks strictly extend every finalized block a validator honest through its
  step had from `tE` until the proposal's slot started;



-/

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ slotStart supportCutoff proposalWindowStart)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V]

section Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction SignedMsg)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.View

variable [RootOrder]

/-- `FinalityIncludedBetween S Sched x Δw tE t`: for every slot `s` starting at or after `tE` with
`HonestOpenerAt S Sched s`, and every round `r` with `s ≤ r * R`, `FinalityWindowAt S Sched r` and
the update of the window's last opening slot `(r + 3) * R` at most `t`
: the proposer's tick at
the start of slot `s` puts some block on the wire; and for every block `B` that tick puts on the
wire, either a block the proposer held before the start of slot `s` has `B`'s root
(`RootCollisionAtProposal`), or one of the four rounds' proposals has the root of a block its
proposer held (`RootCollisionAtOpening` on the rounds `r, r + 1, r + 2, r + 3`), or every
validator `v` honest through a step `j` at or before some support cutoff at most `t`, awake for
`max (Δ S) Δw` between the start of slot `(r + 3) * R` and the time of step `j`, has at step `j` a
finalized block `S.F` of which `B` is an ancestor or which is `B`, and which no validator had as
its finalized block at a step at a time before the start of slot `s`.

 The window and the reader are the
restated statement's; the reading with every reader whose step
is at a time at most `t` is `FinalityIncludedBetweenEveryReader`.

Defined as its view form: `FinalityIncludedBetweenV` with
Goldilocks's vocabulary `Vocab.goldilocks`, on the view of `x`, `projectTrace nodeView x.toTrace`,
whose node states are read as each validator's finalized block, confirmed tip (`confirmedOf`) and
held blocks. `finalityIncludedBetween_unfold` (`Proofs/View/Bridges.lean`) reads it on the
execution's node states.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Δw`: the catch-up delay, which with
  `Δ S` sets how long a reader is awake (`AwakeForDelayWithin`); `tE`: the time from which the
  slots are read; `t`: the time that decides the rounds and the readers;
- `s`: the slot of the proposal; `r`: the window's first round; `i`: the step of the proposer's
  tick; `B`: the proposal; `v`, `j`: a reader and its step; `u`, `i'`: a validator and an earlier
  step.

Read aloud: from `tE`, for the readers whose step is at or before some support cutoff at most `t`,
whenever four consecutive honest round opening slots with quorums at the first three follow an
honest proposal, and the update of the fourth opening slot is at most `t`, everyone awake for a
delay after the fourth opening slot has finalized that proposal or a descendant of it, a block no
validator had finalized before the proposal, unless a root collision hit one of the five
proposals. -/
def FinalityIncludedBetween (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (Δw tE t : ℕ) : Prop :=
  FinalityIncludedBetweenV Vocab.goldilocks S Sched (projectTrace nodeView x.toTrace) Δw tE t

/-- For every slot `s` starting at or after `tE` with `HonestOpenerAt S Sched s`, and every
round `r` with `s ≤ r * R`, `FinalityWindowAt S Sched r` and the support cutoff of the window's last
opening slot `(r + 3) * R` at most `t`: the proposer's tick at the start of slot `s` puts some block
on the wire; and for every block `B` that tick puts on the wire, either a block the proposer held
before the start of slot `s` has `B`'s root (`RootCollisionAtProposal`), or one of the four rounds'
proposals has the root of a block its proposer held (`RootCollisionAtOpening` on the rounds
`r, r + 1, r + 2, r + 3`), or every validator `v` honest through a step `j` at a time at most `t`,
awake for `max (Δ S) Δw` between the start of slot `(r + 3) * R` and the time of step `j`, has at
step `j` a finalized block `S.F` of which `B` is an ancestor or which is `B`, and which no validator
had as its finalized block at a step at a time before the start of slot `s`.

At the same `t` it reads every round and every reader `FinalityIncludedBetween` reads, and more:
the rounds whose fourth opening slot's support cutoff is at most `t` while the next slot's is after
`t`, and the readers whose step has no support cutoff between it and `t`. It is the first
conclusion of `lem98_healed_finality_liveness_everyReader`.

Defined as its view form: `FinalityIncludedBetweenEveryReaderV` with Goldilocks's vocabulary
`Vocab.goldilocks`, on the view of `x`, `projectTrace nodeView x.toTrace`.
`finalityIncludedBetweenEveryReader_unfold` (`Proofs/View/Bridges.lean`) reads it on the
execution's node states.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Δw`: the catch-up delay, which with
  `Δ S` sets how long a reader is awake (`AwakeForDelayWithin`); `tE`: the time from which the
  slots are read; `t`: the time up to which the readers' steps are read.

Read aloud: from `tE` and up to `t`, whenever four consecutive honest round opening slots with
quorums at the first three follow an honest proposal, everyone awake for a delay after the fourth
opening slot has finalized that proposal or a descendant of it, a block no validator had
finalized before the proposal, unless a root collision hit one of the five proposals. -/
def FinalityIncludedBetweenEveryReader (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (Δw tE t : ℕ) : Prop :=
  FinalityIncludedBetweenEveryReaderV Vocab.goldilocks S Sched (projectTrace nodeView x.toTrace) Δw
    tE t

/-- `FinalityIncludedAfterHealing S Sched x Δw tE`: `FinalityIncludedBetween S Sched x Δw tE t` with
no upper end: for every slot `s` starting at or after `tE` with `HonestOpenerAt S Sched s`, and
every round `r` with `s ≤ r * R` and `FinalityWindowAt S Sched r`, the proposer of `s` puts some
block on the wire at its tick at the start of `s`, and every such block `B` has a root collision at
one of the five proposals, or is an ancestor of, or equal to, the finalized block of every validator
honest through a step and awake for `max (Δ S) Δw` between the start of slot `(r + 3) * R` and that
step's time, a finalized block no validator had at a step before the start of slot `s`.

Defined as its view form: `FinalityIncludedAfterHealingV` with
Goldilocks's vocabulary `Vocab.goldilocks`, on the view of `x`, `projectTrace nodeView x.toTrace`,
whose node states are read as each validator's finalized block, confirmed tip (`confirmedOf`) and
held blocks. `finalityIncludedAfterHealing_unfold` (`Proofs/View/Bridges.lean`) reads it on the
execution's node states.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Δw`: the catch-up delay, which with
  `Δ S` sets how long a reader is awake (`AwakeForDelayWithin`); `tE`: the time from which the
  slots are read.

Read aloud: from `tE`, whenever four consecutive honest round opening slots with quorums at the
first three follow an honest proposal, everyone awake for a delay after the fourth has finalized a
new block at or after that proposal, unless a root collision hit one of the five proposals. -/
def FinalityIncludedAfterHealing (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (Δw tE : ℕ) : Prop :=
  FinalityIncludedAfterHealingV Vocab.goldilocks S Sched (projectTrace nodeView x.toTrace) Δw tE

/-- `FinalityIncludedAfterHealing S Sched x tE` holds exactly when
`FinalityIncludedBetween S Sched x tE t` holds for every time `t`.

Why: one way, the upper ends are dropped. The other way, the proposal comes from the time
`t := supportCutoff S ((r + 3) * R + 1)`, the update of the window's last opening slot, and the
reader's step `j` from the time `t := supportCutoff S n` with
`n := max x[j].time ((r + 3) * R + 1)`: the support cutoff of slot `n` is at or after the step (the
support cutoff of a slot is at least the slot, `supportCutoff_eq`) and at or after the update of the
window's last opening slot, so it is the support cutoff after the step that the reader condition
of `FinalityIncludedBetween` asks for, and it meets the window condition
.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tE`: the time from which the slots
  are read.

Read aloud: finality from `tE` is finality read up to every time. -/
theorem finalityIncludedAfterHealing_iff (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (tE : ℕ) :
    FinalityIncludedAfterHealing S Sched x (Δ S) tE ↔
      ∀ t : ℕ, FinalityIncludedBetween S Sched x (Δ S) tE t := by
  constructor
  · intro h t s r hs hop hsr hwin _
    obtain ⟨h1, h2⟩ := h s r hs hop hsr hwin
    refine ⟨h1, fun B hB => ?_⟩
    rcases h2 B hB with hc | hc | h3
    · exact Or.inl hc
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr (fun v j hv _ hAw => h3 v j hv hAw))
  · intro h s r hs hop hsr hwin
    obtain ⟨h1, -⟩ := h (supportCutoff S ((r + 3) * S.C.R + 1)) s r hs hop hsr hwin le_rfl
    refine ⟨h1, fun B hB => ?_⟩
    by_cases hc : RootCollisionAtProposal S Sched x s B
    · exact Or.inl hc
    by_cases hc' : RootCollisionAtOpening S Sched x (fun i => r + i) 3
    · exact Or.inr (Or.inl hc')
    right; right
    intro v j hv hAw
    -- the support cutoff of slot `max x[j].time ((r + 3) * R + 1)`: after the step and the window
    have key : ∀ n : ℕ, n ≤ supportCutoff S n := fun n => by
      have h1 := GoldilocksCorrectness.Proofs.Routines.supportCutoff_eq S n
      have h2 := GoldilocksCorrectness.Proofs.Routines.voteTime_eq S n
      have h3 := GoldilocksCorrectness.Proofs.Routines.slotStart_eq S n
      have h4 : 1 * n ≤ 4 * Δ S * n := Nat.mul_le_mul_right n
        (by have := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S; omega)
      omega
    have hjn : x[j].time ≤ supportCutoff S (max x[j].time ((r + 3) * S.C.R + 1)) :=
      le_trans (le_max_left _ _) (key _)
    rcases (h (supportCutoff S (max x[j].time ((r + 3) * S.C.R + 1))) s r hs hop hsr hwin
        (GoldilocksCorrectness.Proofs.Routines.supportCutoff_mono S (le_max_right _ _))).2 B hB
      with h₁ | h₁ | h₁
    · exact absurd h₁ hc
    · exact absurd h₁ hc'
    · exact h₁ v j hv ⟨_, hjn, le_rfl⟩ hAw

/-- `FinalizedExtendedByHonestProposalsBetween S Sched x Δw tE t`: Lemma 98's second conclusion
. For every slot `s` starting at or after `tE` with
`HonestOpenerAt S Sched s`, and every round `r` with `s ≤ r * R`, `FinalityWindowAt S Sched r` and
the update of the window's last opening slot `(r + 3) * R` at most `t`
, and for every block `B` the proposer's tick
at the start of slot `s` puts on the wire: either a block the proposer held before the start of
slot `s` has `B`'s root (`RootCollisionAtProposal`), or one of the four rounds' proposals has the
root of a block its proposer held (`RootCollisionAtOpening` on the rounds `r, r + 1, r + 2,
r + 3`), or every validator `v` honest through a step `j` at or before some support cutoff at most
`t`, awake for
`max (Δ S) Δw` between the start of slot `(r + 3) * R` and the time of step `j`, has at step `j` a
finalized block `S.F` that strictly extends the finalized block of every validator `w` at every step
`i` at a time from `tE` to before the start of slot `s` through which `w` has been honest: `w`'s
finalized block is an ancestor of `v`'s other than `v`'s.

The window and the reader are the restated statement's; the
reading with every reader whose step is at a time at most `t` is
`FinalizedExtendedByHonestProposalsBetweenEveryReader`.

Defined as its view form: `FinalizedExtendedByHonestProposalsBetweenV` with
Goldilocks's vocabulary `Vocab.goldilocks`, on the view of `x`, `projectTrace nodeView x.toTrace`.
`finalizedExtendedByHonestProposalsBetween_unfold`
(`Proofs/Executions/HonestProposalExtension.lean`) reads it on the execution's node states.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Δw`: the catch-up delay, which with
  `Δ S` sets how long a reader is awake (`AwakeForDelayWithin`); `tE`: the time from which the
  slots are read; `t`: the time that decides the rounds and the readers.

Read aloud: from `tE`, for the readers whose step is at or before some support cutoff at most `t`,
whenever four consecutive honest round opening slots with quorums at the first three follow an
honest proposal, and the update of the fourth is at most `t`, everyone awake for a delay after the
fourth has a finalized block that strictly extends every finalized block an honest validator had
from `tE` until the proposal's slot started, unless a root collision hit one of the five
proposals. -/
def FinalizedExtendedByHonestProposalsBetween (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (Δw tE t : ℕ) : Prop :=
  FinalizedExtendedByHonestProposalsBetweenV Vocab.goldilocks S Sched
    (projectTrace nodeView x.toTrace) Δw tE t

/-- For every slot `s` starting at or after `tE` with
`HonestOpenerAt S Sched s`, and every round `r` with `s ≤ r * R`, `FinalityWindowAt S Sched r` and
the support cutoff of the window's last opening slot `(r + 3) * R` at most `t`, and for every block
`B` the proposer's tick at the start of slot `s` puts on the wire: either a block the proposer held
before the start of slot `s` has `B`'s root (`RootCollisionAtProposal`), or one of the four rounds'
proposals has the root of a block its proposer held (`RootCollisionAtOpening` on the rounds
`r, r + 1, r + 2, r + 3`), or every validator `v` honest through a step `j` at a time at most `t`,
awake for `max (Δ S) Δw` between the start of slot `(r + 3) * R` and the time of step `j`, has at
step `j` a finalized block `S.F` that strictly extends the finalized block of every validator `w`
at every step `i` at a time from `tE` to before the start of slot `s` through which `w` has been
honest: `w`'s finalized block is an ancestor of `v`'s other than `v`'s.

At the same `t` it reads every round and every reader
`FinalizedExtendedByHonestProposalsBetween` reads, and more: the rounds whose fourth opening slot's
support cutoff is at most `t` while the next slot's is after `t`, and the readers whose step has no
support cutoff between it and `t`. It is the second conclusion of
`lem98_healed_finality_liveness_everyReader`.

Defined as its view form: `FinalizedExtendedByHonestProposalsBetweenEveryReaderV` with Goldilocks's
vocabulary `Vocab.goldilocks`, on the view of `x`, `projectTrace nodeView x.toTrace`.
`finalizedExtendedByHonestProposalsBetweenEveryReader_unfold`
(`Proofs/Executions/HonestProposalExtension.lean`) reads it on the execution's node states.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Δw`: the catch-up delay, which with
  `Δ S` sets how long a reader is awake (`AwakeForDelayWithin`); `tE`: the time from which the
  slots are read; `t`: the time up to which the readers' steps are read.

Read aloud: from `tE` and up to `t`, whenever four consecutive honest round opening slots with
quorums at the first three follow an honest proposal, everyone awake for a delay after the fourth
has a finalized block that strictly extends every finalized block an honest validator had from
`tE` until the proposal's slot started, unless a root collision hit one of the five proposals. -/
def FinalizedExtendedByHonestProposalsBetweenEveryReader (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (Δw tE t : ℕ) : Prop :=
  FinalizedExtendedByHonestProposalsBetweenEveryReaderV Vocab.goldilocks S Sched
    (projectTrace nodeView x.toTrace) Δw tE t

end Executions

end GoldilocksCorrectness.Statements.Executions
