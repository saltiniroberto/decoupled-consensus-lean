module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.SleepyDefs
public import GoldilocksCorrectness.Statements.Executions.FinalityWindowDefs

@[expose] public section

/-!
# FinalityWindowDefs, over a model

The definitions of `GoldilocksCorrectness/Statements/Executions/FinalityWindowDefs.lean` over a
model `M`: a slot's proposer awake and honest from its proposal window to the slot's update, a
quorum of honest active validators, and the finality window, read at the model's times.
`AwakeForDelayWithin` reads no time of the model; the twins read the landed one.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ slotStart supportCutoff proposalWindowStart)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V)

open Classical in
/-- `HonestOpenerAt M S A x s`: the proposer of slot `s` ticks to the support cutoff of slot `s + 1` and either
has been active (awake and outside the adversary set) after every step up to that tick, or ticked, after its
last restart, to a clock value at most the protocol's proposal window start of slot `s`,
`proposal_window_start S.C s`, and stayed active up to its tick to the cutoff; and it is outside the adversary
set after every step whose time is at most that cutoff or at most the real time of its own tick to
the cutoff. It is the per-slot premise
`ConfirmedIncludedAfterHealing` spells out, given a name; when `s` is the first slot of a round, `s` is an
honest round opening slot.

The first conjunct is the reader `A.activeThroughoutToTick` of the sets `activeAt`, `updaterAt`: the condition
the protocol's proposal test reads at the proposer's tick to the slot's start (its stored wake time at most the
proposal window's start), kept up to the update. It reads steps and clock values only.

The variables:
- `M`: the model;
- `S`: the setup; `A`: the activity; `x`: the trace; `s`: the slot.

Read aloud: the proposer of `s` ticks to the support cutoff of slot `s + 1` and either has been awake and
honest since the trace's start, or ticked, after its last restart, to a clock value at most the protocol's
proposal window start of `s` and stayed awake and honest up to that tick; and it is outside the adversary set
at every step whose time is at most that cutoff, at every step whose time is at most the real time of its own
tick to that cutoff, and at every step at which an honest validator ticks to that cutoff
. -/
def HonestOpenerAt (S : Setup V) (A : Activity V) {Msg N : Type} (x : Trace V Msg N) (s : ℕ) : Prop :=
  S.P.proposer s ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C s)
      (M.supportCutoff S.C (s + 1)) ∧
    S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) ∪
      A.corruptedAtTime x (x.time (x.tickStep (S.P.proposer s) (M.supportCutoff S.C (s + 1)))) ∪
      Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
        x.lbl k = Event.tick w (M.supportCutoff S.C (s + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k)

/-- `QuorumActiveAt M S Sched s`: at least `quorum V` validators are in `honestActiveAt M S Sched s`
(awake from `M.dutyWindowStart S.C s` through `M.supportCutoff S.C (s + 1)`, outside the adversary
set at that cutoff).

The variables:
- `M`: the model;
- `S`: the setup; `Sched`: the schedule; `s`: the slot.

Read aloud: a quorum of validators runs slot `s`'s duties honestly, the attestation of the round
whose first slot is `s` included. -/
def QuorumActiveAt (S : Setup V) (A : Activity V) {Msg N : Type} (x : Trace V Msg N) (s : ℕ) : Prop :=
  quorum V ≤ |honestActiveAt M S A x s|

/-- `FinalityWindowAt M S Sched r`: for the four consecutive rounds `r`, `r + 1`, `r + 2`, `r + 3`,
each first slot `(r + i) * R` has `HonestOpenerAt`, and the first three have `QuorumActiveAt`.

The variables:
- `M`: the model;
- `S`: the setup; `Sched`: the schedule; `r`: the first round of the window.

Read aloud: four consecutive honest round opening slots, the proposer of each awake and honest from
its proposal window to its slot's update, with a quorum of honest active validators at the first
three. -/
def FinalityWindowAt (S : Setup V) (A : Activity V) {Msg N : Type} (x : Trace V Msg N) (r : ℕ) : Prop :=
  (∀ i : ℕ, i < 4 → HonestOpenerAt M S A x ((r + i) * S.C.R)) ∧
  (∀ i : ℕ, i < 3 → QuorumActiveAt M S A x ((r + i) * S.C.R))

end GoldilocksCorrectness.Record.Statements.Executions

