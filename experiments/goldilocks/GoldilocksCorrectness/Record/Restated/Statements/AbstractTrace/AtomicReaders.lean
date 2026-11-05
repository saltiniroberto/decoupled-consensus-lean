module
public import GoldilocksCorrectness.Record.Wiring
public import GoldilocksCorrectness.Record.ModelSpellings
public import GoldilocksCorrectness.Statements.Executions.ExecutionDefs
public import GoldilocksCorrectness.Statements.Executions.Lemma89Defs

@[expose] public section

/-!
# The sts framework's atomic run: its readers over a model

The readers of an execution `x` of the model's node `protocolOf M S` under the sts framework's atomic
semantics that the bridges of `Record/Restated/Proofs/AbstractTrace/OfAtomic.lean` relate to the
trace `ofAtomic M x`: the step before a time and a validator's node state then (`stepBefore`,
`stateBefore`), the blocks honest validators hold (`inHonestTree`, `inHonestTreeBy`), the node state a
tick starts from (`tickInputState`), and a slot's proposal (`ProposalAt`). The section at the end of
the page states, for each, the equation `goldilocks_<name>`: at the spec's model the reader is the
landed one.

`Record/Restated/Statements/Executions/ExecutionDefs.lean` and
`Record/Restated/Statements/Executions/Lemma89Defs.lean` export these names into their namespace,
`GoldilocksCorrectness.Record.Statements.Executions`, for the record pages that read the atomic run.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ)

namespace GoldilocksCorrectness.Record.Statements.AbstractTrace.Atomic

open Framework.StsMultisetLog (AtomicExec AtomicAction AtomicHonest Schedule SignedMsg entrants)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)

/-! ## Reading the execution -/

section Reading

variable {S : Setup V} {Sched : Schedule V}

open Classical in
/-- `stepBefore M x t`: the step of `x` whose label is the tick of every awake validator at the
time `t`, `tickAllAwake t`, the first one if there were several; `0` when there is none, which is
the case at `t = 0` (the first tick is at `1`) and at a time `x` never reaches. The configuration
`x[stepBefore M x t]` is at the time `t − 1` and holds every step at a time before `t`.

The variables:
- `M`: the model.

Read aloud: the step at which the execution moves to the time `t`. -/
noncomputable def stepBefore (x : AtomicExec (protocolOf M S) Sched) (t : ℕ) : ℕ :=
  if h : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake t then Nat.find h else 0

/-- `stateBefore M x t v`: the node state of the validator `v` in the configuration
`x[stepBefore M x t]`.

The variables:
- `M`: the model.

Read aloud: `v`'s node state after every step of `x` at a time before `t`, the state `v`'s tick at
`t` starts from. -/
noncomputable def stateBefore (x : AtomicExec (protocolOf M S) Sched) (t : ℕ) (v : V) :
    M.N :=
  x[stepBefore M x t][v].st

/-- `inHonestTree M x B`: some validator holds the block `B` in its FG state's tree at some step of
`x`, and is outside the schedule's adversary set at that step's time.

The variables:
- `M`: the model.

Read aloud: an honest validator holds `B` at some point of the execution. -/
def inHonestTree (x : AtomicExec (protocolOf M S) Sched) (B : Block V) : Prop :=
  ∃ (i : ℕ) (v : V), AtomicHonest x i v ∧ B ∈ (x[i][v].st).tree

/-- `inHonestTreeBy M x t B`: some validator holds the block `B` in its FG state's tree at some step
of `x` whose time is at most `t`, and is outside the schedule's adversary set at that step's time.
It is `inHonestTree M x B` with the step's time bounded by `t`.

The variables:
- `M`: the model;
- `x`: the execution; `t`: the bound on the time; `B`: the block.

Read aloud: an honest validator holds `B` at some step at a time at most `t`. -/
def inHonestTreeBy (x : AtomicExec (protocolOf M S) Sched) (t : ℕ) (B : Block V) : Prop :=
  ∃ (i : ℕ) (v : V), AtomicHonest x i v ∧ x[i].time ≤ t ∧ B ∈ (x[i][v].st).tree

/-- `tickInputState M x i t v`: the node state the tick reaction of the validator `v` starts from at
the step `i` of `x`, when that step is the tick of every awake validator at the time `t`. For a
validator entering the awake set at `t` (`entrants Sched t`: awake and outside the adversary set
at `t`, asleep at `t − 1`), its state after the wake reaction, which the sts framework runs at
`v`'s framework clock `x[i][v].clock`: `M.wake x[i][v].st x[i][v].clock`; for any other, its state
`x[i][v].st`.

The variables:
- `M`: the model.

Read aloud: what `v`'s tick at `t` starts from, a validator that has just woken having first
forgotten the time it had been awake since and set its clock to its framework clock. -/
def tickInputState (x : AtomicExec (protocolOf M S) Sched) (i t : ℕ) (v : V) : M.N :=
  if v ∈ entrants Sched t then M.wake x[i][v].st (x[i][v].clock : Int) else x[i][v].st

end Reading

/-! ## A slot's proposal -/

/-- `ProposalAt M S Sched x s B`: the proposer of slot `s` put the block `B` on the wire at its tick
at the start of slot `s`.

The variables:
- `M`: the model.

Read aloud: `B` is slot `s`'s proposal. -/
def ProposalAt (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocolOf M S) Sched)
    (s : ℕ) (B : Block V) : Prop :=
  ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (M.slotStart S.C s) ∧
    (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent

end GoldilocksCorrectness.Record.Statements.AbstractTrace.Atomic

namespace GoldilocksCorrectness.Record.Statements.AbstractTrace.Atomic

open scoped DC
open DC (DRE)
open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)
open Framework.StsMultisetLog (AtomicExec AtomicAction AtomicHonest Schedule SignedMsg entrants)
open Goldilocks
open Goldilocks.Sts (Setup)

/-! ## At the spec's model -/

/-- At the spec's model, `stepBefore` is the landed definition.

The variables:
- as in `stepBefore`, at the spec's model.

Read aloud: the spec's model has the landed `stepBefore`. -/
@[record_goldilocks]
theorem goldilocks_stepBefore {V : Type} [DecidableEq V] [Fintype V] [Goldilocks.RootOrder]
    {S : Setup V} {Sched : Schedule V}
    (x : AtomicExec (GoldilocksCorrectness.Wiring.protocol S) Sched) (t : ℕ) :
    GoldilocksCorrectness.Statements.Executions.stepBefore x t =
      stepBefore Model.goldilocks x t := rfl

/-- At the spec's model, `stateBefore` is the landed definition.

The variables:
- as in `stateBefore`, at the spec's model.

Read aloud: the spec's model has the landed `stateBefore`. -/
@[record_goldilocks]
theorem goldilocks_stateBefore {V : Type} [DecidableEq V] [Fintype V] [Goldilocks.RootOrder]
    {S : Setup V} {Sched : Schedule V}
    (x : AtomicExec (GoldilocksCorrectness.Wiring.protocol S) Sched) (t : ℕ) (v : V) :
    GoldilocksCorrectness.Statements.Executions.stateBefore x t v =
      stateBefore Model.goldilocks x t v := rfl

/-- At the spec's model, `inHonestTree` is the landed definition.

The variables:
- as in `inHonestTree`, at the spec's model.

Read aloud: the spec's model has the landed `inHonestTree`. -/
@[record_goldilocks]
theorem goldilocks_inHonestTree {V : Type} [DecidableEq V] [Fintype V] [Goldilocks.RootOrder]
    {S : Setup V} {Sched : Schedule V}
    (x : AtomicExec (GoldilocksCorrectness.Wiring.protocol S) Sched) (B : Block V) :
    GoldilocksCorrectness.Statements.Executions.inHonestTree x B =
      inHonestTree Model.goldilocks x B := rfl

/-- At the spec's model, `inHonestTreeBy` is the landed definition.

The variables:
- as in `inHonestTreeBy`, at the spec's model.

Read aloud: the spec's model has the landed `inHonestTreeBy`. -/
@[record_goldilocks]
theorem goldilocks_inHonestTreeBy {V : Type} [DecidableEq V] [Fintype V] [Goldilocks.RootOrder]
    {S : Setup V} {Sched : Schedule V}
    (x : AtomicExec (GoldilocksCorrectness.Wiring.protocol S) Sched) (t : ℕ) (B : Block V) :
    GoldilocksCorrectness.Statements.Executions.inHonestTreeBy x t B =
      inHonestTreeBy Model.goldilocks x t B := rfl

/-- At the spec's model, `tickInputState` is the landed definition.

The variables:
- as in `tickInputState`, at the spec's model.

Read aloud: the spec's model has the landed `tickInputState`. -/
@[record_goldilocks]
theorem goldilocks_tickInputState {V : Type} [DecidableEq V] [Fintype V] [Goldilocks.RootOrder]
    {S : Setup V} {Sched : Schedule V}
    (x : AtomicExec (GoldilocksCorrectness.Wiring.protocol S) Sched) (i t : ℕ) (v : V) :
    GoldilocksCorrectness.Statements.Executions.tickInputState x i t v =
      tickInputState Model.goldilocks x i t v := rfl

/-- At the spec's model, `ProposalAt` is the landed definition.

The variables:
- as in `ProposalAt`, at the spec's model.

Read aloud: the spec's model has the landed `ProposalAt`. -/
@[record_goldilocks]
theorem goldilocks_ProposalAt {V : Type} [DecidableEq V] [Fintype V] [Goldilocks.RootOrder]
    (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (GoldilocksCorrectness.Wiring.protocol S) Sched) (s : ℕ) (B : Block V) :
    GoldilocksCorrectness.Statements.Executions.ProposalAt S Sched x s B =
      ProposalAt Model.goldilocks S Sched x s B := by
  simp only [GoldilocksCorrectness.Statements.Executions.ProposalAt, ProposalAt, record_goldilocks]
  rfl

end GoldilocksCorrectness.Record.Statements.AbstractTrace.Atomic

/-! ## The old framework's assumptions and schedule readings over a model

The definitions the record execution pages read over the sts framework's schedule and atomic run
before they were stated over a trace: the tick success of an execution, and the schedule read at a
model's times. `Record/Restated/Proofs/AbstractTrace/OfAtomic.lean` and
`Record/Restated/Statements/AbstractTrace/ScheduleActivity.lean` read them. -/

namespace GoldilocksCorrectness.Record.Statements.AbstractTrace.Atomic

open scoped DC
open DC (DRE)
open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open Framework.StsMultisetLog (AtomicExec AtomicAction AtomicHonest Schedule SignedMsg entrants)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V)

section Assumptions

variable [RootOrder] (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocolOf M S) Sched)

/-- Every honest awake validator's tick answers: at every step that is the tick of every awake
validator at a time `t`, for every validator awake and outside the adversary set at `t`, every
outcome of the model's `tick` at `t` from the node state it starts from (`tickInputState`, the
woken state for a validator that has just woken) is an answer, and an outcome exists.

The variables:
- `M`: the model;
- `x`: the execution; `i`: the step; `t`: the time of the tick; `v`: the validator.

Read aloud: an honest awake validator's tick never fails. -/
def TicksSucceed : Prop :=
  ∀ (i t : ℕ) (v : V), x.lbl i = AtomicAction.tickAllAwake t →
    v ∈ Sched.awake (t : Int) → v ∉ Sched.adv (t : Int) →
      (∀ r ∈ M.tick S.C S.P S.X (tickInputState M x i t v) (t : Int),
        ∃ p : M.N × List (NamedObject V), r = .ok p) ∧
      (M.tick S.C S.P S.X (tickInputState M x i t v) (t : Int)).Nonempty

end Assumptions

section Schedule

/-- `activeAt M S Sched s`: the validators awake at every time from the duty window's start of slot
`s` to the support cutoff of slot `s + 1`, where their confirmation update that evaluates slot `s`
runs.

The variables:
- `M`: the model;
- `S`: the setup; `Sched`: the schedule; `s`: the slot.

Read aloud: the validators awake through the duties of slot `s`. -/
def activeAt (S : Setup V) (Sched : Schedule V) (s : ℕ) : Finset V :=
  Sched.awakeThroughout ((M.dutyWindowStart S.C s : ℕ) : Int)
    ((M.supportCutoff S.C (s + 1) : ℕ) : Int)

/-- `honestActiveAt M S Sched s`: the validators of `activeAt M S Sched s` outside the adversary set
at the support cutoff of slot `s + 1`.

The variables:
- `M`: the model;
- `S`: the setup; `Sched`: the schedule; `s`: the slot.

Read aloud: the validators awake through the duties of slot `s` and honest at its update. -/
def honestActiveAt (S : Setup V) (Sched : Schedule V) (s : ℕ) : Finset V :=
  activeAt M S Sched s \ Sched.adv ((M.supportCutoff S.C (s + 1) : ℕ) : Int)

/-- `updaterAt M S Sched s`: the validators awake at every time from the duty window's start of
slot `s + 1` to the support cutoff of slot `s + 1`, the window of the confirmation update that
evaluates slot `s`, and outside the adversary set at that cutoff.

The variables:
- `M`: the model;
- `S`: the setup; `Sched`: the schedule; `s`: the slot the update evaluates.

Read aloud: the validators awake and honest through the update of slot `s`. -/
def updaterAt (S : Setup V) (Sched : Schedule V) (s : ℕ) : Finset V :=
  Sched.awakeThroughout ((M.dutyWindowStart S.C (s + 1) : ℕ) : Int)
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) \
    Sched.adv ((M.supportCutoff S.C (s + 1) : ℕ) : Int)

/-- `Sleepiness M S Sched anchor`: at every slot `s ≥ 1` starting at or after `anchor`, the
validators of `activeAt M S Sched (s - 1)` outside the adversary set at the vote time of slot `s`
outnumber the adversary set at that time.

The variables:
- `M`: the model;
- `S`: the setup; `Sched`: the schedule; `anchor`: the time from which the condition holds.

Read aloud: from `anchor` on, the honest validators active at the slot before outnumber the
adversary at every vote time. -/
def Sleepiness (S : Setup V) (Sched : Schedule V) (anchor : ℕ) : Prop :=
  ∀ s : ℕ, 1 ≤ s → anchor ≤ M.slotStart S.C s →
    |Sched.adv ((M.voteTime S.C s : ℕ) : Int)| <
      |activeAt M S Sched (s - 1) \ Sched.adv ((M.voteTime S.C s : ℕ) : Int)|

/-- `roundMembers M S Sched s''`: the validators outside the adversary set at the support cutoff of
slot `s''`. A round whose next honest round opening slot is `s''` reads its invariants at this set; the next
opening's proposer is one of them (`HonestOpeningSeq.honest`), and the validators honest at a
later time are among them.

The variables:
- `M`: the model;
- `S`: the setup; `Sched`: the schedule; `s''`: the next honest round opening slot.

Read aloud: the members of a round are the validators honest through that round. -/
def roundMembers (S : Setup V) (Sched : Schedule V) (s'' : ℕ) : Finset V :=
  Finset.univ \ Sched.adv ((M.supportCutoff S.C s'' : ℕ) : Int)

variable [RootOrder] (S : Setup V) (Sched : Schedule V) in
/-- `holdersAt M S Sched s s'`: the lock holders of slot `s` that act at slot `s'`, that is the
validators of `updaterAt M S Sched s` (awake through the update of slot `s`, honest at its cutoff)
that are in `honestActiveAt M S Sched s'`.

The variables:
- `M`: the model;
- `S`, `Sched`: the setup, the schedule; `s`: the hand-over slot; `s'`: the slot they act at.

Read aloud: the validators that ran slot `s`'s update and are honest and active at slot `s'`. -/
def holdersAt (s s' : ℕ) : Finset V :=
  updaterAt M S Sched s ∩ honestActiveAt M S Sched s'

end Schedule

end GoldilocksCorrectness.Record.Statements.AbstractTrace.Atomic
