module
public import GoldilocksCorrectness.Statements.AbstractTrace.TraceDefs
public import GoldilocksCorrectness.Record.Model
public import GoldilocksSts

@[expose] public section

/-!
# The activity read at a model's times

The readings of an activity `A`, through a trace `x`, at the times of a model `M`: the validators
awake through a slot's duties, those of them honest at the slot's update, the validators that run a
slot's update, the sleepiness condition, the members of a round, and the lock holders. A validator is
read awake through a slot's duties by `Activity.awakeThroughoutToTick`, opened at the protocol's duty
window start `duty_window_start S.C s` (an integer, negative at the first slots): it ticks to the
window's last time and has been awake since the trace's start, or since its first tick after its last
restart, to a clock value at most that start, up to that tick, as the protocol's wake rule counts it;
nothing is asked of the steps after its tick. A validator of `updaterAt` is read awake and honest in
the same window, by `Activity.activeThroughoutToTick` (awake and outside the adversary set after every
step of the window up to its tick); nothing is asked of it after that tick. A validator
is honest at a time, in `honestActiveAt`, `Sleepiness` and `roundMembers`, when it is outside the adversary set after every
step whose time is that time.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.AbstractTrace

open GoldilocksCorrectness.Statements.AbstractTrace (Activity Trace Event)
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] {Msg N : Type}
variable (M : GoldilocksModel V)

/-- `activeAt M S A x s`: the validators that tick to the support cutoff of slot `s + 1`, where
their confirmation update that evaluates slot `s` runs, and are awake after every step up to that tick
(never restarted), or tick, after their last restart, to a clock value at most the protocol's duty
window start of slot `s`, `duty_window_start S.C s`, and are awake after every step from that tick up
to their tick to the cutoff. At the first slots that start is negative, and
only a validator never restarted counts, as the protocol's wake test reads it.

The variables:
- `M`: the model;
- `S`: the setup; `A`: the activity; `x`: the trace; `s`: the slot.

Read aloud: the validators awake through the duties of slot `s` up to their update's tick, a
validator that came back up counted from its first tick, at a clock value at most the duty window's
start. -/
noncomputable def activeAt (S : Setup V) (A : Activity V) (x : Trace V Msg N) (s : ℕ) : Finset V :=
  A.awakeThroughoutToTick x (Goldilocks.duty_window_start S.C s) (M.supportCutoff S.C (s + 1))

open Classical in
/-- `honestActiveAt M S A x s`: the validators of `activeAt M S A x s` (awake through the duties of
slot `s` up to their tick to the support cutoff of slot `s + 1`) outside the adversary set after every
step whose time is at most that cutoff, and outside the adversary set at every step at which a
validator outside the adversary set ticks to that cutoff.

Awakeness is read up to the member's own tick; honesty is read at the time of the cutoff, where the
phase's member set reads it, and at every honest validator's tick to the
cutoff, where that validator counts the member's votes.

The variables:
- `M`: the model;
- `S`: the setup; `A`: the activity; `x`: the trace; `s`: the slot.

Read aloud: the validators awake through the duties of slot `s` up to their update, honest through
the real time of its support cutoff, and still honest whenever an honest validator counts the slot's
votes at its tick to that cutoff. -/
noncomputable def honestActiveAt (S : Setup V) (A : Activity V) (x : Trace V Msg N) (s : ℕ) :
    Finset V :=
  activeAt M S A x s \ (A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) ∪
    Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))

/-- `updaterAt M S A x s`: the validators that tick to the support cutoff of slot `s + 1`, where the
confirmation update that evaluates slot `s` runs, and are awake and outside the adversary set after
every step up to that tick, or tick, after their last restart, to a clock value at most the protocol's
duty window start of slot `s + 1`, `duty_window_start S.C (s + 1)`, and are awake and outside the
adversary set after every step from that tick up to their tick to the cutoff.

Awakeness and honesty are read up to the member's own tick: nothing is
asked of the member after that tick, the tick that runs the protocol's update.

The variables:
- `M`: the model;
- `S`: the setup; `A`: the activity; `x`: the trace; `s`: the slot the update evaluates.

Read aloud: an updater of slot `s` is a validator that ran slot `s`'s update awake and honest up to
its own tick, a validator that came back up counted from its first tick, at a clock value at most the
duty window's start. -/
noncomputable def updaterAt (S : Setup V) (A : Activity V) (x : Trace V Msg N) (s : ℕ) :
    Finset V :=
  A.activeThroughoutToTick x (Goldilocks.duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1))

/-- `Sleepiness M S A x anchor`: at every slot `s ≥ 1` starting at or after `anchor`, the
validators of `activeAt M S A x (s - 1)` outside the adversary set after every step whose time is
the vote time of slot `s` outnumber the validators in the adversary set after some such step.

The variables:
- `M`: the model;
- `S`: the setup; `A`: the activity; `x`: the trace; `anchor`: the time from which the condition
  holds.

Read aloud: from `anchor` on, the honest validators active at the slot before outnumber the
adversary at every vote time. -/
def Sleepiness (S : Setup V) (A : Activity V) (x : Trace V Msg N) (anchor : ℕ) : Prop :=
  ∀ s : ℕ, 1 ≤ s → anchor ≤ M.slotStart S.C s →
    |A.corruptedAtTime x (M.voteTime S.C s)| <
      |activeAt M S A x (s - 1) \ A.corruptedAtTime x (M.voteTime S.C s)|

/-- `roundMembers M S A x s''`: the validators outside the adversary set after every step whose
time is the support cutoff of slot `s''`.

The variables:
- `M`: the model;
- `S`: the setup; `A`: the activity; `x`: the trace; `s''`: the next honest round opening slot.

Read aloud: the members of a round are the validators honest through that round. -/
noncomputable def roundMembers (S : Setup V) (A : Activity V) (x : Trace V Msg N) (s'' : ℕ) :
    Finset V :=
  Finset.univ \ A.corruptedAtTime x (M.supportCutoff S.C s'')

/-- `holdersAt M S A x s s'`: the validators of `updaterAt M S A x s` (awake and honest up to their
tick that runs the update of slot `s`) that are in `honestActiveAt M S A x s'` (awake through the
duties of slot `s'` and honest at its support cutoff).

The variables:
- `M`: the model;
- `S`: the setup; `A`: the activity; `x`: the trace; `s`: the hand-over slot; `s'`: the slot they
  act at.

Read aloud: the validators that ran slot `s`'s update and are honest and active at slot `s'`. -/
noncomputable def holdersAt (S : Setup V) (A : Activity V) (x : Trace V Msg N) (s s' : ℕ) :
    Finset V :=
  updaterAt M S A x s ∩ honestActiveAt M S A x s'

end GoldilocksCorrectness.Record.Statements.AbstractTrace
