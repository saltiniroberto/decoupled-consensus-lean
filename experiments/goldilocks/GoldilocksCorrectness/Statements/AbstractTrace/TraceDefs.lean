module
public import GoldilocksCorrectness.Statements.AbstractTrace.ActivityDefs
public import GoldilocksCorrectness.Statements.Network.ViewVocabDefs
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The trace

A run, as the execution-level statements read it: a sequence of steps, each one validator's tick to
a clock reading, one validator's restart at a clock reading, one delivery of a signed message to one
validator, or a step of another kind; after each step, the time, every validator's node state and the
sent log (every signed message ever put on the wire, with multiplicity).

The page defines:
- `Event` and `Trace`;
- the readers of a trace: honesty after a step, the step of a validator's tick to a clock value
  and the node state that tick starts from and the one it leaves, a validator's clock value after a
  step, the step after every step at a time less than `t` and the node states then, a step's sends,
  an honest send, the trace with its node states mapped;
- the activity read through the trace: the validators in the adversary set, awake or active at
  every step read as a time, honesty up to a time, the validators counted through an interval of
  times, and the three counts of the adversary set up to a time;
- `Trace.ReactedAtLeast`: by a step, a validator has ticked to, or been restarted at, a reading at
  least a given one;
- `EnvFactsBy`: what the environment promises on a trace under an activity, with the delivery
  deadline a function of the message and the time of its sending, and a re-delivery delay after the
  receiver's first tick at a reading at least the message's release reading; of unforgeability, only
  its half about the adversary's steps (`other_sent`);
- `CatchUpAfterRestartBy`: what a validator restarted after a message was on the wire is owed, in the
  shape of the delivery promise;
- the instances: `EnvFactsDelivery` (the synchronous delivery promise), `EnvFactsSync` (that and the
  catch-up after a restart), `EnvFacts` (the catch-up delay equal to the delay), `EnvFactsNoDelivery`
  (no delivery promised);
- `SyncedWithinBy`: what an honest validator active then and for a while after would serve to a peer
  that asks, from its last state before the time and at its own clock value, reaches every validator
  that stays active through a sync deadline, a function of the receiver, the message and the time;
  its instance `SyncedWithin` (the deadline `Δs` after the later of the time and `GST`).

What a step of a protocol does to a node state is not a fact of the environment; it is the record
`RunFacts` of `GoldilocksCorrectness/Record/Restated/Statements/AbstractTrace/RunFactsDefs.lean`.

This page reads no protocol: it imports only the sts framework (for signed messages), the
vocabulary `ViewVocab` and the activity.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GoldilocksCorrectness.Statements.AbstractTrace

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.Network (ViewVocab)

/-- One step of a trace, as far as the statements read it. -/
inductive Event (V Msg : Type) where
  /-- `tick v t`: the clock of `v` comes to read `t`, and `v` runs its tick at that reading. -/
  | tick (v : V) (t : ℕ)
  /-- `restart v t keep`: `v` comes back up with its clock reading `t` and runs its wake reaction;
  `keep` says whether it keeps its memory. -/
  | restart (v : V) (t : ℕ) (keep : Bool)
  /-- `deliver v sm`: the signed message `sm` is delivered to `v`, which runs its receive
  reaction. -/
  | deliver (v : V) (sm : SignedMsg V Msg)
  /-- Any other step: the time moving, a step of the environment, a send by a validator in the
  adversary set, a copy of a message already on the wire. -/
  | other

/-- A run as the statements read it: after each step, the time, every node state and the sent log,
and for each step, its event. -/
structure Trace (V Msg N : Type) where
  /-- `time i`: the real time after `i` steps. -/
  time : (i : ℕ) → ℝ
  /-- `st i v`: the node state of `v` after `i` steps. -/
  st : (i : ℕ) → (v : V) → N
  /-- `sent i`: the sent log after `i` steps, every signed message put on the wire so far, with
  multiplicity. -/
  sent : (i : ℕ) → Multiset (SignedMsg V Msg)
  /-- `lbl i`: the event of step `i`, the step from the configuration after `i` steps to the one
  after `i + 1`. -/
  lbl : (i : ℕ) → Event V Msg

namespace Trace

variable {V Msg N : Type}

section Readers

variable (A : Activity V) (x : Trace V Msg N)

set_option linter.unusedVariables false in
/-- `x.Honest A i v`: `v` is outside the adversary set after `i` steps.

The variables:
- `A`: the activity; `x`: the trace; `i`: the step; `v`: the validator.

Read aloud: `v` is honest after `i` steps. -/
def Honest (A : Activity V) (x : Trace V Msg N) (i : ℕ) (v : V) : Prop := v ∉ A.corrupted i

set_option linter.unusedVariables false in
/-- `x.HonestThrough A i v`: `v` is outside the adversary set after every step up to `i`.

The variables:
- `A`: the activity; `x`: the trace; `i`: the step; `v`: the validator.

Read aloud: `v` has been honest up to step `i`. -/
def HonestThrough (A : Activity V) (x : Trace V Msg N) (i : ℕ) (v : V) : Prop :=
  A.HonestThroughStep i v

open Classical in
/-- `x.tickStep v t`: the first step whose event is `v`'s tick to the reading `t`; `0` when there is
none.

The variables:
- `x`: the trace; `v`: the validator; `t`: the clock reading.

Read aloud: the step of `v`'s tick to `t`. -/
noncomputable def tickStep (v : V) (t : ℕ) : ℕ :=
  if h : ∃ i : ℕ, x.lbl i = Event.tick v t then Nat.find h else 0

/-- `x.tickInput v t`: the node state of `v` at the step of its tick to `t`, the state that tick
starts from.

The variables:
- `x`: the trace; `v`: the validator; `t`: the clock reading.

Read aloud: what `v`'s tick to `t` reads. -/
noncomputable def tickInput (v : V) (t : ℕ) : N := x.st (x.tickStep v t) v

/-- `x.tickOutput v t`: the node state of `v` at the step after the step of its tick to `t`, the
state that tick leaves.

The variables:
- `x`: the trace; `v`: the validator; `t`: the clock value.

Read aloud: the state `v`'s tick to the clock value `t` leaves. -/
noncomputable def tickOutput (v : V) (t : ℕ) : N := x.st (x.tickStep v t + 1) v

open Classical in
/-- `x.clockValue i v`: the value of `v`'s clock after `i` steps: the clock value `t` of `v`'s last
`tick v t` or `restart v t keep` at a step less than `i`; `0`, the node's initial clock, when there
is none. A clock value is the natural number `t` of `Event.tick v t` and `Event.restart v t keep`,
the node's clock field's value after that step, as distinct from the real time `x.time i`.

The variables:
- `x`: the trace; `i`: the step; `v`: the validator.

Read aloud: what `v`'s clock reads after `i` steps. -/
noncomputable def clockValue : (i : ℕ) → (v : V) → ℕ
  | 0, _ => 0
  | i + 1, v =>
    match x.lbl i with
    | Event.tick w t => if w = v then t else clockValue i v
    | Event.restart w t _ => if w = v then t else clockValue i v
    | _ => clockValue i v

open Classical in
/-- `x.firstAt t`: the first step after which the time is at least `t`; `0` when there is none.

The variables:
- `x`: the trace; `t`: the time.

Read aloud: the first step at which the time has reached `t`. -/
noncomputable def firstAt (t : ℕ) : ℕ :=
  if h : ∃ i : ℕ, (t : ℝ) ≤ x.time i then Nat.find h else 0

/-- `x.stepBefore t`: `x.firstAt t − 1` (`0` when `x.firstAt t` is `0`). When the time starts at
`0` and reaches `t ≥ 1`, the configuration after `x.stepBefore t` steps is the one after every step
at a time less than `t`.

The variables:
- `x`: the trace; `t`: the time.

Read aloud: the step after every step at a time less than `t`. -/
noncomputable def stepBefore (t : ℕ) : ℕ := x.firstAt t - 1

/-- `x.stateBefore t v`: the node state of `v` after `x.stepBefore t` steps, for every `v`, awake or
not.

The variables:
- `x`: the trace; `t`: the time; `v`: the validator.

Read aloud: `v`'s node state after every step at a time less than `t`. -/
noncomputable def stateBefore (t : ℕ) (v : V) : N := x.st (x.stepBefore t) v

/-- `x.ReactedAtLeast j v r`: at some step up to `j`, `v` ticked to, or was restarted at, a clock
reading at least `r`.

The variables:
- `x`: the trace; `j`: the step; `v`: the validator; `r`: the clock reading.

Read aloud: by step `j`, `v` has reacted to a reading at least `r`. -/
def ReactedAtLeast (j : ℕ) (v : V) (r : ℕ) : Prop :=
  ∃ i' : ℕ, i' ≤ j ∧ ∃ t' : ℕ, r ≤ t' ∧
    (x.lbl i' = Event.tick v t' ∨ ∃ keep : Bool, x.lbl i' = Event.restart v t' keep)

variable [DecidableEq V] [DecidableEq Msg]

/-- `x.PutsAt i sm`: the step `i` adds a copy of the signed message `sm` to the sent log.

The variables:
- `x`: the trace; `i`: the step; `sm`: the signed message.

Read aloud: step `i` puts `sm` on the wire. -/
def PutsAt (i : ℕ) (sm : SignedMsg V Msg) : Prop := sm ∈ x.sent (i + 1) - x.sent i

/-- `x.HonestSendAt A i sm`: the step `i` adds a copy of `sm` to the sent log, and the signer of
`sm` is outside the adversary set in the configuration the step starts from. A validator's own send
and a copy of what it received each count.

The variables:
- `A`: the activity; `x`: the trace; `i`: the step; `sm`: the signed message.

Read aloud: at step `i`, an honest validator put `sm` on the wire. -/
def HonestSendAt (i : ℕ) (sm : SignedMsg V Msg) : Prop :=
  x.PutsAt i sm ∧ sm.sender ∉ A.corrupted i

end Readers

section Map

variable (x : Trace V Msg N)

/-- `x.map f`: the trace `x` with every node state mapped by `f`; the times, the sent logs and the
events unchanged.

The variables:
- `x`: the trace; `f`: the map on node states.

Read aloud: the trace seen through `f`. -/
def map {N' : Type} (f : (n : N) → N') : Trace V Msg N' :=
  { time := x.time, st := fun i v => f (x.st i v), sent := x.sent, lbl := x.lbl }

variable {N' : Type} (f : (n : N) → N')

/-- The times of `x.map f` are those of `x`. -/
@[simp] theorem map_time (i : ℕ) : (x.map f).time i = x.time i := rfl

/-- The node states of `x.map f` are those of `x`, mapped by `f`. -/
@[simp] theorem map_st (i : ℕ) (v : V) : (x.map f).st i v = f (x.st i v) := rfl

/-- The sent logs of `x.map f` are those of `x`. -/
@[simp] theorem map_sent (i : ℕ) : (x.map f).sent i = x.sent i := rfl

/-- The events of `x.map f` are those of `x`. -/
@[simp] theorem map_lbl (i : ℕ) : (x.map f).lbl i = x.lbl i := rfl

/-- The step of a tick in `x.map f` is the one in `x`. -/
@[simp] theorem map_tickStep (v : V) (t : ℕ) : (x.map f).tickStep v t = x.tickStep v t := rfl

/-- The node state a tick starts from in `x.map f` is the one in `x`, mapped by `f`. -/
@[simp] theorem map_tickInput (v : V) (t : ℕ) : (x.map f).tickInput v t = f (x.tickInput v t) :=
  rfl

/-- The step before a time in `x.map f` is the one in `x`. -/
@[simp] theorem map_stepBefore (t : ℕ) : (x.map f).stepBefore t = x.stepBefore t := rfl

/-- The node state before a time in `x.map f` is the one in `x`, mapped by `f`. -/
@[simp] theorem map_stateBefore (t : ℕ) (v : V) :
    (x.map f).stateBefore t v = f (x.stateBefore t v) := rfl

/-- The clock values in `x.map f` are those of `x`. -/
@[simp] theorem map_clockValue (i : ℕ) (v : V) : (x.map f).clockValue i v = x.clockValue i v := by
  induction i generalizing v with
  | zero => rfl
  | succ i ih => simp only [clockValue, map_lbl, ih]

end Map
section TickStep

variable (x : Trace V Msg N)

/-- When `v` ticks to the reading `d` at some step, `x.tickStep v d` is such a step.

The variables:
- `x`: the trace; `v`: the validator; `d`: the reading; `h`: some step is `v`'s tick to `d`.

Read aloud: the step of `v`'s tick to `d` is a tick of `v` to `d`. -/
theorem lbl_tickStep {v : V} {d : ℕ} (h : ∃ i : ℕ, x.lbl i = Event.tick v d) :
    x.lbl (x.tickStep v d) = Event.tick v d := by
  classical
  unfold tickStep
  rw [dif_pos h]
  exact Nat.find_spec h

/-- A step before `x.tickStep v d` exists only when `v` ticks to `d` at some step: when it never
does, `x.tickStep v d` is `0`.

The variables:
- `x`: the trace; `v`: the validator; `d`: the reading; `j`: the step.

Read aloud: being before `v`'s tick to `d` means that tick exists. -/
theorem exists_tick_of_lt_tickStep {v : V} {d j : ℕ} (hj : j < x.tickStep v d) :
    ∃ i : ℕ, x.lbl i = Event.tick v d := by
  classical
  by_contra h
  unfold tickStep at hj
  rw [dif_neg h] at hj
  omega

/-- On a trace whose time is monotone in the step, a step at a real time less than `c` comes before
`v`'s tick to the clock value `d`, when `v` ticks to `d` and every such tick is at a real time at
least `c`.

The variables:
- `x`: the trace; `htime`: the time is monotone in the step; `v`: the validator; `d`: the clock
  value; `c`: the real time; `j`: the step; `hk`: some step is `v`'s tick to `d`; `htk`: every such
  step is at a real time at least `c`.

Read aloud: what happens before the earliest real time of `v`'s tick to `d` happens before that
tick. -/
theorem lt_tickStep_of_time_lt (htime : Monotone x.time) {v : V} {d j : ℕ} {c : ℝ}
    (hk : ∃ i : ℕ, x.lbl i = Event.tick v d)
    (htk : ∀ i : ℕ, x.lbl i = Event.tick v d → c ≤ x.time i)
    (hj : x.time j < c) : j < x.tickStep v d := by
  by_contra h
  have := htime (Nat.le_of_not_lt h)
  have := htk _ (x.lbl_tickStep hk)
  linarith

/-- No step has happened before step `0`: `v`'s clock value after `0` steps is `0`, the node's
initial clock.

The variables:
- `x`: the trace; `v`: the validator.

Read aloud: every clock starts at `0`. -/
@[simp] theorem clockValue_zero (v : V) : x.clockValue 0 v = 0 := rfl

/-- After `v`'s tick to the clock value `t` at step `i`, `v`'s clock value is `t`.

The variables:
- `x`: the trace; `i`: the step; `v`: the validator; `t`: the clock value; `h`: step `i` is `v`'s
  tick to `t`.

Read aloud: a tick sets the clock to its value. -/
theorem clockValue_succ_of_tick {i : ℕ} {v : V} {t : ℕ} (h : x.lbl i = Event.tick v t) :
    x.clockValue (i + 1) v = t := by
  simp [clockValue, h]

/-- After `v`'s restart at the clock value `t` at step `i`, `v`'s clock value is `t`.

The variables:
- `x`: the trace; `i`: the step; `v`: the validator; `t`: the clock value; `keep`: whether it keeps
  its memory; `h`: step `i` is `v`'s restart at `t`.

Read aloud: a restart sets the clock to its value. -/
theorem clockValue_succ_of_restart {i : ℕ} {v : V} {t : ℕ} {keep : Bool}
    (h : x.lbl i = Event.restart v t keep) : x.clockValue (i + 1) v = t := by
  simp [clockValue, h]

/-- A step that is neither a tick nor a restart of `v` leaves `v`'s clock value as it is.

The variables:
- `x`: the trace; `i`: the step; `v`: the validator; `htick`: step `i` is no tick of `v`;
  `hrestart`: step `i` is no restart of `v`.

Read aloud: only `v`'s own ticks and restarts move `v`'s clock. -/
theorem clockValue_succ_of_not {i : ℕ} {v : V} (htick : ∀ t : ℕ, x.lbl i ≠ Event.tick v t)
    (hrestart : ∀ (t : ℕ) (keep : Bool), x.lbl i ≠ Event.restart v t keep) :
    x.clockValue (i + 1) v = x.clockValue i v := by
  classical
  cases hl : x.lbl i with
  | tick w t =>
    have hw : w ≠ v := fun hw => htick t (hw ▸ hl)
    simp [clockValue, hl, hw]
  | restart w t keep =>
    have hw : w ≠ v := fun hw => hrestart t keep (hw ▸ hl)
    simp [clockValue, hl, hw]
  | deliver w sm => simp [clockValue, hl]
  | other => simp [clockValue, hl]

/-- `v`'s clock value after `i` steps is `0` or was set by a tick or a restart of `v` at a step less
than `i` with no later tick or restart of `v` before `i`.

The variables:
- `x`: the trace; `i`: the step; `v`: the validator.

Read aloud: a nonzero clock value was set by `v`'s last tick or restart. -/
theorem clockValue_cases (i : ℕ) (v : V) :
    (x.clockValue i v = 0 ∧ ∀ j : ℕ, j < i → (∀ t : ℕ, x.lbl j ≠ Event.tick v t) ∧
      ∀ (t : ℕ) (keep : Bool), x.lbl j ≠ Event.restart v t keep) ∨
    ∃ j : ℕ, j < i ∧
      (x.lbl j = Event.tick v (x.clockValue i v) ∨
        ∃ keep : Bool, x.lbl j = Event.restart v (x.clockValue i v) keep) ∧
      ∀ l : ℕ, j < l → l < i → (∀ t : ℕ, x.lbl l ≠ Event.tick v t) ∧
        ∀ (t : ℕ) (keep : Bool), x.lbl l ≠ Event.restart v t keep := by
  classical
  induction i with
  | zero => exact Or.inl ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ i ih =>
    by_cases ht : ∃ t : ℕ, x.lbl i = Event.tick v t
    · obtain ⟨t, ht⟩ := ht
      refine Or.inr ⟨i, Nat.lt_succ_self i, Or.inl ?_, fun l h1 h2 => absurd h2 (by omega)⟩
      rw [x.clockValue_succ_of_tick ht]; exact ht
    by_cases hr : ∃ (t : ℕ) (keep : Bool), x.lbl i = Event.restart v t keep
    · obtain ⟨t, keep, hr⟩ := hr
      refine Or.inr ⟨i, Nat.lt_succ_self i, Or.inr ⟨keep, ?_⟩, fun l h1 h2 => absurd h2 (by omega)⟩
      rw [x.clockValue_succ_of_restart hr]; exact hr
    have ht' : ∀ t : ℕ, x.lbl i ≠ Event.tick v t := fun t h => ht ⟨t, h⟩
    have hr' : ∀ (t : ℕ) (keep : Bool), x.lbl i ≠ Event.restart v t keep :=
      fun t keep h => hr ⟨t, keep, h⟩
    rw [x.clockValue_succ_of_not ht' hr']
    rcases ih with ⟨h0, hno⟩ | ⟨j, hj, hset, hafter⟩
    · refine Or.inl ⟨h0, fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact hno j hj
      · exact ⟨ht', hr'⟩
    · refine Or.inr ⟨j, by omega, hset, fun l h1 h2 => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
      · exact hafter l h1 h2
      · exact ⟨ht', hr'⟩

end TickStep

end Trace

/-! ## The activity read through the trace -/

namespace Activity

variable {V Msg N : Type} [DecidableEq V] [Fintype V] (A : Activity V) (x : Trace V Msg N)

open Classical in
/-- `A.corruptedAtTime x t`: the validators in the adversary set after some step whose time is at
most `t`. A validator outside it is outside the adversary set after every step whose
time is at most `t` (`A.HonestThroughTime x t v`).

The variables:
- `A`: the activity; `x`: the trace; `t`: the time.

Read aloud: the validators corrupted by `t`. -/
noncomputable def corruptedAtTime (t : ℝ) : Finset V :=
  Finset.univ.filter fun v => ∃ i : ℕ, x.time i ≤ t ∧ v ∈ A.corrupted i

open Classical in
/-- `A.awakeAtTime x t`: the validators awake in every configuration in force at `t`: after `i`
steps for every `i` with `x.time i ≤ t ≤ x.time (i + 1)`.

The configuration after `i` steps is in force on `[x.time i, x.time (i + 1)]`, both ends included
: it is in force at some time of `[a, b]` exactly when `x.time i ≤ b` and
`a ≤ x.time (i + 1)`. No step need be at any given time.

The variables:
- `A`: the activity; `x`: the trace; `t`: the time.

Read aloud: the validators awake in every configuration in force at time `t`. -/
noncomputable def awakeAtTime (t : ℝ) : Finset V :=
  Finset.univ.filter fun v => ∀ i : ℕ, x.time i ≤ t → t ≤ x.time (i + 1) → v ∈ A.awake i

open Classical in
/-- `A.activeAtTime x t`: the validators active (awake and outside the adversary set) in every
configuration in force at `t`: after `i` steps for every `i` with `x.time i ≤ t ≤ x.time (i + 1)`.

The configuration after `i` steps is in force on `[x.time i, x.time (i + 1)]`, both ends included
: it is in force at some time of `[a, b]` exactly when `x.time i ≤ b` and
`a ≤ x.time (i + 1)`. No step need be at any given time.

The variables:
- `A`: the activity; `x`: the trace; `t`: the time.

Read aloud: the validators active in every configuration in force at time `t`. -/
noncomputable def activeAtTime (t : ℝ) : Finset V :=
  Finset.univ.filter fun v => ∀ i : ℕ, x.time i ≤ t → t ≤ x.time (i + 1) → v ∈ A.active i

/-- `A.HonestThroughTime x t v`: `v` is outside the adversary set after every step whose time is at
most `t`.

The variables:
- `A`: the activity; `x`: the trace; `t`: the time; `v`: the validator.

Read aloud: `v` has not been in the adversary set at any time up to `t`. -/
def HonestThroughTime (t : ℝ) (v : V) : Prop := ∀ i : ℕ, x.time i ≤ t → v ∉ A.corrupted i

open Classical in
/-- `A.awakeThroughout x a b`: the validators awake in every configuration in force at some time of
`[a, b]`: after `i` steps for every `i` with `x.time i ≤ b` and `a ≤ x.time (i + 1)`, the
configuration of the last step at or before `a` included.

A validator restarted at a step whose time is `a` is not awake in the configuration before its
restart, which is in force at `a`, so it is counted only by the intervals that start at a later
time.

The variables:
- `A`: the activity; `x`: the trace; `a`, `b`: the first and the last time of the interval.

Read aloud: the validators awake throughout `[a, b]`. -/
noncomputable def awakeThroughout (a b : ℝ) : Finset V :=
  Finset.univ.filter fun v => ∀ i : ℕ, x.time i ≤ b → a ≤ x.time (i + 1) → v ∈ A.awake i

open Classical in
/-- `A.awakeThroughoutOrFromTick x a b`: the validators awake after every step whose time is in
`[a, b]`, and the validators that tick to a natural clock value at most `a` at some step `k` and are
awake after every step from `k` on whose time is at most `b`.

The second case counts a validator restarted before the interval and ticking afterwards to a clock
value at most `a`: it is counted from that tick. The window opens at an integer clock value `a`, the
start type of `awakeThroughoutToTick`; at a negative `a` no natural clock value is at
most `a`, and only the first case counts. The environment's promises read `awakeThroughout` and
`activeThroughout`, which keep only the first case.

The variables:
- `A`: the activity; `x`: the trace; `a`, `b`: the first and the last time of the interval.

Read aloud: the validators awake throughout `[a, b]`, a validator that came back up counted from its
tick to a clock value at most `a`. -/
noncomputable def awakeThroughoutOrFromTick (a : ℤ) (b : ℕ) : Finset V :=
  Finset.univ.filter fun v =>
    (∀ i : ℕ, x.time i ≤ b → (a : ℝ) ≤ x.time (i + 1) → v ∈ A.awake i) ∨
    (∃ k : ℕ, ∃ c : ℕ, (c : ℤ) ≤ a ∧ x.lbl k = Event.tick v c ∧
      ∀ i : ℕ, k ≤ i → x.time i ≤ b → v ∈ A.awake i)

open Classical in
/-- `A.activeThroughout x a b`: the validators active in every configuration in force at some time of
`[a, b]`: after `i` steps for every `i` with `x.time i ≤ b` and `a ≤ x.time (i + 1)`, the
configuration of the last step at or before `a` included.

A validator restarted at a step whose time is `a` is not active in the configuration before its
restart, which is in force at `a`, so it is counted only by the intervals that start at a later
time.

The variables:
- `A`: the activity; `x`: the trace; `a`, `b`: the first and the last time of the interval.

Read aloud: the validators active throughout `[a, b]`. -/
noncomputable def activeThroughout (a b : ℝ) : Finset V :=
  Finset.univ.filter fun v => ∀ i : ℕ, x.time i ≤ b → a ≤ x.time (i + 1) → v ∈ A.active i

open Classical in
/-- `A.activeThroughoutOrFromTick x a b`: the validators active after every step whose time is in
`[a, b]`, and the validators that tick to a natural clock value at most `a` at some step `k` and are
active after every step from `k` on whose time is at most `b`.

The active form of `awakeThroughoutOrFromTick`: the second case counts a validator that came back up,
from its tick to a clock value at most `a`.

The variables:
- `A`: the activity; `x`: the trace; `a`, `b`: the first and the last time of the interval.

Read aloud: the validators active throughout `[a, b]`, a validator that came back up counted from its
tick to a clock value at most `a`. -/
noncomputable def activeThroughoutOrFromTick (a : ℤ) (b : ℕ) : Finset V :=
  Finset.univ.filter fun v =>
    (∀ i : ℕ, x.time i ≤ b → (a : ℝ) ≤ x.time (i + 1) → v ∈ A.active i) ∨
    (∃ k : ℕ, ∃ c : ℕ, (c : ℤ) ≤ a ∧ x.lbl k = Event.tick v c ∧
      ∀ i : ℕ, k ≤ i → x.time i ≤ b → v ∈ A.active i)

open Classical in
/-- `A.awakeAtTimeOrFromTick x t`: the validators awake after every step whose time is `t`, and the
validators that tick to a natural clock value at most `t` at some step `k` and are awake after every
step from `k` on whose time is at most `t`.

The per-time form of `awakeThroughoutOrFromTick` (its interval `[t, t]`), with its start type and
second case: a validator that came back up is counted awake at `t` from its tick to a
clock value at most `t`; at a negative `t` only the first case counts.

The variables:
- `A`: the activity; `x`: the trace; `t`: the time.

Read aloud: the validators awake at time `t`, a validator that came back up counted from its tick to a
clock value at most `t`. -/
noncomputable def awakeAtTimeOrFromTick (t : ℤ) : Finset V :=
  Finset.univ.filter fun v =>
    (∀ i : ℕ, x.time i ≤ t → (t : ℝ) ≤ x.time (i + 1) → v ∈ A.awake i) ∨
    (∃ k : ℕ, ∃ c : ℕ, (c : ℤ) ≤ t ∧ x.lbl k = Event.tick v c ∧
      ∀ i : ℕ, k ≤ i → x.time i ≤ t → v ∈ A.awake i)

open Classical in
/-- `A.awakeThroughoutToTick x a b`: the validators that tick to the clock value `b` at some step
`k'` and either are awake after every step up to `k'` (never restarted up to that tick), or tick to a
natural clock value `c ≤ a` at some step `k ≤ k'` and are awake after every step from `k` up to `k'`
.

The window opens at the integer clock value `a` and ends at the validator's own tick to `b`, its last
value: nothing is asked of the steps after that tick. The cases are read in steps and clock values
only. This is the reader of the sets the protocol's wake rule defines (`updaterAt`, `activeAt`): the
wake rule's test at the tick to `b`, for a duty window starting at `a`, reads the clock value of the
first tick after the last restart; a validator never restarted keeps the initial value, and a
validator that ticked to a value at most `a` after its last restart and stayed awake up to its tick to
`b` stored a value at most `a`. At a negative `a` no natural clock value is at most `a`, and only the
first case counts. The environment's promises read `awakeThroughout` and `activeThroughout`.

The variables:
- `A`: the activity; `x`: the trace; `a`: the clock value that opens the window; `b`: the clock value
  of the tick that ends it.

Read aloud: the validators that tick to `b` and either have been awake since the trace's start, or
ticked, after their last restart, to a clock value at most `a` and stayed awake up to their tick to
`b`. -/
noncomputable def awakeThroughoutToTick (a : ℤ) (b : ℕ) : Finset V :=
  Finset.univ.filter fun v => ∃ k' : ℕ, x.lbl k' = Event.tick v b ∧
    ((∀ i : ℕ, i ≤ k' → v ∈ A.awake i) ∨
     (∃ k ≤ k', ∃ c : ℕ, (c : ℤ) ≤ a ∧ x.lbl k = Event.tick v c ∧
        ∀ i : ℕ, k ≤ i → i ≤ k' → v ∈ A.awake i))

open Classical in
/-- `A.activeThroughoutToTick x a b`: the validators that tick to the clock value `b` at some step
`k'` and either are active after every step up to `k'`, or tick to a natural clock value `c ≤ a` at
some step `k ≤ k'` and are active after every step from `k` up to `k'`.

The active form of `awakeThroughoutToTick`: the window opens at the integer clock value `a` and ends at
the validator's own tick to `b`; both cases are read in steps and clock values only.

The variables:
- `A`: the activity; `x`: the trace; `a`: the clock value that opens the window; `b`: the clock value
  of the tick that ends it.

Read aloud: the validators that tick to `b` and either have been active since the trace's start, or
ticked, after their last restart, to a clock value at most `a` and stayed active up to their tick to
`b`. -/
noncomputable def activeThroughoutToTick (a : ℤ) (b : ℕ) : Finset V :=
  Finset.univ.filter fun v => ∃ k' : ℕ, x.lbl k' = Event.tick v b ∧
    ((∀ i : ℕ, i ≤ k' → v ∈ A.active i) ∨
     (∃ k ≤ k', ∃ c : ℕ, (c : ℤ) ≤ a ∧ x.lbl k = Event.tick v c ∧
        ∀ i : ℕ, k ≤ i → i ≤ k' → v ∈ A.active i))

/-- `A.AdversaryFewerThanThirdUntil x n t`: every set of validators each of which is in the
adversary set after some step whose time is at most `t` has fewer than a third of `n` members.

The variables:
- `A`: the activity; `x`: the trace; `n`: the number of validators; `t`: the time.

Read aloud: up to `t`, fewer than a third of the `n` validators have ever been in the adversary
set. -/
def AdversaryFewerThanThirdUntil (n : ℕ) (t : ℝ) : Prop :=
  ∀ X : Finset V, (∀ v ∈ X, ∃ i : ℕ, x.time i ≤ t ∧ v ∈ A.corrupted i) → 3 * X.card < n

/-- `A.AdversaryFewerThanQuorumUntil x q t`: every set of validators each of which is in the
adversary set after some step whose time is at most `t` has fewer than `q` members.

The variables:
- `A`: the activity; `x`: the trace; `q`: the bound; `t`: the time.

Read aloud: up to `t`, fewer than `q` validators have ever been in the adversary set. -/
def AdversaryFewerThanQuorumUntil (q : ℕ) (t : ℝ) : Prop :=
  ∀ X : Finset V, (∀ v ∈ X, ∃ i : ℕ, x.time i ≤ t ∧ v ∈ A.corrupted i) → X.card < q

/-- `A.AdversaryFewerThanTwoThirdsUntil x n t`: every set of validators each of which is in the
adversary set after some step whose time is at most `t` has fewer than two thirds of `n` members.

The variables:
- `A`: the activity; `x`: the trace; `n`: the number of validators; `t`: the time.

Read aloud: up to `t`, fewer than two thirds of the `n` validators have ever been in the adversary
set. -/
def AdversaryFewerThanTwoThirdsUntil (n : ℕ) (t : ℝ) : Prop :=
  ∀ X : Finset V, (∀ v ∈ X, ∃ i : ℕ, x.time i ≤ t ∧ v ∈ A.corrupted i) → 3 * X.card < 2 * n

variable {A x}

/-- A validator is in `A.corruptedAtTime x t` exactly when it is in the adversary set after some step whose time is at most `t`.

The variables:
- `A`: the activity; `x`: the trace; `t`: the time; `v`: the validator.

Read aloud: in the adversary set at `t` means in it after some step at `t`. -/
theorem mem_corruptedAtTime {t : ℝ} {v : V} :
    v ∈ A.corruptedAtTime x t ↔ ∃ i : ℕ, x.time i ≤ t ∧ v ∈ A.corrupted i := by
  classical
  simp [corruptedAtTime]

/-- A validator is outside `A.corruptedAtTime x t` exactly when it is outside the adversary set
in every configuration in force at `t`.

The variables:
- `A`: the activity; `x`: the trace; `t`: the time; `v`: the validator.

Read aloud: honest at `t` means honest after every step at `t`. -/
theorem not_mem_corruptedAtTime {t : ℝ} {v : V} :
    v ∉ A.corruptedAtTime x t ↔ ∀ i : ℕ, x.time i ≤ t → v ∉ A.corrupted i := by
  rw [mem_corruptedAtTime]
  simp only [not_exists, not_and]

/-- A validator is in `A.awakeAtTime x t` exactly when it is awake after every step whose time is
`t`.

The variables:
- `A`: the activity; `x`: the trace; `t`: the time; `v`: the validator.

Read aloud: awake at `t` means awake after every step at `t`. -/
theorem mem_awakeAtTime {t : ℝ} {v : V} :
    v ∈ A.awakeAtTime x t ↔ ∀ i : ℕ, x.time i ≤ t → t ≤ x.time (i + 1) → v ∈ A.awake i := by
  classical
  simp [awakeAtTime]

/-- A validator is in `A.activeAtTime x t` exactly when it is active after every step whose time is
`t`.

The variables:
- `A`: the activity; `x`: the trace; `t`: the time; `v`: the validator.

Read aloud: active at `t` means active after every step at `t`. -/
theorem mem_activeAtTime {t : ℝ} {v : V} :
    v ∈ A.activeAtTime x t ↔ ∀ i : ℕ, x.time i ≤ t → t ≤ x.time (i + 1) → v ∈ A.active i := by
  classical
  simp [activeAtTime]

/-- A validator is in `A.awakeThroughout x a b` exactly when it is awake in every configuration in force at some time of `[a, b]`.

The variables:
- `A`: the activity; `x`: the trace; `a`, `b`: the ends of the interval; `v`: the validator.

Read aloud: awake throughout `[a, b]` means awake after every step of the interval. -/
theorem mem_awakeThroughout {a b : ℝ} {v : V} :
    v ∈ A.awakeThroughout x a b ↔
      ∀ i : ℕ, x.time i ≤ b → a ≤ x.time (i + 1) → v ∈ A.awake i := by
  classical
  simp only [awakeThroughout, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A validator is in `A.activeThroughout x a b` exactly when it is active in every configuration in force at some time of `[a, b]`.

The variables:
- `A`: the activity; `x`: the trace; `a`, `b`: the ends of the interval; `v`: the validator.

Read aloud: active throughout `[a, b]` means active after every step of the interval. -/
theorem mem_activeThroughout {a b : ℝ} {v : V} :
    v ∈ A.activeThroughout x a b ↔
      ∀ i : ℕ, x.time i ≤ b → a ≤ x.time (i + 1) → v ∈ A.active i := by
  classical
  simp only [activeThroughout, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A validator awake in every configuration in force at some time of `[a, b]` is in `A.awakeThroughout x a b`.

The variables:
- `A`: the activity; `x`: the trace; `a`, `b`: the ends of the interval; `v`: the validator.

Read aloud: awake at every step of the interval is awake throughout it. -/
theorem mem_awakeThroughout_of_forall {a b : ℝ} {v : V}
    (h : ∀ i : ℕ, x.time i ≤ b → a ≤ x.time (i + 1) → v ∈ A.awake i) : v ∈ A.awakeThroughout x a b :=
  mem_awakeThroughout.2 h

/-- A validator active in every configuration in force at some time of `[a, b]` is in
`A.activeThroughout x a b`.

The variables:
- `A`: the activity; `x`: the trace; `a`, `b`: the ends of the interval; `v`: the validator.

Read aloud: active at every step of the interval is active throughout it. -/
theorem mem_activeThroughout_of_forall {a b : ℝ} {v : V}
    (h : ∀ i : ℕ, x.time i ≤ b → a ≤ x.time (i + 1) → v ∈ A.active i) : v ∈ A.activeThroughout x a b :=
  mem_activeThroughout.2 h

/-- A validator counted active throughout `[a, b]` is counted awake throughout it.

The variables:
- `A`: the activity; `x`: the trace; `a`, `b`: the ends of the interval; `v`: the validator.

Read aloud: active throughout is awake throughout. -/
theorem mem_awakeThroughout_of_mem_activeThroughout {a b : ℝ} {v : V}
    (h : v ∈ A.activeThroughout x a b) : v ∈ A.awakeThroughout x a b :=
  mem_awakeThroughout_of_forall fun i h1 h2 =>
    Activity.mem_awake_of_mem_active (mem_activeThroughout.1 h i h1 h2)

/-- A validator counted active throughout `[a, b]` is counted active throughout every interval
`[a', b']` inside it.

The variables:
- `A`: the activity; `x`: the trace; `v`: the validator; `a`, `b`: the ends of the interval; `a'`,
  `b'`: the ends of the interval inside it.

Read aloud: active throughout an interval is active throughout every interval inside it. -/
theorem mem_activeThroughout_of_le {v : V} {a b a' b' : ℝ} (haa : a ≤ a') (hbb : b' ≤ b)
    (hv : v ∈ A.activeThroughout x a b) : v ∈ A.activeThroughout x a' b' :=
  mem_activeThroughout_of_forall fun i h1 h2 =>
    mem_activeThroughout.1 hv i (le_trans h1 hbb) (le_trans haa h2)

/-- A validator counted awake throughout `[a, b]` is counted awake throughout every interval
`[a', b']` inside it.

The variables:
- `A`: the activity; `x`: the trace; `v`: the validator; `a`, `b`: the ends of the interval; `a'`,
  `b'`: the ends of the interval inside it.

Read aloud: awake throughout an interval is awake throughout every interval inside it. -/
theorem mem_awakeThroughout_of_le {v : V} {a b a' b' : ℝ} (haa : a ≤ a') (hbb : b' ≤ b)
    (hv : v ∈ A.awakeThroughout x a b) : v ∈ A.awakeThroughout x a' b' :=
  mem_awakeThroughout_of_forall fun i h1 h2 =>
    mem_awakeThroughout.1 hv i (le_trans h1 hbb) (le_trans haa h2)

/-- A validator counted active throughout `[a, b]` is active after every step whose time is a `t`
of `[a, b]`.

The variables:
- `A`: the activity; `x`: the trace; `v`: the validator; `a`, `b`: the ends of the interval; `t`:
  the time.

Read aloud: active throughout an interval is active at each of its times. -/
theorem mem_activeAtTime_of_mem_activeThroughout {v : V} {a b t : ℝ}
    (hv : v ∈ A.activeThroughout x a b) (hat : a ≤ t) (htb : t ≤ b) : v ∈ A.activeAtTime x t :=
  mem_activeAtTime.2 fun i h1 h2 => mem_activeThroughout.1 hv i (le_trans h1 htb) (le_trans hat h2)

/-- A validator counted awake throughout `[a, b]` is awake after every step whose time is a `t` of
`[a, b]`.

The variables:
- `A`: the activity; `x`: the trace; `v`: the validator; `a`, `b`: the ends of the interval; `t`:
  the time.

Read aloud: awake throughout an interval is awake at each of its times. -/
theorem mem_awakeAtTime_of_mem_awakeThroughout {v : V} {a b t : ℝ}
    (hv : v ∈ A.awakeThroughout x a b) (hat : a ≤ t) (htb : t ≤ b) : v ∈ A.awakeAtTime x t :=
  mem_awakeAtTime.2 fun i h1 h2 => mem_awakeThroughout.1 hv i (le_trans h1 htb) (le_trans hat h2)

/-- A validator counted active throughout `[a, b]` is active after every step whose time is in
`[a, b]`: the configuration after such a step is in force at that step's time, which time is
monotone.

The variables:
- `A`: the activity; `x`: the trace; `htime`: the time is monotone; `a`, `b`: the ends of the
  interval; `v`: the validator; `i`: the step.

Read aloud: active throughout an interval is active after each step of it. -/
theorem mem_active_of_mem_activeThroughout_of_time {v : V} {a b : ℝ} {i : ℕ}
    (htime : Monotone x.time) (hv : v ∈ A.activeThroughout x a b) (h1 : a ≤ x.time i)
    (h2 : x.time i ≤ b) : v ∈ A.active i :=
  mem_activeThroughout.1 hv i h2 (le_trans h1 (htime (Nat.le_succ i)))

/-- A validator counted awake throughout `[a, b]` is awake after every step whose time is in
`[a, b]`.

The variables:
- `A`: the activity; `x`: the trace; `htime`: the time is monotone; `a`, `b`: the ends of the
  interval; `v`: the validator; `i`: the step.

Read aloud: awake throughout an interval is awake after each step of it. -/
theorem mem_awake_of_mem_awakeThroughout_of_time {v : V} {a b : ℝ} {i : ℕ}
    (htime : Monotone x.time) (hv : v ∈ A.awakeThroughout x a b) (h1 : a ≤ x.time i)
    (h2 : x.time i ≤ b) : v ∈ A.awake i :=
  mem_awakeThroughout.1 hv i h2 (le_trans h1 (htime (Nat.le_succ i)))

/-- A validator is outside `A.corruptedAtTime x t` exactly when it has been outside the adversary set
up to `t`.

The variables:
- `A`: the activity; `x`: the trace; `t`: the time; `v`: the validator.

Read aloud: not corrupted by `t` is honest up to `t`. -/
theorem not_mem_corruptedAtTime_iff_honestThroughTime {t : ℝ} {v : V} :
    v ∉ A.corruptedAtTime x t ↔ A.HonestThroughTime x t v :=
  not_mem_corruptedAtTime

/-! ### The two-case reader -/

/-- A validator is in `A.awakeThroughoutOrFromTick x a b` exactly when it is awake after every step
whose time is in `[a, b]`, or ticks to a natural clock value at most `a` at some step `k` and is awake
after every step from `k` on whose time is at most `b`.

The variables:
- `A`: the activity; `x`: the trace; `a`, `b`: the ends of the interval; `v`: the validator.

Read aloud: the two cases of awake throughout `[a, b]` counted from a tick to a value at most `a`. -/
theorem mem_awakeThroughoutOrFromTick {a : ℤ} {b : ℕ} {v : V} :
    v ∈ A.awakeThroughoutOrFromTick x a b ↔
      ((∀ i : ℕ, x.time i ≤ b → a ≤ x.time (i + 1) → v ∈ A.awake i) ∨
       (∃ k : ℕ, ∃ c : ℕ, (c : ℤ) ≤ a ∧ x.lbl k = Event.tick v c ∧
         ∀ i : ℕ, k ≤ i → x.time i ≤ b → v ∈ A.awake i)) := by
  classical
  simp only [awakeThroughoutOrFromTick, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A validator is in `A.activeThroughoutOrFromTick x a b` exactly when it is active after every
step whose time is in `[a, b]`, or ticks to a natural clock value at most `a` at some step `k` and is
active after every step from `k` on whose time is at most `b`.

The variables:
- `A`: the activity; `x`: the trace; `a`, `b`: the ends of the interval; `v`: the validator.

Read aloud: the two cases of active throughout `[a, b]` counted from a tick to a value at most `a`. -/
theorem mem_activeThroughoutOrFromTick {a : ℤ} {b : ℕ} {v : V} :
    v ∈ A.activeThroughoutOrFromTick x a b ↔
      ((∀ i : ℕ, x.time i ≤ b → a ≤ x.time (i + 1) → v ∈ A.active i) ∨
       (∃ k : ℕ, ∃ c : ℕ, (c : ℤ) ≤ a ∧ x.lbl k = Event.tick v c ∧
         ∀ i : ℕ, k ≤ i → x.time i ≤ b → v ∈ A.active i)) := by
  classical
  simp only [activeThroughoutOrFromTick, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A validator is in `A.awakeAtTimeOrFromTick x t` exactly when it is awake after every step whose
time is `t`, or it ticks to a natural clock value at most `t` at some step `k` and is awake after every
step from `k` on whose time is at most `t`.

The variables:
- `A`: the activity; `x`: the trace; `t`: the time; `v`: the validator.

Read aloud: the two cases of awake at `t` counted from a tick to a value at most `t`. -/
theorem mem_awakeAtTimeOrFromTick {t : ℤ} {v : V} :
    v ∈ A.awakeAtTimeOrFromTick x t ↔
      ((∀ i : ℕ, x.time i ≤ t → t ≤ x.time (i + 1) → v ∈ A.awake i) ∨
       (∃ k : ℕ, ∃ c : ℕ, (c : ℤ) ≤ t ∧ x.lbl k = Event.tick v c ∧ ∀ i : ℕ, k ≤ i → x.time i ≤ t →
         v ∈ A.awake i)) := by
  classical
  simp only [awakeAtTimeOrFromTick, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A validator awake in every configuration in force at some time of `[a, b]` is in
`A.awakeThroughoutOrFromTick x a b`.

The variables:
- `A`: the activity; `x`: the trace; `a`, `b`: the ends of the interval; `v`: the validator.

Read aloud: awake at every step of the interval is awake throughout it, from the tick or not. -/
theorem mem_awakeThroughoutOrFromTick_of_forall {a : ℤ} {b : ℕ} {v : V}
    (h : ∀ i : ℕ, x.time i ≤ b → a ≤ x.time (i + 1) → v ∈ A.awake i) :
    v ∈ A.awakeThroughoutOrFromTick x a b :=
  mem_awakeThroughoutOrFromTick.2 (Or.inl h)

/-- A validator active in every configuration in force at some time of `[a, b]` is in
`A.activeThroughoutOrFromTick x a b`.

The variables:
- `A`: the activity; `x`: the trace; `a`, `b`: the ends of the interval; `v`: the validator.

Read aloud: active at every step of the interval is active throughout it, from the tick or not. -/
theorem mem_activeThroughoutOrFromTick_of_forall {a : ℤ} {b : ℕ} {v : V}
    (h : ∀ i : ℕ, x.time i ≤ b → a ≤ x.time (i + 1) → v ∈ A.active i) :
    v ∈ A.activeThroughoutOrFromTick x a b :=
  mem_activeThroughoutOrFromTick.2 (Or.inl h)

/-- A validator that ticks to a natural clock value `c ≤ a` at step `k` and is awake after every step
from `k` on whose time is at most `b` is in `A.awakeThroughoutOrFromTick x a b`.

The variables:
- `A`: the activity; `x`: the trace; `a`, `b`: the ends of the interval; `v`: the validator; `c`: the
  clock value; `k`: the step of its tick to `c`.

Read aloud: awake from its tick to a value at most `a` through the interval is awake throughout it,
from the tick. -/
theorem mem_awakeThroughoutOrFromTick_of_tick {a : ℤ} {b k c : ℕ} {v : V} (hca : (c : ℤ) ≤ a)
    (hk : x.lbl k = Event.tick v c)
    (h : ∀ i : ℕ, k ≤ i → x.time i ≤ b → v ∈ A.awake i) :
    v ∈ A.awakeThroughoutOrFromTick x a b :=
  mem_awakeThroughoutOrFromTick.2 (Or.inr ⟨k, c, hca, hk, h⟩)

/-- A validator that ticks to a natural clock value `c ≤ a` at step `k` and is active after every
step from `k` on whose time is at most `b` is in `A.activeThroughoutOrFromTick x a b`.

The variables:
- `A`: the activity; `x`: the trace; `a`, `b`: the ends of the interval; `v`: the validator; `c`: the
  clock value; `k`: the step of its tick to `c`.

Read aloud: active from its tick to a value at most `a` through the interval is active throughout it,
from the tick. -/
theorem mem_activeThroughoutOrFromTick_of_tick {a : ℤ} {b k c : ℕ} {v : V} (hca : (c : ℤ) ≤ a)
    (hk : x.lbl k = Event.tick v c)
    (h : ∀ i : ℕ, k ≤ i → x.time i ≤ b → v ∈ A.active i) :
    v ∈ A.activeThroughoutOrFromTick x a b :=
  mem_activeThroughoutOrFromTick.2 (Or.inr ⟨k, c, hca, hk, h⟩)

/-- A validator counted awake throughout `[a, b]` by the one-case reader is counted by the two-case
reader.

The variables:
- `A`: the activity; `x`: the trace; `a`, `b`: the ends of the interval; `v`: the validator.

Read aloud: awake throughout is awake throughout, from the tick or not. -/
theorem mem_awakeThroughoutOrFromTick_of_mem_awakeThroughout {a : ℤ} {b : ℕ} {v : V}
    (h : v ∈ A.awakeThroughout x a b) : v ∈ A.awakeThroughoutOrFromTick x a b :=
  mem_awakeThroughoutOrFromTick_of_forall (mem_awakeThroughout.1 h)

/-- A validator counted active throughout `[a, b]` by the one-case reader is counted by the two-case
reader.

The variables:
- `A`: the activity; `x`: the trace; `a`, `b`: the ends of the interval; `v`: the validator.

Read aloud: active throughout is active throughout, from the tick or not. -/
theorem mem_activeThroughoutOrFromTick_of_mem_activeThroughout {a : ℤ} {b : ℕ} {v : V}
    (h : v ∈ A.activeThroughout x a b) : v ∈ A.activeThroughoutOrFromTick x a b :=
  mem_activeThroughoutOrFromTick_of_forall (mem_activeThroughout.1 h)

/-- A validator counted active throughout `[a, b]` by the two-case reader is counted awake
throughout it by the two-case reader.

The variables:
- `A`: the activity; `x`: the trace; `a`, `b`: the ends of the interval; `v`: the validator.

Read aloud: active throughout, from the tick or not, is awake throughout, from the tick or not. -/
theorem mem_awakeThroughoutOrFromTick_of_mem_activeThroughoutOrFromTick {a : ℤ} {b : ℕ} {v : V}
    (h : v ∈ A.activeThroughoutOrFromTick x a b) : v ∈ A.awakeThroughoutOrFromTick x a b := by
  rcases mem_activeThroughoutOrFromTick.1 h with h | ⟨k, c, hca, hk, h⟩
  · exact mem_awakeThroughoutOrFromTick_of_forall fun i h1 h2 =>
      Activity.mem_awake_of_mem_active (h i h1 h2)
  · exact mem_awakeThroughoutOrFromTick_of_tick hca hk fun i h0 h1 =>
      Activity.mem_awake_of_mem_active (h i h0 h1)

/-- A validator counted awake throughout `[a, b]` by the two-case reader, `a ≤ b`, is counted awake
at `a` by the per-time form.

The variables:
- `A`: the activity; `x`: the trace; `a`, `b`: the ends of the interval; `v`: the validator.

Read aloud: awake throughout an interval, from the tick or not, is awake at its first time, from the
tick or not. -/
theorem mem_awakeAtTimeOrFromTick_of_mem_awakeThroughoutOrFromTick {a : ℤ} {b : ℕ} {v : V}
    (hab : a ≤ b)
    (h : v ∈ A.awakeThroughoutOrFromTick x a b) : v ∈ A.awakeAtTimeOrFromTick x a := by
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  rcases mem_awakeThroughoutOrFromTick.1 h with h | ⟨k, c, hca, hk, h⟩
  · exact mem_awakeAtTimeOrFromTick.2
      (Or.inl fun i h1 h2 => h i (le_trans h1 hab') h2)
  · exact mem_awakeAtTimeOrFromTick.2
      (Or.inr ⟨k, c, hca, hk, fun i hki hi => h i hki (le_trans hi hab')⟩)

/-! ### The reader whose window ends at the member's own tick -/

/-- A validator is in `A.awakeThroughoutToTick x a b` exactly when it ticks to `b` at some step `k'`
and is awake after every step up to `k'`, or it ticks to a natural clock value `c ≤ a` at some step
`k ≤ k'` and is awake after every step from `k` up to `k'`.

The variables:
- `A`: the activity; `x`: the trace; `a`, `b`: the clock values that open and end the window; `v`: the
  validator.

Read aloud: the two cases of awake since the start or since a tick to a value at most `a`, up to the
tick to `b`. -/
theorem mem_awakeThroughoutToTick {a : ℤ} {b : ℕ} {v : V} :
    v ∈ A.awakeThroughoutToTick x a b ↔
      ∃ k' : ℕ, x.lbl k' = Event.tick v b ∧
        ((∀ i : ℕ, i ≤ k' → v ∈ A.awake i) ∨
         (∃ k ≤ k', ∃ c : ℕ, (c : ℤ) ≤ a ∧ x.lbl k = Event.tick v c ∧ ∀ i : ℕ, k ≤ i → i ≤ k' →
           v ∈ A.awake i)) := by
  classical
  simp only [awakeThroughoutToTick, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A validator is in `A.activeThroughoutToTick x a b` exactly when it ticks to `b` at some step `k'`
and is active after every step up to `k'`, or it ticks to a natural clock value `c ≤ a` at some step
`k ≤ k'` and is active after every step from `k` up to `k'`.

The variables:
- `A`: the activity; `x`: the trace; `a`, `b`: the clock values that open and end the window; `v`: the
  validator.

Read aloud: the two cases of active since the start or since a tick to a value at most `a`, up to the
tick to `b`. -/
theorem mem_activeThroughoutToTick {a : ℤ} {b : ℕ} {v : V} :
    v ∈ A.activeThroughoutToTick x a b ↔
      ∃ k' : ℕ, x.lbl k' = Event.tick v b ∧
        ((∀ i : ℕ, i ≤ k' → v ∈ A.active i) ∨
         (∃ k ≤ k', ∃ c : ℕ, (c : ℤ) ≤ a ∧ x.lbl k = Event.tick v c ∧ ∀ i : ℕ, k ≤ i → i ≤ k' →
           v ∈ A.active i)) := by
  classical
  simp only [activeThroughoutToTick, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A validator that ticks to `b` at step `k'` and is awake after every step up to `k'` is in
`A.awakeThroughoutToTick x a b`.

The variables:
- `A`: the activity; `x`: the trace; `a`, `b`: the clock values that open and end the window; `v`: the
  validator; `k'`: the step of its tick to `b`.

Read aloud: awake since the start up to the tick to `b` is in the reader, first case. -/
theorem mem_awakeThroughoutToTick_of_forall {a : ℤ} {b k' : ℕ} {v : V}
    (hk' : x.lbl k' = Event.tick v b)
    (h : ∀ i : ℕ, i ≤ k' → v ∈ A.awake i) :
    v ∈ A.awakeThroughoutToTick x a b :=
  mem_awakeThroughoutToTick.2 ⟨k', hk', Or.inl h⟩

/-- A validator that ticks to `b` at step `k'`, ticks to a natural clock value `c ≤ a` at a step
`k ≤ k'`, and is awake after every step from `k` up to `k'` is in `A.awakeThroughoutToTick x a b`.

The variables:
- `A`: the activity; `x`: the trace; `a`, `b`: the clock values that open and end the window; `v`: the
  validator; `c`: the clock value; `k`, `k'`: the steps of its ticks to `c` and to `b`.

Read aloud: awake from a tick to a value at most `a` up to the tick to `b` is in the reader, second
case. -/
theorem mem_awakeThroughoutToTick_of_tick {a : ℤ} {b k k' c : ℕ} {v : V} (hca : (c : ℤ) ≤ a)
    (hkk : k ≤ k') (hk' : x.lbl k' = Event.tick v b)
    (hk : x.lbl k = Event.tick v c) (h : ∀ i : ℕ, k ≤ i → i ≤ k' → v ∈ A.awake i) :
    v ∈ A.awakeThroughoutToTick x a b :=
  mem_awakeThroughoutToTick.2 ⟨k', hk', Or.inr ⟨k, hkk, c, hca, hk, h⟩⟩

/-- A validator counted by `A.activeThroughoutToTick x a b` is counted by
`A.awakeThroughoutToTick x a b`.

The variables:
- `A`: the activity; `x`: the trace; `a`, `b`: the clock values that open and end the window; `v`: the
  validator.

Read aloud: active up to the tick is awake up to the tick. -/
theorem mem_awakeThroughoutToTick_of_mem_activeThroughoutToTick {a : ℤ} {b : ℕ} {v : V}
    (h : v ∈ A.activeThroughoutToTick x a b) : v ∈ A.awakeThroughoutToTick x a b := by
  obtain ⟨k', hk', h | ⟨k, hkk, c, hca, hk, h⟩⟩ := mem_activeThroughoutToTick.1 h
  · exact mem_awakeThroughoutToTick_of_forall hk' fun i h1 =>
      Activity.mem_awake_of_mem_active (h i h1)
  · exact mem_awakeThroughoutToTick_of_tick hca hkk hk' hk fun i h1 h2 =>
      Activity.mem_awake_of_mem_active (h i h1 h2)

/-- A validator counted by `A.awakeThroughoutToTick x a b` is counted by
`A.awakeThroughoutToTick x a' b` for every `a' ≥ a`: a clock value at most `a` is at most `a'`.

The variables:
- `A`: the activity; `x`: the trace; `a`, `a'`: the two opening clock values, `a ≤ a'`; `b`: the
  clock value of the tick that ends the window; `v`: the validator.

Read aloud: awake up to the tick from a window opening at `a` is awake up to the tick from every
later opening value. -/
theorem mem_awakeThroughoutToTick_of_le {a a' : ℤ} {b : ℕ} {v : V} (haa : a ≤ a')
    (h : v ∈ A.awakeThroughoutToTick x a b) : v ∈ A.awakeThroughoutToTick x a' b := by
  obtain ⟨k', hk', h | ⟨k, hkk, c, hca, hk, h⟩⟩ := mem_awakeThroughoutToTick.1 h
  · exact mem_awakeThroughoutToTick_of_forall hk' h
  · exact mem_awakeThroughoutToTick_of_tick (le_trans hca haa) hkk hk' hk h

/-- A validator counted by `A.activeThroughoutToTick x a b` is counted by
`A.activeThroughoutToTick x a' b` for every `a' ≥ a`: a clock value at most `a` is at most `a'`.

The variables:
- `A`: the activity; `x`: the trace; `a`, `a'`: the two opening clock values, `a ≤ a'`; `b`: the
  clock value of the tick that ends the window; `v`: the validator.

Read aloud: active up to the tick from a window opening at `a` is active up to the tick from every
later opening value. -/
theorem mem_activeThroughoutToTick_of_le {a a' : ℤ} {b : ℕ} {v : V} (haa : a ≤ a')
    (h : v ∈ A.activeThroughoutToTick x a b) : v ∈ A.activeThroughoutToTick x a' b := by
  obtain ⟨k', hk', h | ⟨k, hkk, c, hca, hk, h⟩⟩ := mem_activeThroughoutToTick.1 h
  · exact mem_activeThroughoutToTick.2 ⟨k', hk', Or.inl h⟩
  · exact mem_activeThroughoutToTick.2 ⟨k', hk', Or.inr ⟨k, hkk, c, le_trans hca haa, hk, h⟩⟩

/-- The third-of-the-validators premise read up to `t` is read up to any earlier time.

The variables:
- `A`: the activity; `x`: the trace; `n`: the number of validators; `t`, `t'`: the two times.

Read aloud: the premise at `t` gives the premise at every `t' ≤ t`. -/
theorem AdversaryFewerThanThirdUntil.mono {n : ℕ} {t' t : ℝ}
    (h : A.AdversaryFewerThanThirdUntil x n t) (hle : t' ≤ t) :
    A.AdversaryFewerThanThirdUntil x n t' :=
  fun X hX => h X (fun v hv => by
    obtain ⟨i, hi, hmem⟩ := hX v hv
    exact ⟨i, le_trans hi hle, hmem⟩)

/-- The two-thirds premise read up to `t` is read up to any earlier time.

The variables:
- `A`: the activity; `x`: the trace; `n`: the number of validators; `t`, `t'`: the two times.

Read aloud: the premise at `t` gives the premise at every `t' ≤ t`. -/
theorem AdversaryFewerThanTwoThirdsUntil.mono {n : ℕ} {t' t : ℝ}
    (h : A.AdversaryFewerThanTwoThirdsUntil x n t) (hle : t' ≤ t) :
    A.AdversaryFewerThanTwoThirdsUntil x n t' :=
  fun X hX => h X (fun v hv => by
    obtain ⟨i, hi, hmem⟩ := hX v hv
    exact ⟨i, le_trans hi hle, hmem⟩)

/-- The quorum premise read up to `t` is read up to any earlier time.

The variables:
- `A`: the activity; `x`: the trace; `q`: the bound; `t`, `t'`: the two times.

Read aloud: the premise at `t` gives the premise at every `t' ≤ t`. -/
theorem AdversaryFewerThanQuorumUntil.mono {q : ℕ} {t' t : ℝ}
    (h : A.AdversaryFewerThanQuorumUntil x q t) (hle : t' ≤ t) :
    A.AdversaryFewerThanQuorumUntil x q t' :=
  fun X hX => h X (fun v hv => by
    obtain ⟨i, hi, hmem⟩ := hX v hv
    exact ⟨i, le_trans hi hle, hmem⟩)

/-- Honesty up to a time gives honesty up to every earlier time.

The variables:
- `A`: the activity; `x`: the trace; `t`, `t'`: the two times; `v`: the validator.

Read aloud: a validator honest up to `t` is honest up to any `t' ≤ t`. -/
theorem HonestThroughTime.mono {t t' : ℝ} {v : V} (hle : t' ≤ t)
    (h : A.HonestThroughTime x t v) : A.HonestThroughTime x t' v :=
  fun i hi => h i (le_trans hi hle)

end Activity

/-- What the environment promises on the trace `x` under the activity `A`, for the messages of
the class `ok`, with the vocabulary `W`: that time diverges, that corruption is permanent, which
validators tick, restart and are delivered messages and when, what a step of another kind may put on
the wire, that a validator's clock comes to read a clock value `t` (by a tick or a restart) at a real
time in `[t − ΔClockAhead, t + ΔClockBehind]`, that a validator outside the adversary set does not set its
clock back, and that an honest validator's message is delivered to a receiver `v` active since the
message was on the wire before every tick of `v` at a time at least the deadline
`deadline sm a` (`a` the time the message was on the wire) and, when the message has a release
reading `release sm.msg = some r`, at least `ΔRedeliver` after the time of `v`'s first tick at a
reading at least `r` after a delivery that found `v` not yet reacted to `r`; such a delivery
finds `v` already reacted to `r` when `r` is at most the tick's reading. `none` is "nothing promised" for that message. What the honest
validators' own steps put on the wire is the protocol's, not the environment's, and is not a field
here.

The variables:
- `A`: the activity; `x`: the trace; `ΔClockAhead`, `ΔClockBehind`: how far before and after the
  real time `t` a clock may come to read the clock value `t` (one shared clock is `0`, `0`);
  `deadline sm a`: the deadline of the message `sm` on the wire at `a`; `release m`: the clock reading from which the object of the message `m` may be processed
  (`none`: from any reading); `ΔRedeliver`: the delay of a delivery after the receiver's first tick
  at a reading at least the release reading; `ok`: the class of messages; `W`: the vocabulary. -/
structure EnvFactsBy {V Msg N : Type} [DecidableEq V] [DecidableEq Msg] (A : Activity V)
    (x : Trace V Msg N) (ΔClockAhead ΔClockBehind : ℝ)
    (deadline : (sm : SignedMsg V Msg) → (a : ℝ) → Option ℝ)
    (release : (m : Msg) → Option ℕ) (ΔRedeliver : ℕ)
    (ok : (m : Msg) → Prop) {B : Type} (W : ViewVocab V B Msg) : Prop where
  /-- Every time is reached: for every natural number `t`, some step is at a real time at least
  `t`. -/
  time_div : ∀ t : ℕ, ∃ i : ℕ, (t : ℝ) ≤ x.time i
  /-- Corruption is permanent: a validator in the adversary set after `i` steps is in it after
  every later step. -/
  corrupted_mono : ∀ i i' : ℕ, i ≤ i' → A.corrupted i ⊆ A.corrupted i'
  /-- The adversary set is the same before and after every tick, restart and delivery: only a step
  of the kind `other` changes it. -/
  corrupted_keep : ∀ i : ℕ, x.lbl i ≠ Event.other → A.corrupted (i + 1) = A.corrupted i
  /-- The clock-ahead bound is not negative: `ΔClockAhead` is how far ahead of the real time a
  clock may read. -/
  ahead_nonneg : 0 ≤ ΔClockAhead
  /-- The clock-behind bound is not negative: `ΔClockBehind` is how far behind the real time a
  clock may read. -/
  behind_nonneg : 0 ≤ ΔClockBehind
  /-- Every validator active after every step whose real time is in
  `[t − ΔClockAhead, t + ΔClockBehind]`, for a clock value `t ≥ 1`, ticks to `t` at a step whose real
  time is in that window. -/
  tick_of_active : ∀ t : ℕ, 1 ≤ t → ∀ v : V,
    (∀ i : ℕ, (t : ℝ) - ΔClockAhead ≤ x.time i → x.time i ≤ t + ΔClockBehind → v ∈ A.active i) →
    ∃ i : ℕ, x.lbl i = Event.tick v t ∧ (t : ℝ) - ΔClockAhead ≤ x.time i ∧
      x.time i ≤ t + ΔClockBehind
  /-- A tick to the clock value `t` is by a validator active in the configuration it starts from, at
  a step whose real time is in `[t − ΔClockAhead, t + ΔClockBehind]`. -/
  tick_active : ∀ (i : ℕ) (v : V) (t : ℕ), x.lbl i = Event.tick v t →
    v ∈ A.active i ∧ (t : ℝ) - ΔClockAhead ≤ x.time i ∧ x.time i ≤ t + ΔClockBehind
  /-- A validator ticks at most once to each reading: two steps that are `v`'s tick to `t` are the
  same step. -/
  tick_unique : ∀ (i j : ℕ) (v : V) (t : ℕ), x.lbl i = Event.tick v t → x.lbl j = Event.tick v t →
    i = j
  /-- A restart is by a validator not awake in the configuration it starts from and awake after
  it. -/
  restart_crashed : ∀ (i : ℕ) (v : V) (t : ℕ) (keep : Bool), x.lbl i = Event.restart v t keep →
    v ∉ A.awake i ∧ v ∈ A.awake (i + 1)
  /-- A restart at the clock value `t` is at a step whose real time is in
  `[t − ΔClockAhead, t + ΔClockBehind]`. -/
  restart_time : ∀ (i : ℕ) (v : V) (t : ℕ) (keep : Bool), x.lbl i = Event.restart v t keep →
    (t : ℝ) - ΔClockAhead ≤ x.time i ∧ x.time i ≤ t + ΔClockBehind
  /-- A validator outside the adversary set in the configuration a step starts from does not set its
  clock back at that step: when `v` ticks or restarts to the clock value `t` at step `i`, and ticks or
  restarts to `t'` at a later step `j`, and `v` is outside the adversary set in the configuration step
  `j` starts from, then `t ≤ t'`. Nothing is promised of a validator in the adversary set. -/
  clock_mono : ∀ (i j : ℕ) (v : V) (t t' : ℕ), i < j → v ∉ A.corrupted j →
    (x.lbl i = Event.tick v t ∨ ∃ keep, x.lbl i = Event.restart v t keep) →
    (x.lbl j = Event.tick v t' ∨ ∃ keep, x.lbl j = Event.restart v t' keep) → t ≤ t'
  /-- A validator not awake before a step and awake after it was restarted at that step. -/
  restart_of_awake : ∀ (i : ℕ) (v : V), v ∉ A.awake i → v ∈ A.awake (i + 1) →
    ∃ (t : ℕ) (keep : Bool), x.lbl i = Event.restart v t keep
  /-- A delivery is to a validator active in the configuration it starts from. -/
  deliver_active : ∀ (i : ℕ) (v : V) (sm : SignedMsg V Msg), x.lbl i = Event.deliver v sm →
    v ∈ A.active i
  /-- A step of another kind puts on the wire only copies of messages already on the wire, or
  messages signed by a validator in the adversary set in the configuration the step starts from
  that forge no honest validator: for the message's object, and for every object it includes, when
  the object is attributed to a validator `u` outside the adversary set after every step up to that
  one, the sent log before the step already holds `u`'s own signed message with that object.

  This is the environment's half of unforgeability: the adversary puts on the wire no object of an
  honest validator that the validator has not itself put on the wire. The other half, that the
  steps of honest validators forge no honest validator either, is not promised by the environment:
  it follows from what the protocol's tick, restart and receive reactions send. -/
  other_sent : ∀ (i : ℕ) (sm : SignedMsg V Msg), x.lbl i = Event.other →
    sm ∈ x.sent (i + 1) - x.sent i →
    sm ∈ x.sent i ∨
    (sm.sender ∈ A.corrupted i ∧
     ∀ (o' : Msg) (u : V), (o' = sm.msg ∨ W.carries sm.msg o') → W.author o' = some u →
       A.HonestThroughStep i u → (⟨u, o'⟩ : SignedMsg V Msg) ∈ x.sent i)
  /-- At `v`'s tick `k` to the reading `t`, every message `sm` of the class `ok` that an honest
  validator put on the wire at a step `i` before `k`, with `v` active after every step from `i + 1`
  to `k`, whose deadline `d` (from the time after step `i`) is at most the time of step `k`, and,
  when its object has a release reading `r` and a delivery of `sm` to `v` after the sending found
  `v` not yet reacted to `r`, whose re-delivery deadline (`ΔRedeliver` after the time of `v`'s first
  tick at a reading at least `r` after that delivery) is also at most the time of step `k`, was
  delivered to `v` at a step `j` between `i` and `k`; when the release reading `r` is at most `t`,
  that delivery found `v` already reacted to `r`; and no step between `j` and `k` is a restart of
  `v` that loses its memory. -/
  delivered : ∀ (i k : ℕ) (v : V) (sm : SignedMsg V Msg) (t : ℕ) (d : ℝ),
    x.HonestSendAt A i sm → ok sm.msg → x.lbl k = Event.tick v t → i < k →
    (∀ j : ℕ, i + 1 ≤ j → j ≤ k → v ∈ A.active j) →
    deadline sm (x.time (i + 1)) = some d → d ≤ x.time k →
    -- after a delivery `j₀` that found `v` not yet reacted to `r`, the re-delivery deadline
    -- (`ΔRedeliver` after `v`'s first tick `k₁` at a reading at least `r`) is at most the time of `k`
    (∀ (r j₀ k₁ t₁ : ℕ), release sm.msg = some r →
      i < j₀ → x.lbl j₀ = Event.deliver v sm → ¬ x.ReactedAtLeast j₀ v r →
      j₀ < k₁ → k₁ ≤ k → x.lbl k₁ = Event.tick v t₁ → r ≤ t₁ →
      (∀ (l t' : ℕ), j₀ < l → l < k₁ → x.lbl l = Event.tick v t' → t' < r) →
      x.time (k₁ + 1) + ΔRedeliver ≤ x.time k) →
    ∃ j : ℕ, i < j ∧ j < k ∧ x.lbl j = Event.deliver v sm ∧
      (∀ r : ℕ, release sm.msg = some r → r ≤ t → x.ReactedAtLeast j v r) ∧
      ∀ (l t' : ℕ), j < l → l < k → x.lbl l ≠ Event.restart v t' false

/-- `syncDeadline Δ GST`: the ordinary deadline `max a GST + Δ` of a message on the wire at `a`,
always promised.

The variables:
- `α`: the type of the times (the real numbers for the delivery promise, the natural numbers for the
  sync fact); `Δ`: the delay; `GST`: the time from which the network is synchronous.

Read aloud: a message is due `Δ` after the later of its time and `GST`. -/
def syncDeadline {V Msg α : Type} [Max α] [Add α] (Δ GST : α) :
    (sm : SignedMsg V Msg) → (a : α) → Option α :=
  fun _ a => some (max a GST + Δ)

/-- `syncCatchUp Δ Δw GST`: the catch-up deadline of a message on the wire at `a` for a validator
restarted at the time `t`: the later of the message's ordinary deadline and `max t GST + Δw`.

The variables:
- `α`: the type of the times; `Δ`: the delay; `Δw`: the catch-up delay; `GST`: the time from which
  the network is synchronous.

Read aloud: a restarted validator is due an earlier message by the later of the message's own
deadline and `Δw` after the later of its restart and `GST`. -/
def syncCatchUp {V Msg α : Type} [Max α] [Add α] (Δ Δw GST : α) :
    (sm : SignedMsg V Msg) → (a : α) → (t : α) → Option α :=
  fun _ a t => some (max (max a GST + Δ) (max t GST + Δw))

/-- `CatchUpAfterRestartBy A x catchUp release ΔRedeliver ok`: a validator `v` restarted at a step `k`
after the step `i` at which an honest validator put a message `sm` of the class `ok` on the wire
(`i < k`, so a restart at the time of the sending, after it, is covered), whose catch-up deadline `c`
for that message (from the message's time and the restart's time) is defined, and that ticks at a
step `k' > k` to a clock value `c'` at least `c`, active after every step `j` with `k < j ≤ k'`: when
the object of `sm` has a release clock value `r` and a delivery of `sm` to `v` after the restart found
`v` not yet reacted to `r`, provided that the re-delivery deadline (`ΔRedeliver` after the time of
`v`'s first tick after that delivery at a clock value at least `r`) is at most the time of `k'`, `v` is
delivered `sm` at a step `j` with `k < j < k'`; when `r` is at most `c'`, that delivery found `v`
already reacted to `r`; and no step between `j` and `k'` is a restart of `v` that loses its memory.
`none` is "nothing promised".

This is the shape of the delivery promise `delivered`: the tick read is any tick of `v`
after the restart at a clock value at least `c`, not only the first; the receiver's window ends at that
tick, and nothing is asked of the steps after it, nor promised about them.

The variables:
- `A`: the activity; `x`: the trace; `catchUp sm a t`: the catch-up deadline of the message `sm` on
  the wire at `a` for a validator restarted at `t`; `release m`: the clock value from which the
  receiver admits the object of the message `m` (`none`: from any); `ΔRedeliver`: the delay of a
  re-delivery after the receiver's first tick at a clock value at least it; `ok`: the class of
  messages.

Read aloud: a restarted validator that stays up from its restart to any of its ticks, after the
restart, at a clock value at least its catch-up deadline is delivered every earlier honest message
before that tick, with no memory-losing restart in between; and, when the object's release clock
value is at most that tick's, the delivery found the validator's clock already there, provided a
re-delivery after its clock reached that value would come before the tick. -/
def CatchUpAfterRestartBy {V Msg N : Type} [DecidableEq V] [DecidableEq Msg] (A : Activity V)
    (x : Trace V Msg N) (catchUp : (sm : SignedMsg V Msg) → (a : ℝ) → (t : ℝ) → Option ℝ)
    (release : (m : Msg) → Option ℕ) (ΔRedeliver : ℕ) (ok : (m : Msg) → Prop) : Prop :=
  ∀ (i k : ℕ) (v : V) (sm : SignedMsg V Msg) (t : ℕ) (keep : Bool) (c : ℝ) (k' c' : ℕ),
    x.HonestSendAt A i sm → ok sm.msg → x.lbl k = Event.restart v t keep →
    i < k →
    catchUp sm (x.time (i + 1)) (x.time k) = some c →
    k < k' → x.lbl k' = Event.tick v c' → c ≤ (c' : ℝ) →
    (∀ j : ℕ, k < j → j ≤ k' → v ∈ A.active j) →
    -- after a delivery `j₀` after the restart that found `v` not yet reacted to `r`, the re-delivery
    -- deadline (`ΔRedeliver` after `v`'s first tick `k₁` at a clock value at least `r`) is at most the
    -- time of `k'`
    (∀ (r j₀ k₁ t₁ : ℕ), release sm.msg = some r →
      k < j₀ → x.lbl j₀ = Event.deliver v sm → ¬ x.ReactedAtLeast j₀ v r →
      j₀ < k₁ → k₁ ≤ k' → x.lbl k₁ = Event.tick v t₁ → r ≤ t₁ →
      (∀ (l t' : ℕ), j₀ < l → l < k₁ → x.lbl l = Event.tick v t' → t' < r) →
      x.time (k₁ + 1) + ΔRedeliver ≤ x.time k') →
    ∃ j : ℕ, k < j ∧ j < k' ∧ x.lbl j = Event.deliver v sm ∧
      (∀ r : ℕ, release sm.msg = some r → r ≤ c' → x.ReactedAtLeast j v r) ∧
      ∀ (l t' : ℕ), j < l → l < k' → x.lbl l ≠ Event.restart v t' false

/-- `EnvFactsDelivery A x ΔClockAhead ΔClockBehind Δ ΔRedeliver GST release ok W`: the environment's promises with every
message of the class `ok` due `Δ` after the later of its time and `GST`, and a message whose object
has a release reading also due `ΔRedeliver` after the receiver's first tick at a reading at least it.

The variables:
- `A`: the activity; `x`: the trace; `ΔClockAhead`, `ΔClockBehind`: the two bounds of the clocks;
  `Δ`: the delay; `ΔRedeliver`: the re-delivery delay; `GST`:
  the time from which the network is synchronous; `release`: the release reading of a message's
  object; `ok`: the class of messages; `W`: the vocabulary.

Read aloud: the environment keeps its non-delivery facts and the synchronous delivery promise. -/
abbrev EnvFactsDelivery {V Msg N : Type} [DecidableEq V] [DecidableEq Msg] (A : Activity V)
    (x : Trace V Msg N) (ΔClockAhead ΔClockBehind : ℝ) (Δ ΔRedeliver GST : ℕ) (release : (m : Msg) → Option ℕ)
    (ok : (m : Msg) → Prop) {B : Type} (W : ViewVocab V B Msg) : Prop :=
  EnvFactsBy A x ΔClockAhead ΔClockBehind (syncDeadline (α := ℝ) Δ GST) release ΔRedeliver ok W

/-- `EnvFactsSync A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver GST release ok W`: the synchronous network from `GST` on,
messages delivered within `Δ` (and within `ΔRedeliver` of the receiver's first tick at a reading at
least a message's release reading), and a restarted validator caught up within `Δw` of the later of
its restart and `GST`. -/
structure EnvFactsSync {V Msg N : Type} [DecidableEq V] [DecidableEq Msg] (A : Activity V)
    (x : Trace V Msg N) (ΔClockAhead ΔClockBehind : ℝ) (Δ Δw ΔRedeliver GST : ℕ) (release : (m : Msg) → Option ℕ)
    (ok : (m : Msg) → Prop) {B : Type}
    (W : ViewVocab V B Msg) : Prop extends
    EnvFactsBy A x ΔClockAhead ΔClockBehind (syncDeadline (α := ℝ) Δ GST) release ΔRedeliver ok W where
  /-- A restarted validator that stays up is delivered every earlier honest message of the class
  `ok` by the later of the message's deadline and `Δw` after the later of its restart and `GST`. -/
  caught_up : CatchUpAfterRestartBy A x (syncCatchUp (α := ℝ) Δ Δw GST) release ΔRedeliver ok

/-- `EnvFactsNoDelivery A x ΔClockAhead ΔClockBehind W`: the environment's promises with no delivery promised at all (no
deadline, no release reading, re-delivery delay `0`).

The variables:
- `A`: the activity; `x`: the trace; `ΔClockAhead`, `ΔClockBehind`: the two bounds of the clocks; `W`:
  the vocabulary.

Read aloud: the environment keeps every promise except delivery, of which it promises nothing. -/
abbrev EnvFactsNoDelivery {V Msg N : Type} [DecidableEq V] [DecidableEq Msg] (A : Activity V)
    (x : Trace V Msg N) (ΔClockAhead ΔClockBehind : ℝ) {B : Type} (W : ViewVocab V B Msg) : Prop :=
  EnvFactsBy A x ΔClockAhead ΔClockBehind (fun _ _ => none) (fun _ => none) 0 (fun _ => True) W

/-- `EnvFacts A x ΔClockAhead ΔClockBehind Δ ΔRedeliver GST release ok W`: `EnvFactsSync A x ΔClockAhead ΔClockBehind Δ Δ ΔRedeliver GST release ok W`,
the synchronous promises with the catch-up delay equal to the delay `Δ`.

The variables:
- `A`: the activity; `x`: the trace; `ΔClockAhead`, `ΔClockBehind`: the two bounds of the clocks;
  `Δ`: the delay; `ΔRedeliver`: the re-delivery delay; `GST`: the
  time from which the network is synchronous; `release`: the release reading of a message's object;
  `ok`: the class of messages; `W`: the vocabulary.

Read aloud: the environment's promises, with every message due `Δ` after the later of its time
and `GST`, and a restarted validator's backlog due `Δ` after the later of its restart and `GST`. -/
abbrev EnvFacts {V Msg N : Type} [DecidableEq V] [DecidableEq Msg] (A : Activity V)
    (x : Trace V Msg N) (ΔClockAhead ΔClockBehind : ℝ) (Δ ΔRedeliver GST : ℕ)
    (release : (m : Msg) → Option ℕ) (ok : (m : Msg) → Prop) {B : Type} (W : ViewVocab V B Msg) :
    Prop :=
  EnvFactsSync A x ΔClockAhead ΔClockBehind Δ Δ ΔRedeliver GST release ok W

namespace EnvFactsBy

variable {V Msg N : Type} [DecidableEq V] [DecidableEq Msg] {A : Activity V} {x : Trace V Msg N}
  {ΔClockAhead ΔClockBehind : ℝ} {deadline : SignedMsg V Msg → ℝ → Option ℝ} {release : (m : Msg) → Option ℕ} {ΔRedeliver : ℕ}
  {ok : (m : Msg) → Prop} {B : Type} {W : ViewVocab V B Msg}

/-- Once time is promised to reach `t`, the first step at which the time has reached `t` is at a
time at least `t`.

The variables:
- `E`: the environment's facts; `t`: the time.

Read aloud: `x.firstAt t` is at time `t` or later. -/
theorem le_time_firstAt (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W) (t : ℕ) :
    (t : ℝ) ≤ x.time (x.firstAt t) := by
  classical
  unfold Trace.firstAt
  rw [dif_pos (E.time_div t)]
  exact Nat.find_spec (E.time_div t)

/-- A validator outside the adversary set after step `i'` is outside it after every earlier step.

The variables:
- `E`: the environment's facts; `i`, `i'`: the two steps; `v`: the validator.

Read aloud: a validator honest after step `i'` was honest after every step `i ≤ i'`. -/
theorem not_mem_corrupted_of_le (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W) {i i' : ℕ}
    (hle : i ≤ i') {v : V} (h : v ∉ A.corrupted i') : v ∉ A.corrupted i :=
  fun hv => h (E.corrupted_mono i i' hle hv)

/-- A validator outside the adversary set after step `i` has been honest up to step `i`.

The variables:
- `E`: the environment's facts; `i`: the step; `v`: the validator.

Read aloud: honest after step `i` means honest up to step `i`. -/
theorem honestThroughStep_of_not_mem (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W) {i : ℕ} {v : V}
    (h : v ∉ A.corrupted i) : A.HonestThroughStep i v :=
  fun _ hi' => E.not_mem_corrupted_of_le hi' h

/-- A restarted validator is awake after its restart.

The variables:
- `E`: the environment's facts; `i`: the step; `v`: the validator; `t`: the reading; `keep`: whether
  it keeps its memory.

Read aloud: a validator is up after its restart. -/
theorem awake_succ_of_restart (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W) {i : ℕ} {v : V} {t : ℕ}
    {keep : Bool} (hl : x.lbl i = Event.restart v t keep) : v ∈ A.awake (i + 1) :=
  (E.restart_crashed i v t keep hl).2

/-- A validator that ticks at step `i` is outside the adversary set in the configuration the step
starts from.

The variables:
- `E`: the environment's facts; `i`: the step; `v`: the validator; `t`: the reading.

Read aloud: only honest validators tick. -/
theorem not_mem_corrupted_of_tick (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W) {i : ℕ} {v : V}
    {t : ℕ} (hl : x.lbl i = Event.tick v t) : v ∉ A.corrupted i :=
  Activity.not_mem_corrupted_of_mem_active (E.tick_active i v t hl).1

/-- A validator that ticks at step `i` is outside the adversary set in the configuration after that
step too: a tick is by an active validator, and it does not change the adversary set (`corrupted_keep`).

The variables:
- `E`: the environment's facts; `i`: the step; `v`: the validator; `t`: the reading.

Read aloud: a validator that ticks is still honest right after its tick. -/
theorem not_mem_corrupted_succ_of_tick (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W) {i : ℕ}
    {v : V} {t : ℕ} (hl : x.lbl i = Event.tick v t) : v ∉ A.corrupted (i + 1) := by
  rw [E.corrupted_keep i (by rw [hl]; simp)]
  exact E.not_mem_corrupted_of_tick hl

/-- A validator outside the adversary set in the configuration step `j` starts from, and ticking or
restarting to the clock value `t` at step `j`, has a clock value at most `t` before that step
(`clock_mono`, with `clockValue_cases`: the clock value is `0` or was set by an earlier tick or
restart of `v`).

The variables:
- `E`: the environment's facts; `j`: the step; `v`: the validator; `t`: the clock value of the step;
  `hv`: `v` is outside the adversary set in the configuration step `j` starts from; `hl`: step `j` is
  `v`'s tick or restart to `t`.

Read aloud: an honest validator never ticks or restarts to a clock value less than its clock value. -/
theorem clockValue_le_of_set (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    {j : ℕ} {v : V} {t : ℕ} (hv : v ∉ A.corrupted j)
    (hl : x.lbl j = Event.tick v t ∨ ∃ keep, x.lbl j = Event.restart v t keep) :
    x.clockValue j v ≤ t := by
  rcases x.clockValue_cases j v with ⟨h0, -⟩ | ⟨j', hj', hset, -⟩
  · rw [h0]; exact Nat.zero_le t
  · exact E.clock_mono j' j v _ t hj' hv hset hl

/-- The clock value of a validator outside the adversary set after `i` steps never decreases up to
step `i`: for `j ≤ i`, `x.clockValue j v ≤ x.clockValue i v` (`clockValue_le_of_set` at every tick
and restart of `v` between, with corruption permanent, `corrupted_mono`).

The variables:
- `E`: the environment's facts; `j`, `i`: the two steps; `v`: the validator; `hji`: `j ≤ i`; `hv`:
  `v` is outside the adversary set after `i` steps.

Read aloud: an honest validator's clock value never goes back. -/
theorem clockValue_mono (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    {j i : ℕ} {v : V} (hji : j ≤ i) (hv : v ∉ A.corrupted i) :
    x.clockValue j v ≤ x.clockValue i v := by
  classical
  induction i, hji using Nat.le_induction with
  | base => exact le_rfl
  | succ i hji ih =>
    have hvi : v ∉ A.corrupted i := fun h => hv (E.corrupted_mono i (i + 1) (Nat.le_succ i) h)
    refine le_trans (ih hvi) ?_
    by_cases ht : ∃ t : ℕ, x.lbl i = Event.tick v t
    · obtain ⟨t, ht⟩ := ht
      rw [x.clockValue_succ_of_tick ht]
      exact E.clockValue_le_of_set hvi (Or.inl ht)
    by_cases hr : ∃ (t : ℕ) (keep : Bool), x.lbl i = Event.restart v t keep
    · obtain ⟨t, keep, hr⟩ := hr
      rw [x.clockValue_succ_of_restart hr]
      exact E.clockValue_le_of_set hvi (Or.inr ⟨keep, hr⟩)
    rw [x.clockValue_succ_of_not (fun t h => ht ⟨t, h⟩) (fun t keep h => hr ⟨t, keep, h⟩)]

/-- At every time `t ≥ 0` some configuration is in force: some step `i` has
`x.time i ≤ t ≤ x.time (i + 1)`. The time starts at `0`, never goes back, and reaches every natural
number (`time_div`).

The variables:
- `E`: the environment's facts; `h0`: the time starts at `0`; `htime`: the time is monotone; `t`:
  the time.

Read aloud: at every time from `0` on, the run is in some configuration. -/
theorem exists_inForce (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    (h0 : x.time 0 = 0) (htime : Monotone x.time) {t : ℝ} (ht : 0 ≤ t) :
    ∃ i : ℕ, x.time i ≤ t ∧ t ≤ x.time (i + 1) := by
  classical
  obtain ⟨j, hj⟩ := E.time_div (Nat.ceil t)
  have hex : ∃ i : ℕ, t ≤ x.time i := ⟨j, le_trans (Nat.le_ceil t) hj⟩
  have hi : t ≤ x.time (Nat.find hex) := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos (Nat.find hex) with hz | hpos
  · have h0t : t = 0 := le_antisymm (by rw [hz] at hi; rw [h0] at hi; exact hi) ht
    exact ⟨0, by rw [h0, h0t], by rw [h0t, ← h0]; exact htime (Nat.zero_le 1)⟩
  · refine ⟨Nat.find hex - 1, le_of_not_ge (Nat.find_min hex (by omega)), ?_⟩
    rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega]
    exact hi

/-- A validator counted active throughout `[a, b]`, `a ≤ b`, is outside `A.corruptedAtTime x b`: it
is active in the configuration in force at `b` (`exists_inForce`), and corruption is permanent
(`corrupted_mono`). Moved here from the readers' kit, since it reads the environment.

The variables:
- `E`: the environment's facts; `h0`: the time starts at `0`; `htime`: the time is monotone; `a`,
  `b`: the ends of the interval; `v`: the validator.

Read aloud: active throughout an interval is honest up to its end. -/
theorem not_mem_corruptedAtTime_of_mem_activeThroughout [Fintype V]
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    (h0 : x.time 0 = 0) (htime : Monotone x.time) {v : V} {a b : ℝ} (hab : a ≤ b)
    (hv : v ∈ A.activeThroughout x a b) : v ∉ A.corruptedAtTime x b := by
  rw [Activity.not_mem_corruptedAtTime]
  intro i hi hci
  have hb : 0 ≤ b := le_trans (by rw [← h0]; exact htime (Nat.zero_le i)) hi
  obtain ⟨j, hj1, hj2⟩ := E.exists_inForce h0 htime hb
  rcases le_or_gt i j with hij | hij
  · exact Activity.not_mem_corrupted_of_mem_active
      (Activity.mem_activeThroughout.1 hv j hj1 (le_trans hab hj2)) (E.corrupted_mono i j hij hci)
  · exact Activity.not_mem_corrupted_of_mem_active
      (Activity.mem_activeThroughout.1 hv i hi
        (le_trans hab (le_trans hj2 (le_trans (htime hij) (htime (Nat.le_succ i)))))) hci

/-- When `v` ticks to the clock value `d`, the step of that tick is at a real time in
`[d − ΔClockAhead, d + ΔClockBehind]`.

The variables:
- `E`: the environment's facts; `v`: the validator; `d`: the clock value; `hk`: some step is `v`'s
  tick to `d`.

Read aloud: `v`'s tick to `d` happens within the two bounds of the real time `d`. -/
theorem time_tickStep (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    {v : V} {d : ℕ} (hk : ∃ i : ℕ, x.lbl i = Event.tick v d) :
    (d : ℝ) - ΔClockAhead ≤ x.time (x.tickStep v d) ∧ x.time (x.tickStep v d) ≤ d + ΔClockBehind :=
  (E.tick_active _ v d (x.lbl_tickStep hk)).2

/-- A step at a real time less than `d − ΔClockAhead` comes before `v`'s tick to `d`, when `v` ticks
to `d`.

The variables:
- `E`: the environment's facts; `htime`: the time is monotone in the step; `v`: the validator;
  `d`: the clock value; `j`: the step.

Read aloud: what happens before real time `d − ΔClockAhead` happens before `v`'s tick to `d`. -/
theorem lt_tickStep_of_time_lt (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    (htime : Monotone x.time) {v : V} {d j : ℕ} (hk : ∃ i : ℕ, x.lbl i = Event.tick v d)
    (hj : x.time j < (d : ℝ) - ΔClockAhead) : j < x.tickStep v d :=
  x.lt_tickStep_of_time_lt htime hk (fun i hi => (E.tick_active i v d hi).2.1) hj

/-- A step before `v`'s tick to `d` is at a real time at most `d + ΔClockBehind`.

The variables:
- `E`: the environment's facts; `htime`: the time is monotone in the step; `v`: the validator;
  `d`: the clock value; `j`: the step.

Read aloud: what happens before `v`'s tick to `d` happens by real time `d + ΔClockBehind`. -/
theorem time_le_of_lt_tickStep (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    (htime : Monotone x.time) {v : V} {d j : ℕ} (hj : j < x.tickStep v d) :
    x.time j ≤ d + ΔClockBehind :=
  le_trans (htime hj.le) (E.time_tickStep (x.exists_tick_of_lt_tickStep hj)).2

/-- Before `v`'s tick to `d` is before `v`'s tick to every clock value `d'` to which `v` ticks whose
window lies wholly after `d`'s: `d + ΔClockBehind < d' − ΔClockAhead`.

The variables:
- `E`: the environment's facts; `htime`: the time is monotone in the step; `v`: the validator;
  `d`, `d'`: the two clock values; `j`: the step.

Read aloud: a tick to a value whose window lies wholly after another's comes later. -/
theorem lt_tickStep_mono (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    (htime : Monotone x.time) {v : V} {d d' j : ℕ}
    (hdd : (d : ℝ) + ΔClockBehind < (d' : ℝ) - ΔClockAhead)
    (hk' : ∃ i : ℕ, x.lbl i = Event.tick v d') (hj : j < x.tickStep v d) : j < x.tickStep v d' := by
  have h1 := E.time_tickStep (x.exists_tick_of_lt_tickStep hj)
  have h2 := E.time_tickStep hk'
  have : x.tickStep v d < x.tickStep v d' := by
    by_contra hc
    have := htime (Nat.le_of_not_lt hc)
    linarith
  omega

/-- A validator counted active throughout `[a, b]` ticks to every clock value `t ≥ 1` whose window
`[t − ΔClockAhead, t + ΔClockBehind]` lies in `[a, b]`, at a step whose real time is in that window.

The variables:
- `E`: the environment's facts; `v`: the validator; `a`, `b`: the ends of the interval; `t`: the
  clock value.

Read aloud: a validator active throughout an interval ticks to each clock value from `1` on whose
window the interval holds. -/
theorem tick_of_mem_activeThroughout [Fintype V]
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    (htime : Monotone x.time) {v : V} {a b : ℝ} {t : ℕ} (hv : v ∈ A.activeThroughout x a b)
    (ha : a ≤ (t : ℝ) - ΔClockAhead) (hb : (t : ℝ) + ΔClockBehind ≤ b) (h1 : 1 ≤ t) :
    ∃ i : ℕ, x.lbl i = Event.tick v t ∧ (t : ℝ) - ΔClockAhead ≤ x.time i ∧
      x.time i ≤ t + ΔClockBehind :=
  E.tick_of_active t h1 v fun i h1' h2' =>
    Activity.mem_active_of_mem_activeThroughout_of_time htime hv (le_trans ha h1') (le_trans h2' hb)

/-- A validator counted awake throughout `[a, b]` is awake after every step from its tick to the
clock value `a₀` to its tick to the clock value `b₀`, when `[a₀ − ΔClockAhead, b₀ + ΔClockBehind]`
lies in `[a, b]`.

The variables:
- `E`: the environment's facts; `htime`: the time is monotone in the step; `v`: the validator; `a`,
  `b`: the ends of the interval; `a₀`, `b₀`: the two clock values; `k`, `k'`: the steps of its ticks
  to `a₀` and to `b₀`; `i`: the step.

Read aloud: a validator awake throughout an interval is awake between two of its ticks whose windows
the interval holds. -/
theorem awake_of_mem_awakeThroughout [Fintype V]
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    (htime : Monotone x.time) {v : V} {a b : ℝ} {a₀ b₀ k k' i : ℕ}
    (hv : v ∈ A.awakeThroughout x a b) (ha : a ≤ (a₀ : ℝ) - ΔClockAhead)
    (hb : (b₀ : ℝ) + ΔClockBehind ≤ b)
    (hk : x.lbl k = Event.tick v a₀) (hk' : x.lbl k' = Event.tick v b₀) (hki : k ≤ i)
    (hik' : i ≤ k') : v ∈ A.awake i := by
  have h1 := (E.tick_active k v a₀ hk).2.1
  have h2 := (E.tick_active k' v b₀ hk').2.2
  have h3 := htime hki
  have h4 := htime hik'
  have h5 := htime (Nat.le_succ i)
  exact Activity.mem_awakeThroughout.1 hv i (by linarith) (by linarith)

/-- A validator counted active throughout `[a, b]` is active after every step from its tick to the
clock value `a₀` to its tick to the clock value `b₀`, when `[a₀ − ΔClockAhead, b₀ + ΔClockBehind]`
lies in `[a, b]`.

The variables:
- `E`: the environment's facts; `htime`: the time is monotone in the step; `v`: the validator; `a`,
  `b`: the ends of the interval; `a₀`, `b₀`: the two clock values; `k`, `k'`: the steps of its ticks
  to `a₀` and to `b₀`; `i`: the step.

Read aloud: a validator active throughout an interval is active between two of its ticks whose
windows the interval holds. -/
theorem active_of_mem_activeThroughout [Fintype V]
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    (htime : Monotone x.time) {v : V} {a b : ℝ} {a₀ b₀ k k' i : ℕ}
    (hv : v ∈ A.activeThroughout x a b) (ha : a ≤ (a₀ : ℝ) - ΔClockAhead)
    (hb : (b₀ : ℝ) + ΔClockBehind ≤ b)
    (hk : x.lbl k = Event.tick v a₀) (hk' : x.lbl k' = Event.tick v b₀) (hki : k ≤ i)
    (hik' : i ≤ k') : v ∈ A.active i := by
  have h1 := (E.tick_active k v a₀ hk).2.1
  have h2 := (E.tick_active k' v b₀ hk').2.2
  have h3 := htime hki
  have h4 := htime hik'
  have h5 := htime (Nat.le_succ i)
  exact Activity.mem_activeThroughout.1 hv i (by linarith) (by linarith)

/-- A validator counted awake throughout `[a, b]` by the two-case reader is awake after every step
whose real time is in `[a', b]`, for every `a' ≥ a` with `a + ΔClockBehind < a'`: in the second case,
every such step comes after its tick to a value `c ≤ a`, which is at a real time at most
`c + ΔClockBehind`.

The variables:
- `E`: the environment's facts; `htime`: the time is monotone in the step; `v`: the validator; `a`,
  `b`: the ends of the interval; `a'`: the later start.

Read aloud: awake throughout an interval, from the tick or not, is awake throughout the interval
from every start after the last real time of the tick to `a`. -/
theorem mem_awakeThroughout_of_mem_awakeThroughoutOrFromTick [Fintype V]
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    (htime : Monotone x.time) {v : V}
    {a : ℤ} {b : ℕ} {a' : ℝ} (haa : (a : ℝ) ≤ a') (haB : (a : ℝ) + ΔClockBehind < a')
    (hv : v ∈ A.awakeThroughoutOrFromTick x a b) :
    v ∈ A.awakeThroughout x a' b := by
  rcases Activity.mem_awakeThroughoutOrFromTick.1 hv with h | ⟨k, c, hca, hk, h⟩
  · exact Activity.mem_awakeThroughout_of_forall fun i h1 h2 => h i h1 (by linarith)
  · refine Activity.mem_awakeThroughout_of_forall fun i h1 h2 => h i ?_ h1
    have hka := (E.tick_active k v c hk).2.2
    have hca' : (c : ℝ) ≤ (a : ℝ) := by exact_mod_cast hca
    by_contra hc
    have := htime (show i + 1 ≤ k by omega)
    linarith

/-- A validator counted active throughout `[a, b]` by the two-case reader is active after every
step whose real time is in `[a', b]`, for every `a' ≥ a` with `a + ΔClockBehind < a'`: in the second
case, every such step comes after its tick to a value `c ≤ a`, which is at a real time at most
`c + ΔClockBehind`.

The variables:
- `E`: the environment's facts; `htime`: the time is monotone in the step; `v`: the validator; `a`,
  `b`: the ends of the interval; `a'`: the later start.

Read aloud: active throughout an interval, from the tick or not, is active throughout the interval
from every start after the last real time of the tick to `a`. -/
theorem mem_activeThroughout_of_mem_activeThroughoutOrFromTick [Fintype V]
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    (htime : Monotone x.time) {v : V}
    {a : ℤ} {b : ℕ} {a' : ℝ} (haa : (a : ℝ) ≤ a') (haB : (a : ℝ) + ΔClockBehind < a')
    (hv : v ∈ A.activeThroughoutOrFromTick x a b) :
    v ∈ A.activeThroughout x a' b := by
  rcases Activity.mem_activeThroughoutOrFromTick.1 hv with h | ⟨k, c, hca, hk, h⟩
  · exact Activity.mem_activeThroughout_of_forall fun i h1 h2 => h i h1 (by linarith)
  · refine Activity.mem_activeThroughout_of_forall fun i h1 h2 => h i ?_ h1
    have hka := (E.tick_active k v c hk).2.2
    have hca' : (c : ℝ) ≤ (a : ℝ) := by exact_mod_cast hca
    by_contra hc
    have := htime (show i + 1 ≤ k by omega)
    linarith

/-- A validator counted awake throughout `[a, b]` by the two-case reader is counted by it throughout
every interval `[a', b']` inside `[a, b]` with `a + ΔClockBehind < a'`.

The variables:
- `E`: the environment's facts; `htime`: the time is monotone in the step; `v`: the validator; `a`,
  `b`: the ends of the interval; `a'`, `b'`: the ends of the interval inside it.

Read aloud: awake throughout an interval, from the tick or not, is so throughout every interval
inside it that starts after the last real time of the tick to `a`. -/
theorem mem_awakeThroughoutOrFromTick_of_le [Fintype V]
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    (htime : Monotone x.time) {v : V}
    {a a' : ℤ} {b b' : ℕ} (haa : a ≤ a') (haB : (a : ℝ) + ΔClockBehind < a') (hbb : b' ≤ b)
    (hv : v ∈ A.awakeThroughoutOrFromTick x a b) :
    v ∈ A.awakeThroughoutOrFromTick x a' b' := by
  have hbb' : (b' : ℝ) ≤ b := by exact_mod_cast hbb
  exact Activity.mem_awakeThroughoutOrFromTick_of_mem_awakeThroughout
    (Activity.mem_awakeThroughout_of_le le_rfl hbb'
      (E.mem_awakeThroughout_of_mem_awakeThroughoutOrFromTick htime (by exact_mod_cast haa) haB hv))

/-- A validator's tick to `b` at step `k'` is the step `x.tickStep v b`: a validator ticks at most
once to each value.

The variables:
- `E`: the environment's facts; `v`: the validator; `b`: the value; `k'`: the step.

Read aloud: the tick to `b` is the step of the tick to `b`. -/
theorem tickStep_eq_of_lbl (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W) {v : V} {b k' : ℕ}
    (hk' : x.lbl k' = Event.tick v b) : x.tickStep v b = k' :=
  E.tick_unique _ _ v b (x.lbl_tickStep ⟨k', hk'⟩) hk'

/-- A validator counted by `A.awakeThroughoutToTick x a b` and outside the adversary set after every
step whose real time is at most `b + ΔClockBehind` is counted by `A.activeThroughoutToTick x a b`: its
tick to `b` is at a step whose real time is at most `b + ΔClockBehind`, and corruption is permanent.

The variables:
- `E`: the environment's facts; `v`: the validator; `a`, `b`: the window's first and last times.

Read aloud: awake up to the tick and honest through the last real time of that tick is active up to
the tick. -/
theorem mem_activeThroughoutToTick_of_mem_awakeThroughoutToTick [Fintype V]
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W) {v : V} {a : ℤ} {b : ℕ}
    (hv : v ∈ A.awakeThroughoutToTick x a b) (hh : A.HonestThroughTime x (b + ΔClockBehind) v) :
    v ∈ A.activeThroughoutToTick x a b := by
  obtain ⟨k', hk', h⟩ := Activity.mem_awakeThroughoutToTick.1 hv
  have hk'b := (E.tick_active k' v b hk').2.2
  have hhon : ∀ i : ℕ, i ≤ k' → v ∉ A.corrupted i := fun i hi hc =>
    hh k' hk'b (E.corrupted_mono i k' hi hc)
  refine Activity.mem_activeThroughoutToTick.2 ⟨k', hk', ?_⟩
  rcases h with h | ⟨k, hkk, c, hca, hk, h⟩
  · exact Or.inl fun i h1 => Activity.mem_active.2 ⟨h i h1, hhon i h1⟩
  · exact Or.inr ⟨k, hkk, c, hca, hk, fun i h1 h2 => Activity.mem_active.2 ⟨h i h1 h2, hhon i h2⟩⟩

/-- A validator counted by `A.awakeThroughoutToTick x a b` is counted by
`A.activeThroughoutToTick x a b`: a tick is by a validator active in the configuration it starts
from, so the validator is outside the adversary set at its tick to `b`, and corruption is permanent,
so it is outside it after every earlier step.

The variables:
- `E`: the environment's facts; `v`: the validator; `a`, `b`: the window's first and last times.

Read aloud: awake up to the tick is active up to the tick. -/
theorem mem_activeThroughoutToTick_of_awakeThroughoutToTick [Fintype V]
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W) {v : V} {a : ℤ} {b : ℕ}
    (hv : v ∈ A.awakeThroughoutToTick x a b) : v ∈ A.activeThroughoutToTick x a b := by
  obtain ⟨k', hk', h⟩ := Activity.mem_awakeThroughoutToTick.1 hv
  have hhon : ∀ i : ℕ, i ≤ k' → v ∉ A.corrupted i := fun i hi hc =>
    Activity.not_mem_corrupted_of_mem_active (E.tick_active k' v b hk').1
      (E.corrupted_mono i k' hi hc)
  refine Activity.mem_activeThroughoutToTick.2 ⟨k', hk', ?_⟩
  rcases h with h | ⟨k, hkk, c, hca, hk, h⟩
  · exact Or.inl fun i h1 => Activity.mem_active.2 ⟨h i h1, hhon i h1⟩
  · exact Or.inr ⟨k, hkk, c, hca, hk, fun i h1 h2 => Activity.mem_active.2 ⟨h i h1 h2, hhon i h2⟩⟩

/-- A validator counted by `A.awakeThroughoutToTick x a b` is awake after every step whose real time
is greater than `a + ΔClockBehind`, up to its tick to `b`: in the first case it is awake after every
step up to that tick; in the second, such a step comes after its tick to a value `c ≤ a`, which is at a
real time at most `c + ΔClockBehind`.

The variables:
- `E`: the environment's facts; `htime`: the time is monotone in the step; `v`: the validator; `a`,
  `b`: the window's first and last times; `i`: the step.

Read aloud: awake up to the tick is awake at every step after the window's first time and after the
last real time of the tick to it, up to the tick. -/
theorem awake_of_mem_awakeThroughoutToTick [Fintype V]
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    (htime : Monotone x.time) {v : V}
    {a : ℤ} {b i : ℕ} (hv : v ∈ A.awakeThroughoutToTick x a b)
    (haBi : (a : ℝ) + ΔClockBehind < x.time i)
    (hik : i ≤ x.tickStep v b) : v ∈ A.awake i := by
  obtain ⟨k', hk', h | ⟨k, -, c, hca, hk, h⟩⟩ := Activity.mem_awakeThroughoutToTick.1 hv
  · rw [E.tickStep_eq_of_lbl hk'] at hik
    exact h i hik
  · rw [E.tickStep_eq_of_lbl hk'] at hik
    refine h i ?_ hik
    have hka := (E.tick_active k v c hk).2.2
    have hca' : (c : ℝ) ≤ (a : ℝ) := by exact_mod_cast hca
    by_contra hc
    have := htime (le_of_lt (not_le.mp hc))
    linarith

/-- A validator counted by `A.activeThroughoutToTick x a b` is active after every step whose real time
is greater than `a + ΔClockBehind`, up to its tick to `b`: in the first case it is active after every
step up to that tick; in the second, such a step comes after its tick to a value `c ≤ a`, which is at a
real time at most `c + ΔClockBehind`.

The variables:
- `E`: the environment's facts; `htime`: the time is monotone in the step; `v`: the validator; `a`,
  `b`: the window's first and last times; `i`: the step.

Read aloud: active up to the tick is active at every step after the window's first time and after
the last real time of the tick to it, up to the tick. -/
theorem active_of_mem_activeThroughoutToTick [Fintype V]
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    (htime : Monotone x.time) {v : V}
    {a : ℤ} {b i : ℕ} (hv : v ∈ A.activeThroughoutToTick x a b)
    (haBi : (a : ℝ) + ΔClockBehind < x.time i)
    (hik : i ≤ x.tickStep v b) : v ∈ A.active i := by
  obtain ⟨k', hk', h | ⟨k, -, c, hca, hk, h⟩⟩ := Activity.mem_activeThroughoutToTick.1 hv
  · rw [E.tickStep_eq_of_lbl hk'] at hik
    exact h i hik
  · rw [E.tickStep_eq_of_lbl hk'] at hik
    refine h i ?_ hik
    have hka := (E.tick_active k v c hk).2.2
    have hca' : (c : ℝ) ≤ (a : ℝ) := by exact_mod_cast hca
    by_contra hc
    have := htime (le_of_lt (not_le.mp hc))
    linarith

/-- The promises with the deadline `deadline'` follow from those with `deadline` when the target
deadline is defined only where the source one is, and is at least it.

The variables:
- `E`: the environment's facts; `deadline'`: the target deadline; `hd`: the target deadline, where
  defined, is at least the source one, which is defined there too.

Read aloud: a promise by earlier deadlines gives every promise by later ones. -/
theorem of_le (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    {deadline' : SignedMsg V Msg → ℝ → Option ℝ}
    (hd : ∀ sm a d', deadline' sm a = some d' → ∃ d₀, deadline sm a = some d₀ ∧ d₀ ≤ d') :
    EnvFactsBy A x ΔClockAhead ΔClockBehind deadline' release ΔRedeliver ok W where
  time_div := E.time_div
  corrupted_mono := E.corrupted_mono
  corrupted_keep := E.corrupted_keep
  ahead_nonneg := E.ahead_nonneg
  behind_nonneg := E.behind_nonneg
  tick_of_active := E.tick_of_active
  tick_active := E.tick_active
  tick_unique := E.tick_unique
  restart_crashed := E.restart_crashed
  restart_time := E.restart_time
  clock_mono := E.clock_mono
  restart_of_awake := E.restart_of_awake
  deliver_active := E.deliver_active
  other_sent := E.other_sent
  delivered := fun i k v sm t d' hs hok hk hik hwin hd' hdk hrel => by
    obtain ⟨d₀, h₀, hle⟩ := hd sm _ d' hd'
    exact E.delivered i k v sm t d₀ hs hok hk hik hwin h₀ (le_trans hle hdk) hrel

/-- The promises with the deadline `deadline'` follow from those with `deadline` when the target
deadline, where defined, is the source one.

The variables:
- `E`: the environment's facts; `deadline'`: the target deadline; `hd`: the target deadline, where
  defined, is the source one.

Read aloud: a promise restricted to fewer messages is still kept. -/
theorem restrict (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    {deadline' : SignedMsg V Msg → ℝ → Option ℝ}
    (hd : ∀ sm a d', deadline' sm a = some d' → deadline sm a = some d') :
    EnvFactsBy A x ΔClockAhead ΔClockBehind deadline' release ΔRedeliver ok W :=
  E.of_le fun sm a d' h => ⟨d', hd sm a d' h, le_rfl⟩

/-- Every instance promises the facts other than delivery, which is what the no-delivery instance
asks.

The variables:
- `E`: the environment's facts.

Read aloud: whatever delivery an environment promises, it keeps every other promise. -/
theorem noDelivery (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W) : EnvFactsNoDelivery A x ΔClockAhead ΔClockBehind W where
  time_div := E.time_div
  corrupted_mono := E.corrupted_mono
  corrupted_keep := E.corrupted_keep
  ahead_nonneg := E.ahead_nonneg
  behind_nonneg := E.behind_nonneg
  tick_of_active := E.tick_of_active
  tick_active := E.tick_active
  tick_unique := E.tick_unique
  restart_crashed := E.restart_crashed
  restart_time := E.restart_time
  clock_mono := E.clock_mono
  restart_of_awake := E.restart_of_awake
  deliver_active := E.deliver_active
  other_sent := E.other_sent
  delivered := fun _ _ _ _ _ _ _ _ _ _ _ h _ _ => by cases h

/-- The no-delivery instance, read for any class of messages: no deadline is defined, so the
delivery promise says nothing, whatever the class.

The variables:
- `E`: the environment's promises with no delivery; `ok'`: the class of messages.

Read aloud: an environment that promises no delivery promises none for any class. -/
theorem withClass (E : EnvFactsNoDelivery A x ΔClockAhead ΔClockBehind W) (ok' : (m : Msg) → Prop) :
    EnvFactsBy A x ΔClockAhead ΔClockBehind (fun _ _ => none) (fun _ => none) 0 ok' W where
  time_div := E.time_div
  corrupted_mono := E.corrupted_mono
  corrupted_keep := E.corrupted_keep
  ahead_nonneg := E.ahead_nonneg
  behind_nonneg := E.behind_nonneg
  tick_of_active := E.tick_of_active
  tick_active := E.tick_active
  tick_unique := E.tick_unique
  restart_crashed := E.restart_crashed
  restart_time := E.restart_time
  clock_mono := E.clock_mono
  restart_of_awake := E.restart_of_awake
  deliver_active := E.deliver_active
  other_sent := E.other_sent
  delivered := fun _ _ _ _ _ _ _ _ _ _ _ h _ _ => by cases h

end EnvFactsBy

namespace CatchUpAfterRestartBy

variable {V Msg N : Type} [DecidableEq V] [DecidableEq Msg] {A : Activity V} {x : Trace V Msg N}
  {ok : (m : Msg) → Prop} {release : (m : Msg) → Option ℕ} {ΔRedeliver : ℕ}

/-- The catch-up promise read at a tick after the restart: a validator `v` restarted at the step `k`,
after an honest send of the class `ok` at the step `i < k`, whose catch-up deadline is `c`, that ticks
at a step `k' > k` to a clock value `c' ≥ c` and is active after every step `j` with `k < j ≤ k'`, is
delivered the message at a step `j` with `k < j < k'`, under the re-delivery premise at `k'`, with the
admission clause at `c'` and no memory-losing restart between `j` and `k'`.

The variables:
- `C`: the catch-up promise by `catchUp`; `i`, `k`, `v`, `sm`, `t`, `keep`: the send, the restart
  and its validator, message, clock value and kind; `c`: the catch-up deadline; `k'`, `c'`: the
  step of the tick and its clock value; `hrel`: the re-delivery premise at `k'`.

Read aloud: a restarted validator that stays up to any of its ticks, after the restart, at a clock
value at least its catch-up deadline is delivered the message before that tick. -/
theorem apply_tick {catchUp : SignedMsg V Msg → ℝ → ℝ → Option ℝ}
    (C : CatchUpAfterRestartBy A x catchUp release ΔRedeliver ok)
    {i k : ℕ} {v : V} {sm : SignedMsg V Msg} {t : ℕ} {keep : Bool} {c : ℝ} {k' c' : ℕ}
    (hs : x.HonestSendAt A i sm) (hok : ok sm.msg) (hk : x.lbl k = Event.restart v t keep)
    (hlt : i < k) (hc : catchUp sm (x.time (i + 1)) (x.time k) = some c)
    (hkk' : k < k') (hk' : x.lbl k' = Event.tick v c') (hcc' : c ≤ (c' : ℝ))
    (hwin : ∀ j : ℕ, k < j → j ≤ k' → v ∈ A.active j)
    (hrel : ∀ (r j₀ k₁ t₁ : ℕ), release sm.msg = some r →
      k < j₀ → x.lbl j₀ = Event.deliver v sm → ¬ x.ReactedAtLeast j₀ v r →
      j₀ < k₁ → k₁ ≤ k' → x.lbl k₁ = Event.tick v t₁ → r ≤ t₁ →
      (∀ (l t' : ℕ), j₀ < l → l < k₁ → x.lbl l = Event.tick v t' → t' < r) →
      x.time (k₁ + 1) + ΔRedeliver ≤ x.time k') :
    ∃ j : ℕ, k < j ∧ j < k' ∧ x.lbl j = Event.deliver v sm ∧
      (∀ r : ℕ, release sm.msg = some r → r ≤ c' → x.ReactedAtLeast j v r) ∧
      ∀ (l t' : ℕ), j < l → l < k' → x.lbl l ≠ Event.restart v t' false :=
  C i k v sm t keep c k' c' hs hok hk hlt hc hkk' hk' hcc' hwin hrel

set_option linter.unusedVariables false in
/-- A catch-up promise by the deadlines `catchUp` gives the one by `catchUp'` when `catchUp'`, where
defined, is at least `catchUp`, which is defined there too.

The variables:
- `E`: the environment's facts, and `htime`: the time is monotone in the step (neither is read: a
  tick at a clock value at least the later deadline is a tick at a clock value at least the earlier
  one); `catchUp`, `catchUp'`: the two deadlines; `hc`: the target deadline, where defined, is at
  least the source one; `C`: the catch-up promise by `catchUp`.

Read aloud: a catch-up by earlier deadlines gives every catch-up by later ones. -/
theorem of_le {deadline : SignedMsg V Msg → ℝ → Option ℝ} {releaseE : (m : Msg) → Option ℕ}
    {ΔRedeliverE : ℕ} {okE : (m : Msg) → Prop} {B : Type} {ΔClockAhead ΔClockBehind : ℝ}
    {W : ViewVocab V B Msg} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline releaseE ΔRedeliverE okE W)
    (htime : Monotone x.time)
    {catchUp catchUp' : SignedMsg V Msg → ℝ → ℝ → Option ℝ}
    (hc : ∀ sm a t c', catchUp' sm a t = some c' → ∃ c₀, catchUp sm a t = some c₀ ∧ c₀ ≤ c')
    (C : CatchUpAfterRestartBy A x catchUp release ΔRedeliver ok) :
    CatchUpAfterRestartBy A x catchUp' release ΔRedeliver ok := by
  intro i k v sm t keep c' k' c'' hs hok hk hlt hc' hkk' hk' hle' hwin hrel
  obtain ⟨c₀, h₀, hle⟩ := hc sm _ _ c' hc'
  exact C.apply_tick hs hok hk hlt h₀ hkk' hk' (le_trans hle hle') hwin hrel

/-- A catch-up promise by the deadlines `catchUp` gives the one by `catchUp'` when `catchUp'`, where
defined, is `catchUp`.

The variables:
- `catchUp`, `catchUp'`: the two deadlines; `hc`: the target deadline, where defined, is the source
  one; `C`: the catch-up promise by `catchUp`.

Read aloud: a catch-up promise restricted to fewer messages or restarts is kept. -/
theorem restrict {catchUp catchUp' : SignedMsg V Msg → ℝ → ℝ → Option ℝ}
    (hc : ∀ sm a t c, catchUp' sm a t = some c → catchUp sm a t = some c)
    (C : CatchUpAfterRestartBy A x catchUp release ΔRedeliver ok) :
    CatchUpAfterRestartBy A x catchUp' release ΔRedeliver ok :=
  fun i k v sm t keep c k' c' hs hok hk hlt hc' hkk' hk' hcc' hwin hrel =>
    C i k v sm t keep c k' c' hs hok hk hlt (hc sm _ _ c hc') hkk' hk' hcc' hwin hrel

end CatchUpAfterRestartBy

namespace EnvFactsSync

variable {V Msg N : Type} [DecidableEq V] [DecidableEq Msg] {A : Activity V} {x : Trace V Msg N}
  {ΔClockAhead ΔClockBehind : ℝ} {Δ Δw ΔRedeliver GST : ℕ} {release : (m : Msg) → Option ℕ} {ok : (m : Msg) → Prop} {B : Type}
  {W : ViewVocab V B Msg}

/-- A catch-up within `Δw` gives a catch-up within every `Δw' ≥ Δw`.

The variables:
- `E`: the environment's facts; `htime`: the time is monotone in the step; `Δw'`: the larger
  catch-up delay; `h`: `Δw ≤ Δw'`.

Read aloud: a faster catch-up gives a slower one. -/
theorem of_le_Δw (E : EnvFactsSync A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver GST release ok W) (htime : Monotone x.time) {Δw' : ℕ}
    (h : Δw ≤ Δw') : EnvFactsSync A x ΔClockAhead ΔClockBehind Δ Δw' ΔRedeliver GST release ok W where
  toEnvFactsBy := E.toEnvFactsBy
  caught_up := E.caught_up.of_le E.toEnvFactsBy htime fun _ a t c' hc' =>
    ⟨max (max a GST + Δ) (max t GST + Δw), rfl, by
      have hc'' : max (max a GST + Δ) (max t GST + Δw') = c' := Option.some.inj hc'
      rw [← hc'']
      have h' : (Δw : ℝ) ≤ Δw' := by exact_mod_cast h
      exact max_le_max le_rfl (by linarith)⟩

/-- The synchronous promises give the synchronous delivery promise alone.

The variables:
- `E`: the environment's facts.

Read aloud: the synchronous network with a catch-up keeps its delivery promise without it. -/
theorem delivery (E : EnvFactsSync A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver GST release ok W) : EnvFactsDelivery A x ΔClockAhead ΔClockBehind Δ ΔRedeliver GST release ok W :=
  E.toEnvFactsBy

end EnvFactsSync

/-! ## The sync fact -/

section Sync

variable {V Msg N : Type} [DecidableEq V] [DecidableEq Msg]

/-- `SyncedWithinBy A x serves ok release ΔRedeliver sync ΔHolderOnline`: for every real time `t`, with `k` the last
step before `t` (`x.time k < t ≤ x.time (k + 1)`), every validator `u` active in the configuration after
`k` (its activity and its state read in that one configuration, the last before `t`) and active after
every step whose real time is in `[t, ⌈t⌉₊ + ΔHolderOnline]`, every object `o` of the class `ok` that
`u` serves, in that state and at its own clock value there, to a peer that asks, and every validator
`w` that ticks, at a step `k'`, to a clock value `d'` at least the sync deadline `d = sync w ⟨u, o⟩ ⌈t⌉₊`
and is active after every step from the first one whose time is `t` up to `k'`: either `w` itself serves `o` from its last state
before `t` (its state after the same step `k`, at its own clock value there), or `w` is delivered
`u`'s signed message `⟨u, o⟩` at a step `j` before `k'`, that delivery comes at or after some step
`k''` at a time less than `t` after which `u` already serves `o` at its clock value then, and `w` is
active after every step from `j` up to `k'`. `none` is "nothing promised".

The read: the holder's state and activity, and the receiver's
start, are read at the real time `t`; the end of the holder's window and the argument of the deadline are the clock
value `⌈t⌉₊`, the least natural number at least `t`, which is the granularity at which `sync` and the protocol's own
deadlines are written. At a natural `t` the clock value is `t` itself (`Nat.ceil_natCast`).

The receiver's window ends at its own tick `k'`, to any clock value `d'` with `d ≤ d'`: the promise
holds before every such tick; nothing is asked of the steps after that tick, and nothing
is promised about them.

The receiver's admission, as in the delivery promise
`delivered`: provided that, after every delivery of `⟨u, o⟩` to `w`, at any real time, that found `w`
not yet reacted to the release clock value `r = release o` (not yet ticked to, or restarted at, a clock
value at least `r`), `w`'s first tick after it at a clock value at least `r` leaves `ΔRedeliver` before
the time of `k'`, the promised delivery found `w` already reacted to `r` whenever `r ≤ d'`.

The variables:
- `A`: the activity; `x`: the trace; `serves n tClock o`: in the node state `n` whose clock reads the
  clock value `tClock`, the holder sends `o` to a peer that asks; `ok`: the class of objects;
  `release o`: the clock value from which the receiver admits `o` (`none`: from any); `ΔRedeliver`: the
  delay of a re-delivery after the receiver's first tick at a clock value at least it;
  `sync w sm c`: the sync deadline for the receiver `w` of the signed message `sm` served at the clock value `c`;
  `ΔHolderOnline`: how long after the clock value `⌈t⌉₊` the holder stays active.

Read aloud: take a real time `t`, the last step `k` before `t`, a holder `u` active at `k`, serving `o`
there at its own clock value and active at every step whose real time lies in `[t, ⌈t⌉₊ + ΔHolderOnline]`,
and an `o` of the class `ok` whose sync deadline for `w`, computed at the clock value `⌈t⌉₊`, is `d`; then for every step `k'` at which `w`
ticks to a clock value `d'` with `d ≤ d'`, if `w` is active at every step whose real time is at least
`t` and whose index is at most `k'`, either `w` served `o` at step `k` at its own clock value, or there
are steps `k'' ≤ j` with `k''` before `t` and `u` serving `o` at `k''`, `u`'s message carrying `o`
delivered to `w` at `j`, `j` before `k'`, and `w` active at every step from `j` to `k'`; and, when a
re-delivery after `w`'s clock reaches `o`'s release clock value would come before `k'`, the delivery at
`j` found `w`'s clock already there. -/
def SyncedWithinBy (A : Activity V) (x : Trace V Msg N) (serves : N → ℕ → Msg → Prop)
    (ok : Msg → Prop) (release : Msg → Option ℕ) (ΔRedeliver : ℕ)
    (sync : V → SignedMsg V Msg → ℕ → Option ℕ) (ΔHolderOnline : ℝ) : Prop :=
  ∀ (t : ℝ) (k : ℕ) (u w : V) (o : Msg) (d d' k' : ℕ),
    x.time k < t → t ≤ x.time (k + 1) → u ∈ A.active k →
    serves (x.st k u) (x.clockValue k u) o → ok o →
    (∀ i : ℕ, t ≤ x.time i → x.time i ≤ (⌈t⌉₊ : ℝ) + ΔHolderOnline → u ∈ A.active i) →
    sync w ⟨u, o⟩ ⌈t⌉₊ = some d →
    x.lbl k' = Event.tick w d' → d ≤ d' → (∀ i : ℕ, t ≤ x.time i → i ≤ k' → w ∈ A.active i) →
    -- after any delivery `j₀` of `⟨u, o⟩` to `w` that found `w` not yet reacted to `r = release o`,
    -- `ΔRedeliver` after `w`'s first tick `k₁` at a clock value at least `r` is at most the time of `k'`
    (∀ (r j₀ k₁ t₁ : ℕ), release o = some r →
      x.lbl j₀ = Event.deliver w ⟨u, o⟩ → ¬ x.ReactedAtLeast j₀ w r →
      j₀ < k₁ → k₁ ≤ k' → x.lbl k₁ = Event.tick w t₁ → r ≤ t₁ →
      (∀ (l t' : ℕ), j₀ < l → l < k₁ → x.lbl l = Event.tick w t' → t' < r) →
      x.time (k₁ + 1) + ΔRedeliver ≤ x.time k') →
    serves (x.st k w) (x.clockValue k w) o ∨
    ∃ j k'' : ℕ, k'' ≤ j ∧ x.time k'' < t ∧ serves (x.st k'' u) (x.clockValue k'' u) o ∧
      x.lbl j = Event.deliver w ⟨u, o⟩ ∧ j < k' ∧
      -- when the release clock value is at most the tick's clock value, the delivery found `w` reacted to it
      (∀ r : ℕ, release o = some r → r ≤ d' → x.ReactedAtLeast j w r) ∧
      (∀ l : ℕ, j ≤ l → l ≤ k' → w ∈ A.active l)

/-- `SyncedWithin A x serves ok release ΔRedeliver Δs GST`: `SyncedWithinBy` with the sync deadline
`max t GST + Δs` for every receiver and object, and the holder active for `Δs` after `t`.

The variables:
- `A`: the activity; `x`: the trace; `serves`: what a node state serves at a clock value; `ok`: the
  class of objects; `Δs`: the sync delay; `GST`: the time from which the network is synchronous.

Read aloud: from `GST` on, what an honest validator active for `Δs` would serve reaches, within
`Δs`, every validator active for that long, before its every tick to a clock value at least the deadline. -/
abbrev SyncedWithin (A : Activity V) (x : Trace V Msg N) (serves : N → ℕ → Msg → Prop)
    (ok : Msg → Prop) (release : Msg → Option ℕ) (ΔRedeliver : ℕ) (Δs GST : ℕ) : Prop :=
  SyncedWithinBy A x serves ok release ΔRedeliver (fun _ => syncDeadline (α := ℕ) Δs GST) Δs

namespace SyncedWithinBy

variable {A : Activity V} {x : Trace V Msg N} {ok : Msg → Prop}
  {release : Msg → Option ℕ} {ΔRedeliver : ℕ}
  {sync : V → SignedMsg V Msg → ℕ → Option ℕ} {ΔHolderOnline : ℝ}

omit [DecidableEq Msg] in
/-- A promise about a selection gives the promise about every selection contained in it that, at
each clock value and object, is the larger one wherever it holds of some node state (as a selection
cut from the larger one by a condition on the clock value and the object is).

The variables:
- `h`: what `serves₁` serves, `serves₂` serves; `hback`: when some node state `n` serves `o` at
  `t` by `serves₁`, every node state `n'` that serves it at `t` by `serves₂` serves it by `serves₁`
  (read for the holder's state and for the receiver's); `Sy`: the sync fact about `serves₂`.

Read aloud: the sync fact is weaker the smaller the selection it is about, when the smaller
selection keeps, at a clock value and an object it serves somewhere, everything the larger one
serves. -/
theorem mono {serves₁ serves₂ : N → ℕ → Msg → Prop}
    (h : ∀ (n : N) (t : ℕ) (o : Msg), serves₁ n t o → serves₂ n t o)
    (hback : ∀ (n n' : N) (t t' : ℕ) (o : Msg), serves₁ n t o → serves₂ n' t' o → serves₁ n' t' o)
    (Sy : SyncedWithinBy A x serves₂ ok release ΔRedeliver sync ΔHolderOnline) :
    SyncedWithinBy A x serves₁ ok release ΔRedeliver sync ΔHolderOnline :=
  fun t k u w o d d' k' hkt hkt' hu ho hok hon hd hk' hdd hwin hprem => by
    rcases Sy t k u w o d d' k' hkt hkt' hu (h _ _ _ ho) hok hon hd hk' hdd hwin hprem with
      hw | ⟨j, k', hk'j, hk't, hk'o, hl, hj, hadm, hact⟩
    · exact Or.inl (hback _ _ _ _ _ ho hw)
    · exact Or.inr ⟨j, k', hk'j, hk't, hback _ _ _ _ _ ho hk'o, hl, hj, hadm, hact⟩

omit [DecidableEq Msg] in
/-- A promise with the sync deadlines `sync` gives the one with `sync'` when `sync'`, where
defined, is `sync`.

The variables:
- `h`: each target deadline, where defined, is the source one; `Sy`: the sync fact with `sync`.

Read aloud: a sync promise restricted to fewer receivers, messages or times is kept. -/
theorem restrict {serves : N → ℕ → Msg → Prop} {sync' : V → SignedMsg V Msg → ℕ → Option ℕ}
    (h : ∀ w sm t d, sync' w sm t = some d → sync w sm t = some d)
    (Sy : SyncedWithinBy A x serves ok release ΔRedeliver sync ΔHolderOnline) :
    SyncedWithinBy A x serves ok release ΔRedeliver sync' ΔHolderOnline :=
  fun t k u w o d d' k' hkt hkt' hu ho hok hon hd hk' hdd hwin hprem =>
    Sy t k u w o d d' k' hkt hkt' hu ho hok hon (h _ _ _ _ hd) hk' hdd hwin hprem

omit [DecidableEq Msg] in
/-- A promise that asks the holder to stay active for `ΔHolderOnline` gives the one that asks it for
every `ΔHolderOnline' ≥ ΔHolderOnline`.

The variables:
- `h`: `ΔHolderOnline ≤ ΔHolderOnline'`; `Sy`: the sync fact asking `ΔHolderOnline`.

Read aloud: a promise about holders that stay up less long gives the one about holders that stay up
longer. -/
theorem of_le_holderOnline {serves : N → ℕ → Msg → Prop} {ΔHolderOnline' : ℝ}
    (h : ΔHolderOnline ≤ ΔHolderOnline') (Sy : SyncedWithinBy A x serves ok release ΔRedeliver sync ΔHolderOnline) :
    SyncedWithinBy A x serves ok release ΔRedeliver sync ΔHolderOnline' :=
  fun t k u w o d d' k' hkt hkt' hu ho hok hon hd hk' hdd hwin hprem =>
    Sy t k u w o d d' k' hkt hkt' hu ho hok (fun i h1 h2 => hon i h1 (by linarith)) hd hk' hdd hwin hprem

/-- A promise with the sync deadlines `sync` gives the one with `sync'` when each target deadline,
where defined, is at least a source deadline defined there: a receiver's
tick to a clock value at least the target deadline is a tick to a clock value at least the source one.

The variables:
- `h`: each target deadline `d'`, where defined, has a source one `d` with `d ≤ d'`; `Sy`: the sync
  fact with `sync`.

Read aloud: a sync promise by earlier deadlines gives the promise by later deadlines. -/
theorem of_le {serves : N → ℕ → Msg → Prop} {sync' : V → SignedMsg V Msg → ℕ → Option ℕ}
    (h : ∀ w sm t d', sync' w sm t = some d' → ∃ d, sync w sm t = some d ∧ d ≤ d')
    (Sy : SyncedWithinBy A x serves ok release ΔRedeliver sync ΔHolderOnline) :
    SyncedWithinBy A x serves ok release ΔRedeliver sync' ΔHolderOnline :=
  fun t k u w o d' d'' k' hkt hkt' hu ho hok hon hd' hk' hdd hwin hprem => by
    obtain ⟨d, hd, hdd'⟩ := h _ _ _ _ hd'
    exact Sy t k u w o d d'' k' hkt hkt' hu ho hok hon hd hk' (le_trans hdd' hdd) hwin hprem

/-- The sync fact read with a receiver `w` active after every step whose real time is in
`[t, d + ΔClockBehind]`, `d` the sync deadline with `t ≤ d − ΔClockAhead`: `w` ticks to `d`
(`tick_of_active`), and the sync fact at that tick gives the delivery before `x.tickStep w d`, at a
step after which `w` is active up to its tick, and so after every step whose real time is at most
`d + ΔClockBehind`.

The variables:
- `E`: the environment's facts (read for the receiver's tick); `htime`: the time is monotone in the
  step; `htime0`: the time after `0` steps is not negative; `Sy`: the sync fact; `t`: the time; `k`:
  the last step before `t`; `u`: the holder; `w`: the receiver; `o`: the object; `d`: the sync
  deadline;
- `j`: the step of the delivery; `k'`: a step at or before `j`, at a time less than `t`, after which
  `u` already serves `o`.

Read aloud: a receiver active from `t` through the whole window of the sync deadline gets the promise,
with its activity after the delivery read through that window, when the re-delivery premise holds at
its tick to the deadline. -/
theorem apply_window {deadline : SignedMsg V Msg → ℝ → Option ℝ} {releaseE : Msg → Option ℕ}
    {ΔRedeliverE : ℕ} {okE : Msg → Prop} {B : Type} {ΔClockAhead ΔClockBehind : ℝ}
    {W : ViewVocab V B Msg}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline releaseE ΔRedeliverE okE W)
    (htime : Monotone x.time) (htime0 : 0 ≤ x.time 0) {serves : N → ℕ → Msg → Prop}
    (Sy : SyncedWithinBy A x serves ok release ΔRedeliver sync ΔHolderOnline) {t k : ℕ} {u w : V} {o : Msg} {d : ℕ}
    (hkt : x.time k < t) (hkt' : t ≤ x.time (k + 1)) (hu : u ∈ A.active k)
    (ho : serves (x.st k u) (x.clockValue k u) o) (hok : ok o)
    (hon : ∀ i : ℕ, (t : ℝ) ≤ x.time i → x.time i ≤ t + ΔHolderOnline → u ∈ A.active i)
    (hd : sync w ⟨u, o⟩ t = some d) (htd : t ≤ d) (htdA : (t : ℝ) ≤ d - ΔClockAhead)
    (hwin : ∀ i : ℕ, t ≤ x.time i → x.time i ≤ d + ΔClockBehind → w ∈ A.active i)
    -- the re-delivery premise of the sync fact at `w`'s tick to `d`
    (hprem : ∀ kD : ℕ, x.lbl kD = Event.tick w d → ∀ (r j₀ k₁ t₁ : ℕ), release o = some r →
      x.lbl j₀ = Event.deliver w ⟨u, o⟩ → ¬ x.ReactedAtLeast j₀ w r →
      j₀ < k₁ → k₁ ≤ kD → x.lbl k₁ = Event.tick w t₁ → r ≤ t₁ →
      (∀ (l t' : ℕ), j₀ < l → l < k₁ → x.lbl l = Event.tick w t' → t' < r) →
      x.time (k₁ + 1) + ΔRedeliver ≤ x.time kD) :
    serves (x.st k w) (x.clockValue k w) o ∨
    ∃ j k' : ℕ, k' ≤ j ∧ x.time k' < t ∧ serves (x.st k' u) (x.clockValue k' u) o ∧
      x.lbl j = Event.deliver w ⟨u, o⟩ ∧ j < x.tickStep w d ∧
      (∀ r : ℕ, release o = some r → r ≤ d → x.ReactedAtLeast j w r) ∧
      (∀ l : ℕ, j ≤ l → x.time l ≤ d + ΔClockBehind → w ∈ A.active l) := by
  have hk0 : 0 ≤ x.time k := le_trans htime0 (htime (Nat.zero_le k))
  have ht1 : 1 ≤ t := by
    have : (0 : ℝ) < t := lt_of_le_of_lt hk0 hkt
    exact_mod_cast this
  obtain ⟨kD, hkD, hkDt, hkDt'⟩ := E.tick_of_active d (by omega) w fun i hi hi' =>
    hwin i (le_trans htdA hi) hi'
  rcases Sy (t : ℝ) k u w o d d kD hkt hkt' hu ho hok (by rw [Nat.ceil_natCast]; exact hon)
      (by rw [Nat.ceil_natCast]; exact hd) hkD le_rfl (fun i h1 h2 => hwin i h1 (by
      have := htime h2
      linarith)) (hprem kD hkD) with
    hw | ⟨j, k', hk'j, hk't, hk'o, hl, hj, hadm, hact⟩
  · exact Or.inl hw
  refine Or.inr ⟨j, k', hk'j, hk't, hk'o, hl, by rw [E.tickStep_eq_of_lbl hkD]; exact hj, hadm,
    fun l hjl hld => ?_⟩
  by_cases hlk : l ≤ kD
  · exact hact l hjl hlk
  · have := htime (show kD ≤ l by omega)
    exact hwin l (by linarith) hld

end SyncedWithinBy

end Sync

end GoldilocksCorrectness.Statements.AbstractTrace
