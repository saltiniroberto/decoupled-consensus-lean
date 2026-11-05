module
public import RStsVariant2
public import RStsVariant2.Analysis.Lemmas
public import RStsVariant2.Analysis.Observable
public import GoldilocksCorrectness.Statements.AbstractTrace.TraceDefs
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A run of the bare framework read as a trace of the trace layer

`toTrace init π` reads a run `π` of any protocol `Pr` of the bare framework `RStsVariant2` as a trace
of the trace layer (`GoldilocksCorrectness.Statements.AbstractTrace.Trace`).

Each step `i` of `π` is the trace step `newIdx π i = 2 i + 1 + ⌊π.stamp (i + 1)⌋₊`, read as an event
by `eventOf`. Before it, the trace has steps of the kind `other` of its own, which move the time and
keep the run's configuration: one for each natural number `n` with
`⌊π.stamp i⌋₊ < n ≤ ⌊π.stamp (i + 1)⌋₊`, after which the trace's time is `n`, and then one after which
the trace's time is `π.stamp (i + 1)`, the real time of step `i`. So the trace's time moves only at a
step of the kind `other`, a step of `π` keeps it, and the trace has a configuration at every natural
time `n ≥ 1`: the run's configuration in force at `n` (`toTrace_time_of_inForce`). These steps are
the projection's own; they put no condition on the run.

A node state of the trace is the validator's last known memory state (`lastKnownSt`), `init v` before
its local state is first known. `activityOf π` reads the activity off the same configurations: the
validators awake are those outside the crashed set with their local state known, the validators in
the adversary set are the corrupted ones.

The page defines `traceMsg`, `eventOf`, `lastKnownSt`, `newIdx`, `origBefore`, `toTrace` and
`activityOf`, and proves the index arithmetic of the projection and what each trace step and each
configuration of the trace is, read on `π`. It reads no fact of any protocol.
-/

set_option autoImplicit false

namespace GoldilocksVariant.Final

open RStsVariant2 (Exec Execution Envelope Action Config Local Protocol)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity)
open Classical

/-! ## 1. The projection -/

/-- `traceMsg e`: the envelope `e` as a signed message of the trace layer, its recipients dropped.

The variables:
- `e`: the envelope. -/
def traceMsg {Node Msg : Type} (e : Envelope Node Msg) : Framework.StsMultisetLog.SignedMsg Node Msg :=
  ⟨e.sender, e.msg⟩

/-- `eventOf π i`: step `i` of `π` as an event of the trace layer, read from configuration `i`, the
one the step is taken from. A `tick v` is the tick to `v`'s clock reading `t` there; a
`restart v keep` is the restart at that reading; a `deliver v e` is the delivery of `e`'s signed
message when `v` is outside the crashed set, with its local state known, and outside the corrupted
set there; every other step, a tick or a restart of a validator with no clock, and a delivery to a
corrupted validator, is a step of the kind `other`.

The variables:
- `π`: the run; `i`: the step. -/
def eventOf {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (π : Exec Pr) (i : ℕ) : Event Node Msg :=
  match π.lbl i with
  | .tick v =>
    match π[i].clock v with
    | some t => .tick v t
    | none => .other
  | .restart v keep =>
    match π[i].clock v with
    | some t => .restart v t keep
    | none => .other
  | .deliver v e =>
    if v ∉ π[i].crashed ∧ (π[i][v]).isSome ∧ v ∉ π[i].adv then .deliver v (traceMsg e) else .other
  | _ => .other

/-- `lastKnownSt init π i v`: the memory state of the latest local state of `v` known in a
configuration of `π` up to the `i`-th, and `init v` when `v`'s local state is unknown in every
configuration up to the `i`-th.

The variables:
- `init v`: the node state the trace gives `v` before its local state is first known; `π`: the run;
  `i`: the configuration; `v`: the validator. -/
def lastKnownSt {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (init : (v : Node) → NodeState) (π : Exec Pr) :
    (i : ℕ) → (v : Node) → NodeState
  | 0, v => (π[0][v]).elim (init v) Local.st
  | i + 1, v => (π[i + 1][v]).elim (lastKnownSt init π i v) Local.st

/-- `newIdx π i`: the trace step of step `i` of `π`, `2 i + 1 + ⌊π.stamp (i + 1)⌋₊`. Before it come
the `i` earlier steps of `π`, one step moving the time to the real time of each of them and of step
`i` (`i + 1` steps), and one step moving the time to each natural number `n` with
`1 ≤ n ≤ ⌊π.stamp (i + 1)⌋₊` (`⌊π.stamp (i + 1)⌋₊` steps).

The variables:
- `π`: the run; `i`: the step of `π`. -/
noncomputable def newIdx {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (π : Exec Pr) (i : ℕ) : ℕ :=
  2 * i + 1 + ⌊π.stamp (i + 1)⌋₊

/-- `origBefore π j`: the number of steps of `π` among the trace's first `j` steps, so that the
trace's configuration after `j` steps is read off `π`'s configuration `origBefore π j`.

The variables:
- `π`: the run; `j`: the trace step. -/
noncomputable def origBefore {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (π : Exec Pr) (j : ℕ) : ℕ :=
  ((Finset.range j).filter fun j' => ∃ i : ℕ, newIdx π i = j').card

/-- `toTrace init π`: the run `π` as a trace. After `j` trace steps, with `o := origBefore π j` steps
of `π` among them and `c := j − 2 o`: the time is `max (π.stamp o) (min c (π.stamp (o + 1)))`, which
is `π.stamp o` right after step `o − 1` of `π`, the natural number `c` right after the step of the
kind `other` that moves the time to `c`, and `π.stamp (o + 1)` right after the one that moves it to
the real time of step `o`; every node state is the validator's last known memory state at `π`'s
configuration `o` (`lastKnownSt`); the sent log is that configuration's, the recipients dropped. The
event of trace step `newIdx π i` is `eventOf π i`; every other trace step is of the kind `other`.

The variables:
- `init v`: the node state of `v` before its local state is first known; `π`: the run. -/
noncomputable def toTrace {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : Protocol Node Msg NodeState Ev} (init : (v : Node) → NodeState) (π : Exec Pr) :
    Trace Node Msg NodeState where
  time j := max (π.stamp (origBefore π j))
    (min (((j - 2 * origBefore π j : ℕ) : ℝ)) (π.stamp (origBefore π j + 1)))
  st j v := lastKnownSt init π (origBefore π j) v
  sent j := π[origBefore π j].sent.map traceMsg
  lbl j := if h : ∃ i : ℕ, newIdx π i = j then eventOf π (Classical.choose h) else .other

/-- `activityOf π`: the activity of the run `π`, read after `j` trace steps at `π`'s configuration
`origBefore π j`: the validators awake are those outside the crashed set whose local state is known,
the validators in the adversary set are the corrupted ones.

The variables:
- `π`: the run. -/
noncomputable def activityOf {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    [Fintype Node] {Pr : Protocol Node Msg NodeState Ev} (π : Exec Pr) : Activity Node where
  awake j := Finset.univ.filter fun v =>
    v ∉ π[origBefore π j].crashed ∧ (π[origBefore π j][v]).isSome
  corrupted j := π[origBefore π j].adv

/-! ## 2. The index arithmetic -/

section Index

variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
  {Pr : Protocol Node Msg NodeState Ev} (π : Exec Pr)

/-- A later step of `π` is a later trace step.

The variables:
- `i`, `j`: two steps of `π`, `i < j`. -/
theorem newIdx_lt {i j : ℕ} (h : i < j) : newIdx π i < newIdx π j := by
  unfold newIdx
  have := Nat.floor_mono (π.stamp_mono (show i + 1 ≤ j + 1 by omega))
  omega

/-- The trace steps of the steps of `π` are in the order of the steps. -/
theorem newIdx_strictMono : StrictMono (newIdx π) := fun _ _ h => newIdx_lt π h

/-- Two steps of `π` are two trace steps. -/
theorem newIdx_injective : Function.Injective (newIdx π) := (newIdx_strictMono π).injective

/-- The trace's first `j` steps hold at most `j` steps of `π`.

The variables:
- `j`: the trace step. -/
theorem origBefore_le (j : ℕ) : origBefore π j ≤ j := by
  unfold origBefore
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- The trace's first `j + 1` steps hold one step of `π` more than its first `j` exactly when trace
step `j` is a step of `π`.

The variables:
- `j`: the trace step. -/
theorem origBefore_succ (j : ℕ) :
    origBefore π (j + 1) = origBefore π j + if (∃ i : ℕ, newIdx π i = j) then 1 else 0 := by
  unfold origBefore
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

/-- When every step of `π` before `i` is a trace step before `j`, and step `i` is not, the trace's
first `j` steps hold exactly `i` steps of `π`.

The variables:
- `i`: the step of `π`; `j`: the trace step; `hlt`: every step of `π` before `i` is a trace step
  before `j`; `hle`: step `i` is trace step `j` or a later one. -/
theorem origBefore_eq {i j : ℕ} (hlt : ∀ l : ℕ, l < i → newIdx π l < j) (hle : j ≤ newIdx π i) :
    origBefore π j = i := by
  unfold origBefore
  have hset : (Finset.range j).filter (fun j' => ∃ l : ℕ, newIdx π l = j') =
      (Finset.range i).image (newIdx π) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, l, rfl⟩
      refine ⟨l, ?_, rfl⟩
      by_contra hl
      exact absurd hk (not_lt.mpr (hle.trans ((newIdx_strictMono π).monotone (not_lt.mp hl))))
    · rintro ⟨l, hl, rfl⟩
      exact ⟨hlt l hl, l, rfl⟩
  rw [hset, Finset.card_image_of_injective _ (newIdx_injective π), Finset.card_range]

/-- The trace's first `j` steps hold the steps of `π` before `origBefore π j`, and not step
`origBefore π j`.

The variables:
- `j`: the trace step. -/
theorem origBefore_spec (j : ℕ) :
    (∀ l : ℕ, l < origBefore π j → newIdx π l < j) ∧ j ≤ newIdx π (origBefore π j) := by
  have hex : ∃ o : ℕ, j ≤ newIdx π o := ⟨j, by unfold newIdx; omega⟩
  have hlt : ∀ l : ℕ, l < Nat.find hex → newIdx π l < j := fun l hl =>
    lt_of_not_ge (Nat.find_min hex hl)
  rw [origBefore_eq π hlt (Nat.find_spec hex)]
  exact ⟨hlt, Nat.find_spec hex⟩

/-- After `j` trace steps, with `o := origBefore π j`: `2 o + ⌊π.stamp o⌋₊ ≤ j ≤ newIdx π o`.

The variables:
- `j`: the trace step. -/
theorem origBefore_bounds (j : ℕ) :
    2 * origBefore π j + ⌊π.stamp (origBefore π j)⌋₊ ≤ j ∧ j ≤ newIdx π (origBefore π j) := by
  obtain ⟨hlt, hle⟩ := origBefore_spec π j
  refine ⟨?_, hle⟩
  rcases h : origBefore π j with _ | o
  · simp [π.stamp_zero]
  · have := hlt o (by omega)
    unfold newIdx at this
    omega

/-- The trace step of step `i` of `π` comes after exactly `i` steps of `π`.

The variables:
- `i`: the step of `π`. -/
theorem origBefore_newIdx (i : ℕ) : origBefore π (newIdx π i) = i :=
  origBefore_eq π (fun _ hl => newIdx_lt π hl) le_rfl

/-- The trace step after that of step `i` of `π` comes after exactly `i + 1` steps of `π`.

The variables:
- `i`: the step of `π`. -/
theorem origBefore_newIdx_succ (i : ℕ) : origBefore π (newIdx π i + 1) = i + 1 := by
  rw [origBefore_succ, origBefore_newIdx, if_pos ⟨i, rfl⟩]

/-- A trace step that is not a step of `π` keeps the number of steps of `π` before it.

The variables:
- `j`: the trace step; `h`: it is not a step of `π`. -/
theorem origBefore_succ_of_not {j : ℕ} (h : ¬ ∃ i : ℕ, newIdx π i = j) :
    origBefore π (j + 1) = origBefore π j := by
  rw [origBefore_succ, if_neg h, Nat.add_zero]

/-- No step of `π` comes before the trace's first step. -/
theorem origBefore_zero : origBefore π 0 = 0 := by
  unfold origBefore; simp

/-- `origBefore π` never decreases. -/
theorem origBefore_mono : Monotone (origBefore π) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [origBefore_succ]
  split_ifs <;> omega

/-- The trace step `2 k + ⌊π.stamp k⌋₊`, at which the trace enters `π`'s configuration `k`, comes
after exactly `k` steps of `π`.

The variables:
- `k`: the configuration of `π`. -/
theorem origBefore_entry (k : ℕ) : origBefore π (2 * k + ⌊π.stamp k⌋₊) = k := by
  refine origBefore_eq π (fun l hl => ?_) ?_
  · have hf := Nat.floor_mono (π.stamp_mono (show l + 1 ≤ k by omega))
    unfold newIdx
    omega
  · have hf := Nat.floor_mono (π.mono k)
    unfold newIdx
    omega

end Index

/-! ## 3. The trace steps, read on the run -/

section Steps

variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
  {Pr : Protocol Node Msg NodeState Ev} (init : (v : Node) → NodeState) (π : Exec Pr)

/-- The trace's time after `j` steps, read on `π`.

The variables:
- `j`: the trace step. -/
theorem toTrace_time (j : ℕ) : (toTrace init π).time j = max (π.stamp (origBefore π j))
    (min (((j - 2 * origBefore π j : ℕ) : ℝ)) (π.stamp (origBefore π j + 1))) := rfl

/-- The node states after `j` trace steps are the last known memory states at `π`'s configuration
`origBefore π j`.

The variables:
- `j`: the trace step; `v`: the validator. -/
theorem toTrace_st (j : ℕ) (v : Node) :
    (toTrace init π).st j v = lastKnownSt init π (origBefore π j) v := rfl

/-- The sent log after `j` trace steps is that of `π`'s configuration `origBefore π j`, the
recipients dropped.

The variables:
- `j`: the trace step. -/
theorem toTrace_sent (j : ℕ) : (toTrace init π).sent j = π[origBefore π j].sent.map traceMsg := rfl

/-- The trace step of step `i` of `π` is `eventOf π i`.

The variables:
- `i`: the step of `π`. -/
theorem toTrace_lbl_newIdx (i : ℕ) : (toTrace init π).lbl (newIdx π i) = eventOf π i := by
  have hex : ∃ l : ℕ, newIdx π l = newIdx π i := ⟨i, rfl⟩
  show (if h : ∃ l : ℕ, newIdx π l = newIdx π i then eventOf π (Classical.choose h) else .other) = _
  rw [dif_pos hex, newIdx_injective π (Classical.choose_spec hex)]

/-- A trace step that is not a step of `π` is of the kind `other`.

The variables:
- `j`: the trace step; `h`: it is not a step of `π`. -/
theorem toTrace_lbl_of_not {j : ℕ} (h : ¬ ∃ i : ℕ, newIdx π i = j) :
    (toTrace init π).lbl j = Event.other := by
  show (if h : ∃ l : ℕ, newIdx π l = j then eventOf π (Classical.choose h) else .other) = _
  rw [dif_neg h]

/-- A trace step whose event is not of the kind `other` is the trace step `newIdx π i` of a step `i`
of `π`, whose event is `eventOf π i`.

The variables:
- `j`: the trace step. -/
theorem exists_newIdx_of_lbl_ne_other {j : ℕ} (h : (toTrace init π).lbl j ≠ Event.other) :
    ∃ i : ℕ, newIdx π i = j ∧ (toTrace init π).lbl j = eventOf π i := by
  by_cases hc : ∃ i : ℕ, newIdx π i = j
  · obtain ⟨i, rfl⟩ := hc
    exact ⟨i, rfl, toTrace_lbl_newIdx init π i⟩
  · exact absurd (toTrace_lbl_of_not init π hc) h

/-- Every trace step is the trace step of a step of `π`, or a step of the kind `other` that keeps the
run's configuration.

The variables:
- `j`: the trace step. -/
theorem newIdx_or_other (j : ℕ) :
    (∃ i : ℕ, newIdx π i = j) ∨
      ((toTrace init π).lbl j = Event.other ∧ origBefore π (j + 1) = origBefore π j) := by
  by_cases hc : ∃ i : ℕ, newIdx π i = j
  · exact Or.inl hc
  · exact Or.inr ⟨toTrace_lbl_of_not init π hc, origBefore_succ_of_not π hc⟩

/-- After the trace step of step `i` of `π`, the node states are those at configuration `i`.

The variables:
- `i`: the step of `π`; `v`: the validator. -/
theorem toTrace_st_newIdx (i : ℕ) (v : Node) :
    (toTrace init π).st (newIdx π i) v = lastKnownSt init π i v := by
  rw [toTrace_st, origBefore_newIdx]

/-- One trace step after the trace step of step `i` of `π`, the node states are those at
configuration `i + 1`.

The variables:
- `i`: the step of `π`; `v`: the validator. -/
theorem toTrace_st_newIdx_succ (i : ℕ) (v : Node) :
    (toTrace init π).st (newIdx π i + 1) v = lastKnownSt init π (i + 1) v := by
  rw [toTrace_st, origBefore_newIdx_succ]

/-- At the trace step of step `i` of `π`, the sent log is configuration `i`'s.

The variables:
- `i`: the step of `π`. -/
theorem toTrace_sent_newIdx (i : ℕ) :
    (toTrace init π).sent (newIdx π i) = π[i].sent.map traceMsg := by
  rw [toTrace_sent, origBefore_newIdx]

/-- One trace step after the trace step of step `i` of `π`, the sent log is configuration `i + 1`'s.

The variables:
- `i`: the step of `π`. -/
theorem toTrace_sent_newIdx_succ (i : ℕ) :
    (toTrace init π).sent (newIdx π i + 1) = π[i + 1].sent.map traceMsg := by
  rw [toTrace_sent, origBefore_newIdx_succ]

/-- At the trace step of step `i` of `π`, the time is the real time `π.stamp (i + 1)` of step `i`.

The variables:
- `i`: the step of `π`. -/
theorem toTrace_time_newIdx (i : ℕ) : (toTrace init π).time (newIdx π i) = π.stamp (i + 1) := by
  rw [toTrace_time, origBefore_newIdx]
  have hc : newIdx π i - 2 * i = ⌊π.stamp (i + 1)⌋₊ + 1 := by unfold newIdx; omega
  rw [hc]
  have h1 : π.stamp (i + 1) ≤ ((⌊π.stamp (i + 1)⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast
    exact (Nat.lt_floor_add_one _).le
  rw [min_eq_right h1, max_eq_right (π.mono i)]

/-- One trace step after the trace step of step `i` of `π`, the time is still `π.stamp (i + 1)`: a
step of `π` keeps the time.

The variables:
- `i`: the step of `π`. -/
theorem toTrace_time_newIdx_succ (i : ℕ) :
    (toTrace init π).time (newIdx π i + 1) = π.stamp (i + 1) := by
  rw [toTrace_time, origBefore_newIdx_succ]
  have hc : newIdx π i + 1 - 2 * (i + 1) = ⌊π.stamp (i + 1)⌋₊ := by unfold newIdx; omega
  rw [hc]
  apply max_eq_left
  exact (min_le_left _ _).trans (Nat.floor_le (π.stamp_nonneg _))

/-- At the trace step `2 k + ⌊π.stamp k⌋₊`, the time is the real time `π.stamp k` at which `π`'s
configuration `k` is entered.

The variables:
- `k`: the configuration of `π`. -/
theorem toTrace_time_entry (k : ℕ) :
    (toTrace init π).time (2 * k + ⌊π.stamp k⌋₊) = π.stamp k := by
  rw [toTrace_time, origBefore_entry, show 2 * k + ⌊π.stamp k⌋₊ - 2 * k = ⌊π.stamp k⌋₊ by omega]
  apply max_eq_left
  exact (min_le_left _ _).trans (Nat.floor_le (π.stamp_nonneg _))

/-- The trace starts at the real time `0`. -/
theorem toTrace_time_zero : (toTrace init π).time 0 = 0 := by
  rw [toTrace_time, origBefore_zero, π.stamp_zero]
  simp [π.stamp_nonneg]

/-- The time after `j` trace steps lies between the real time `π.stamp o` at which `π`'s configuration
`o := origBefore π j` is entered and the real time `π.stamp (o + 1)` at which it is left.

The variables:
- `j`: the trace step. -/
theorem toTrace_time_mem (j : ℕ) :
    π.stamp (origBefore π j) ≤ (toTrace init π).time j ∧
      (toTrace init π).time j ≤ π.stamp (origBefore π j + 1) := by
  rw [toTrace_time]
  exact ⟨le_max_left _ _, max_le (π.mono _) (min_le_right _ _)⟩

/-- No trace step moves the time back.

The variables:
- `j`: the trace step. -/
theorem toTrace_time_le_succ (j : ℕ) : (toTrace init π).time j ≤ (toTrace init π).time (j + 1) := by
  by_cases h : ∃ i : ℕ, newIdx π i = j
  · obtain ⟨i, rfl⟩ := h
    rw [toTrace_time_newIdx_succ, toTrace_time_newIdx]
  · rw [toTrace_time, toTrace_time, origBefore_succ_of_not π h]
    have := (origBefore_bounds π j).1
    apply max_le_max le_rfl
    apply min_le_min _ le_rfl
    exact Nat.cast_le.mpr (by omega)

/-- The trace's time never goes back.

The variables:
- `j`, `j'`: two trace steps, `j ≤ j'`. -/
theorem toTrace_time_mono {j j' : ℕ} (h : j ≤ j') :
    (toTrace init π).time j ≤ (toTrace init π).time j' :=
  monotone_nat_of_le_succ (toTrace_time_le_succ init π) h

/-- The step of the kind `other` that moves the time to the natural number `t ≥ 1`: with `i` the
configuration of `π` in force at `t`, the trace holds configuration `i` after `2 i + t − 1` and after
`2 i + t` steps; its time is less than `t` after the first and `t` after the second.

The variables:
- `i`: the configuration of `π` in force at `t`; `t`: the natural time. -/
theorem toTrace_time_of_inForce {i t : ℕ} (ht : 1 ≤ t) (hi : π.InForce i (t : ℝ)) :
    origBefore π (2 * i + t - 1) = i ∧ origBefore π (2 * i + t) = i ∧
      (toTrace init π).time (2 * i + t - 1) < t ∧ (toTrace init π).time (2 * i + t) = t := by
  have hfi : ⌊π.stamp i⌋₊ < t := (Nat.floor_lt (π.stamp_nonneg _)).2 hi.1
  have hlt : ∀ l : ℕ, l < i → newIdx π l < 2 * i + t - 1 := by
    intro l hl
    have hf := Nat.floor_mono (π.stamp_mono (show l + 1 ≤ i by omega))
    unfold newIdx
    omega
  have hge : 2 * i + t ≤ newIdx π i := by
    have hf : t ≤ ⌊π.stamp (i + 1)⌋₊ := Nat.le_floor (by exact_mod_cast hi.2)
    unfold newIdx
    omega
  have h1 : origBefore π (2 * i + t - 1) = i := origBefore_eq π hlt (by omega)
  have h2 : origBefore π (2 * i + t) = i :=
    origBefore_eq π (fun l hl => (hlt l hl).trans_le (by omega)) hge
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [toTrace_time, h1, show 2 * i + t - 1 - 2 * i = t - 1 by omega]
    have hc : (((t - 1 : ℕ)) : ℝ) < t := by
      rw [Nat.cast_sub ht]; simp
    exact max_lt hi.1 ((min_le_left _ _).trans_lt hc)
  · rw [toTrace_time, h2, show 2 * i + t - 2 * i = t by omega, min_eq_left hi.2]
    exact max_eq_right hi.1.le

end Steps

/-! ## 4. The activity, read on the run -/

section Activity

variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg] [Fintype Node]
  {Pr : Protocol Node Msg NodeState Ev} (π : Exec Pr)

/-- `v` is awake after `j` trace steps when it is outside the crashed set with its local state known
in `π`'s configuration `origBefore π j`.

The variables:
- `j`: the trace step; `v`: the validator. -/
theorem mem_awake_activityOf (j : ℕ) (v : Node) :
    v ∈ (activityOf π).awake j ↔
      v ∉ π[origBefore π j].crashed ∧ π[origBefore π j][v] ≠ none := by
  simp [activityOf, Option.isSome_iff_ne_none]

/-- The adversary set after `j` trace steps is the corrupted set of `π`'s configuration
`origBefore π j`.

The variables:
- `j`: the trace step. -/
theorem corrupted_activityOf (j : ℕ) : (activityOf π).corrupted j = π[origBefore π j].adv := rfl

/-- `v` is awake at the trace step of step `i` of `π` when it is up in configuration `i`.

The variables:
- `i`: the step of `π`; `v`: the validator. -/
theorem mem_awake_activityOf_newIdx (i : ℕ) (v : Node) :
    v ∈ (activityOf π).awake (newIdx π i) ↔ v ∉ π[i].crashed ∧ π[i][v] ≠ none := by
  rw [mem_awake_activityOf, origBefore_newIdx]

/-- `v` is awake one trace step after that of step `i` of `π` when it is up in configuration `i + 1`.

The variables:
- `i`: the step of `π`; `v`: the validator. -/
theorem mem_awake_activityOf_newIdx_succ (i : ℕ) (v : Node) :
    v ∈ (activityOf π).awake (newIdx π i + 1) ↔ v ∉ π[i + 1].crashed ∧ π[i + 1][v] ≠ none := by
  rw [mem_awake_activityOf, origBefore_newIdx_succ]

/-- The adversary set at the trace step of step `i` of `π` is the corrupted set of configuration `i`.

The variables:
- `i`: the step of `π`. -/
theorem corrupted_activityOf_newIdx (i : ℕ) :
    (activityOf π).corrupted (newIdx π i) = π[i].adv := by
  rw [corrupted_activityOf, origBefore_newIdx]

/-- The adversary set one trace step after that of step `i` of `π` is the corrupted set of
configuration `i + 1`.

The variables:
- `i`: the step of `π`. -/
theorem corrupted_activityOf_newIdx_succ (i : ℕ) :
    (activityOf π).corrupted (newIdx π i + 1) = π[i + 1].adv := by
  rw [corrupted_activityOf, origBefore_newIdx_succ]

/-- `v` is active after `j` trace steps when it is up and outside the corrupted set in `π`'s
configuration `origBefore π j`.

The variables:
- `j`: the trace step; `v`: the validator. -/
theorem mem_active_activityOf (j : ℕ) (v : Node) :
    v ∈ (activityOf π).active j ↔
      (v ∉ π[origBefore π j].crashed ∧ π[origBefore π j][v] ≠ none) ∧
        v ∉ π[origBefore π j].adv := by
  rw [Activity.active, Finset.mem_sdiff, mem_awake_activityOf, corrupted_activityOf]

end Activity

/-! ## 5. The events, read back -/

section Events

variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
  {Pr : Protocol Node Msg NodeState Ev} (π : Exec Pr)

/-- Step `i` reads as `v`'s tick to `t` exactly when it is `v`'s tick, taken while `v`'s clock reads
`t`.

The variables:
- `i`: the step; `v`: the validator; `t`: the clock reading. -/
theorem eventOf_eq_tick {i : ℕ} {v : Node} {t : ℕ} :
    eventOf π i = Event.tick v t ↔ π.lbl i = .tick v ∧ π[i].clock v = some t := by
  unfold eventOf
  split
  · rename_i w hl
    rw [hl]
    split
    · rename_i t' ht'
      constructor
      · intro h; cases h; exact ⟨rfl, ht'⟩
      · rintro ⟨h1, h2⟩; cases h1; rw [ht'] at h2; cases h2; rfl
    · rename_i ht'
      constructor
      · intro h; cases h
      · rintro ⟨h1, h2⟩; cases h1; rw [ht'] at h2; cases h2
  · rename_i w keep hl
    rw [hl]
    split <;> simp
  · rename_i w e hl
    rw [hl]
    split <;> simp
  · rename_i a h1 h2 h3
    constructor
    · intro h; cases h
    · rintro ⟨hl, -⟩; exact absurd hl (h1 v)

/-- Step `i` reads as `v`'s restart at the reading `t` keeping or losing its memory as `keep` says
exactly when it is `v`'s restart with that `keep`, taken while `v`'s clock reads `t`.

The variables:
- `i`: the step; `v`: the validator; `t`: the clock reading; `keep`: whether the memory is kept. -/
theorem eventOf_eq_restart {i : ℕ} {v : Node} {t : ℕ} {keep : Bool} :
    eventOf π i = Event.restart v t keep ↔
      π.lbl i = .restart v keep ∧ π[i].clock v = some t := by
  unfold eventOf
  split
  · rename_i w hl
    rw [hl]
    split <;> simp
  · rename_i w keep' hl
    rw [hl]
    split
    · rename_i t' ht'
      constructor
      · intro h; cases h; exact ⟨rfl, ht'⟩
      · rintro ⟨h1, h2⟩; cases h1; rw [ht'] at h2; cases h2; rfl
    · rename_i ht'
      constructor
      · intro h; cases h
      · rintro ⟨h1, h2⟩; cases h1; rw [ht'] at h2; cases h2
  · rename_i w e hl
    rw [hl]
    split <;> simp
  · rename_i a h1 h2 h3
    constructor
    · intro h; cases h
    · rintro ⟨hl, -⟩; exact absurd hl (h2 v keep)

/-- Step `i` reads as the delivery to `v` of the signed message `sm` exactly when it is the delivery
to `v` of an envelope whose signed message is `sm`, with `v` up and outside the corrupted set in
configuration `i`.

The variables:
- `i`: the step; `v`: the validator; `sm`: the signed message. -/
theorem eventOf_eq_deliver {i : ℕ} {v : Node} {sm : Framework.StsMultisetLog.SignedMsg Node Msg} :
    eventOf π i = Event.deliver v sm ↔
      ∃ e : Envelope Node Msg, π.lbl i = .deliver v e ∧ traceMsg e = sm ∧
        v ∉ π[i].crashed ∧ π[i][v] ≠ none ∧ v ∉ π[i].adv := by
  unfold eventOf
  split
  · rename_i w hl
    rw [hl]
    split <;> simp
  · rename_i w keep hl
    rw [hl]
    split <;> simp
  · rename_i w e hl
    rw [hl]
    split
    · rename_i hc
      obtain ⟨hcr, hs, hadv⟩ := hc
      constructor
      · intro h
        cases h
        exact ⟨e, rfl, rfl, hcr, Option.isSome_iff_ne_none.mp hs, hadv⟩
      · rintro ⟨e', he', hm, -, -, -⟩
        cases he'
        rw [hm]
    · rename_i hc
      constructor
      · intro h; cases h
      · rintro ⟨e', he', -, hcr, hs, hadv⟩
        cases he'
        exact absurd ⟨hcr, Option.isSome_iff_ne_none.mpr hs, hadv⟩ hc
  · rename_i a h1 h2 h3
    constructor
    · intro h; cases h
    · rintro ⟨e', hl, -⟩; exact absurd hl (h3 v e')

end Events

/-! ## 6. The last known state -/

section LastKnown

variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
  {Pr : Protocol Node Msg NodeState Ev} (init : (v : Node) → NodeState) (π : Exec Pr)

/-- Before any step, every validator's last known state is `init v`: no local state is known at the
start.

The variables:
- `v`: the validator. -/
theorem lastKnownSt_zero (v : Node) : lastKnownSt init π 0 v = init v := by
  have h0 : π[0][v] = none := π.init.1 v
  simp [lastKnownSt, h0]

/-- When `v`'s local state is known as `l` in configuration `i`, its last known state is `l.st`.

The variables:
- `i`: the configuration; `v`: the validator; `l`: its local state there. -/
theorem lastKnownSt_of_some {i : ℕ} {v : Node} {l : Local Node Msg NodeState}
    (h : π[i][v] = some l) : lastKnownSt init π i v = l.st := by
  cases i with
  | zero => simp [lastKnownSt, h]
  | succ i => simp [lastKnownSt, h]

/-- A step after which `v`'s local state is unknown keeps `v`'s last known state.

The variables:
- `i`: the step; `v`: the validator. -/
theorem lastKnownSt_succ_of_none {i : ℕ} {v : Node} (h : π[i + 1][v] = none) :
    lastKnownSt init π (i + 1) v = lastKnownSt init π i v := by
  simp [lastKnownSt, h]

end LastKnown

end GoldilocksVariant.Final
