module
public import GoldilocksVariant.Final.Projection

@[expose] public section

/-!
# The fields of `EnvFactsBy` that read no protocol fact, on the projection of a run

For a run `π` of any protocol `Pr` of the bare framework `RStsVariant2`, read as the trace
`toTrace init π` with the activity `activityOf π` (`GoldilocksVariant.Final.Projection`), each theorem
here concludes one field of `EnvFactsBy` (`GoldilocksCorrectness.Statements.AbstractTrace.TraceDefs`)
in the structure's own wording, from the step relation and, where the field needs it, the conditions
on executions it names:

- from the step relation alone: `time_div`, `corrupted_mono`, `corrupted_keep`, `restart_crashed`,
  `restart_of_awake`, `deliver_active`, `clock_mono`;
- with `TickOncePerReadingG`: `tick_unique`;
- with `ClockWithinSkew` and `ActsWithinSkewG`: `tick_active`, `restart_time`;
- with `ClockWithinSkew`, `ClockAdvancesWithin`, `TicksWithin` and `0 ≤ ΔClockAhead`,
  `0 ≤ ΔClockBehind`: `tick_of_active` (`toTrace_tick_of_active`). Its window argument is
  `toTrace_tick_of_active_of_time_mem`: the field's conclusion under the field's premise and the
  premise that some configuration of the trace has its time in the window, from the same argument
  on the run (`exists_tick_of_upAndHonest_window`). The trace's step of the kind `other` that moves
  the time to `t` has its time in the window, so the field needs no premise more.
-/

set_option autoImplicit false

namespace GoldilocksVariant.Final

open RStsVariant2 (Exec Execution Envelope Action Config Local Protocol)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity)

/-! ## 1. Steps of the trace, read on the run -/

section Steps

variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
  {Pr : Protocol Node Msg NodeState Ev} (init : (v : Node) → NodeState) (π : Exec Pr)

/-- A trace step that is `v`'s tick to `t` is the trace step `newIdx π k` of a step `k` of the run
that is `v`'s tick, taken while `v`'s clock reads `t`.

The variables:
- `j`: the trace step; `v`: the validator; `t`: the clock reading. -/
theorem exists_of_lbl_tick {j : ℕ} {v : Node} {t : ℕ}
    (h : (toTrace init π).lbl j = Event.tick v t) :
    ∃ k : ℕ, newIdx π k = j ∧ π.lbl k = .tick v ∧ π[k].clock v = some t := by
  obtain ⟨k, rfl, hk⟩ := exists_newIdx_of_lbl_ne_other init π (by rw [h]; simp)
  exact ⟨k, rfl, (eventOf_eq_tick π).1 (hk.symm.trans h)⟩

/-- A trace step that is `v`'s restart at `t` is the trace step `newIdx π k` of a step `k` of the run
that is `v`'s restart with the same `keep`, taken while `v`'s clock reads `t`.

The variables:
- `j`: the trace step; `v`: the validator; `t`: the clock reading; `keep`: whether the memory is
  kept. -/
theorem exists_of_lbl_restart {j : ℕ} {v : Node} {t : ℕ} {keep : Bool}
    (h : (toTrace init π).lbl j = Event.restart v t keep) :
    ∃ k : ℕ, newIdx π k = j ∧ π.lbl k = .restart v keep ∧ π[k].clock v = some t := by
  obtain ⟨k, rfl, hk⟩ := exists_newIdx_of_lbl_ne_other init π (by rw [h]; simp)
  exact ⟨k, rfl, (eventOf_eq_restart π).1 (hk.symm.trans h)⟩

/-- A trace step that is `v`'s tick or restart at `t` is the trace step `newIdx π k` of a step `k` of
the run taken while `v`'s clock reads `t`.

The variables:
- `j`: the trace step; `v`: the validator; `t`: the clock reading. -/
theorem exists_clock_of_tick_or_restart {j : ℕ} {v : Node} {t : ℕ}
    (h : (toTrace init π).lbl j = Event.tick v t ∨
      ∃ keep : Bool, (toTrace init π).lbl j = Event.restart v t keep) :
    ∃ k : ℕ, newIdx π k = j ∧ π[k].clock v = some t := by
  rcases h with h | ⟨keep, h⟩
  · obtain ⟨k, rfl, -, hc⟩ := exists_of_lbl_tick init π h
    exact ⟨k, rfl, hc⟩
  · obtain ⟨k, rfl, -, hc⟩ := exists_of_lbl_restart init π h
    exact ⟨k, rfl, hc⟩

/-- A clock reads `t` only after a step that set it to `t`.

Why: no clock exists at the start, and only `setClock` gives a clock a reading.

The variables:
- `k`: the configuration; `v`: the validator; `t`: the clock reading. -/
theorem exists_setClock_of_clock {k : ℕ} {v : Node} {t : ℕ} (h : π[k].clock v = some t) :
    ∃ s : ℕ, s < k ∧ π.lbl s = .setClock v t := by
  induction k with
  | zero =>
    have h0 : π[0].clock v = none := π.init.2.1 v
    rw [h0] at h; cases h
  | succ k ih =>
    by_cases hset : ∃ t' : ℕ, π.lbl k = .setClock v t'
    · obtain ⟨t', ht'⟩ := hset
      have hs := π.step_at k
      rw [ht'] at hs
      obtain ⟨-, -, hc⟩ := hs.setClock_eq
      rw [hc, RStsVariant2.setClock_clock_self] at h
      cases h
      exact ⟨k, Nat.lt_succ_self k, ht'⟩
    · have hset' : ∀ t' : ℕ, π.lbl k ≠ .setClock v t' := fun t' h' => hset ⟨t', h'⟩
      by_cases hcor : π.lbl k = .corrupt v
      · have hs := π.step_at k
        rw [hcor] at hs
        rw [hs.corrupt_eq.2.2.1] at h; cases h
      · rw [π.clock_succ hset' hcor] at h
        obtain ⟨s, hs, hl⟩ := ih h
        exact ⟨s, by omega, hl⟩

/-- A step taken while `v`'s clock reads `t` is at a real time at least `t − ΔClockAhead`, when every
clock change is within the bounds.

Why: the step `setClock v t` came before it, at a real time at least `t − ΔClockAhead`.

The variables:
- `ΔClockAhead`, `ΔClockBehind`: the clock bounds; `hSkew`: every `setClock` to a reading `t` is at
  a real time in `[t − ΔClockAhead, t + ΔClockBehind]`; `k`: the step; `v`: the validator; `t`: the
  clock reading. -/
theorem le_stamp_of_clock (ΔClockAhead ΔClockBehind : ℝ)
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π) {k : ℕ} {v : Node} {t : ℕ}
    (h : π[k].clock v = some t) : (t : ℝ) - ΔClockAhead ≤ π.stamp (k + 1) := by
  obtain ⟨s, hs, hl⟩ := exists_setClock_of_clock π h
  have h1 : (t : ℝ) - ΔClockAhead ≤ π.stamp (s + 1) := (hSkew s v t hl).1
  exact h1.trans (π.stamp_mono (by omega))

end Steps

/-! ## 2. The fields of the activity and of the events -/

section ActivityFields

variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
  {Pr : Protocol Node Msg NodeState Ev} (init : (v : Node) → NodeState) (π : Exec Pr)

/-- `time_div` on `toTrace init π`: for every natural number `t`, some step of the trace is at a real
time at least `t`.

Why: the run's real time never stops (`Execution.progress`).

The variables:
- `init`: the node states before a local state is known; `π`: the run. -/
theorem toTrace_time_div : ∀ t : ℕ, ∃ i : ℕ, (t : ℝ) ≤ (toTrace init π).time i := by
  intro t
  obtain ⟨i, hi⟩ := π.progress t
  exact ⟨newIdx π i, by rw [toTrace_time_newIdx]; exact hi.trans (π.mono i)⟩

variable [Fintype Node]

/-- `corrupted_mono` on `activityOf π`: the adversary set only grows.

The variables:
- `π`: the run. -/
theorem activityOf_corrupted_mono :
    ∀ i i' : ℕ, i ≤ i' → (activityOf π).corrupted i ⊆ (activityOf π).corrupted i' := by
  intro i i' h
  rw [corrupted_activityOf, corrupted_activityOf]
  exact π.adv_mono (origBefore_mono π h)

/-- `corrupted_keep` on `activityOf π` and `toTrace init π`: a tick, a restart or a delivery keeps the
adversary set.

Why: such a trace step is the trace step of a step of the run that is not a corruption, which keeps
the corrupted set.

The variables:
- `init`: the node states before a local state is known; `π`: the run. -/
theorem activityOf_corrupted_keep :
    ∀ i : ℕ, (toTrace init π).lbl i ≠ Event.other →
      (activityOf π).corrupted (i + 1) = (activityOf π).corrupted i := by
  intro j h
  obtain ⟨k, rfl, hk⟩ := exists_newIdx_of_lbl_ne_other init π h
  rw [corrupted_activityOf_newIdx_succ, corrupted_activityOf_newIdx]
  apply (π.step_at k).adv_eq
  intro v hv
  rw [hk] at h
  exact h (by simp [eventOf, hv])

omit [Fintype Node] in
/-- `tick_unique` on `toTrace init π`, when a node ticks at most once at each reading: two trace steps
that are `v`'s tick to `t` are the same step.

Why: they are two ticks of `v` in the run, each taken while `v`'s clock reads `t`.

The variables:
- `init`: the node states before a local state is known; `π`: the run; `hOne`: a node ticks at most
  once while its clock shows any one reading. -/
theorem toTrace_tick_unique (hOne : RStsVariant2.TickOncePerReadingG π) :
    ∀ (i j : ℕ) (v : Node) (t : ℕ), (toTrace init π).lbl i = Event.tick v t →
      (toTrace init π).lbl j = Event.tick v t → i = j := by
  intro i j v t hi hj
  obtain ⟨a, rfl, ha, hca⟩ := exists_of_lbl_tick init π hi
  obtain ⟨b, rfl, hb, hcb⟩ := exists_of_lbl_tick init π hj
  have hab : a = b := hOne a b v t ha hca hb hcb
  rw [hab]

/-- `restart_crashed` on `activityOf π` and `toTrace init π`: a restart is by a validator not awake in
the configuration it starts from and awake after it.

Why: a restart of the run is enabled only at a validator crashed or with its local state unknown,
and leaves it outside the crashed set with its local state known.

The variables:
- `init`: the node states before a local state is known; `π`: the run. -/
theorem activityOf_restart_crashed :
    ∀ (i : ℕ) (v : Node) (t : ℕ) (keep : Bool), (toTrace init π).lbl i = Event.restart v t keep →
      v ∉ (activityOf π).awake i ∧ v ∈ (activityOf π).awake (i + 1) := by
  intro j v t keep h
  obtain ⟨k, rfl, hl, -⟩ := exists_of_lbl_restart init π h
  have hs := π.step_at k
  rw [hl] at hs
  obtain ⟨-, hdown, t', -, hv', -, -, -, hcr, -, -⟩ := hs.restart_eq
  rw [mem_awake_activityOf_newIdx_succ, mem_awake_activityOf_newIdx]
  refine ⟨fun hu => ?_, ?_, ?_⟩
  · rcases hdown with hc | hn
    · exact hu.1 hc
    · exact hu.2 hn
  · rw [hcr]
    exact fun hm => (Finset.mem_erase.1 hm).1 rfl
  · rw [hv']
    exact Option.some_ne_none _

omit [Fintype Node] in
open RStsVariant2 in
/-- A validator not up (outside the crashed set with its local state known) after `i` steps and up
after `i + 1` steps took `restart v keep` at step `i`: no other step of the bare framework brings a
validator up.

The variables:
- `π`: the run; `i`: the step; `v`: the validator. -/
theorem restart_of_up (i : ℕ) (v : Node)
    (hnu : ¬ (v ∉ π[i].crashed ∧ π[i][v] ≠ none))
    (hu : (v ∉ π[i + 1].crashed ∧ π[i + 1][v] ≠ none)) :
    ∃ keep : Bool, π.lbl i = .restart v keep := by
  have h := π.step_at i
  refine h.elim (motive := fun a d d' => ¬ (v ∉ d.crashed ∧ d[v] ≠ none) →
      (v ∉ d'.crashed ∧ d'[v] ≠ none) → ∃ keep : Bool, a = .restart v keep)
    ?setClock ?tick ?deliver ?deliverAdv ?corrupt ?crash ?crashDuring ?restart ?custom
    ?adversarial hnu hu
  case setClock =>
    intro d w t _ _ hnu hu
    exact absurd ⟨by simpa [setClock_crashed] using hu.1, by simpa [setClock_getElem] using hu.2⟩ hnu
  case tick =>
    intro d w l t res _ hwc hl _ _ hnu hu
    by_cases hvw : v = w
    · subst hvw
      exact absurd ⟨hwc, by rw [hl]; exact Option.some_ne_none _⟩ hnu
    · refine absurd ⟨?_, ?_⟩ hnu
      · simpa [applyNodeStepResult_crashed] using hu.1
      · have h2 := hu.2
        rwa [applyNodeStepResult_getElem_other Pr w v res d hvw] at h2
  case deliver =>
    intro d w e l t res _ _ _ hwc hl _ _ hnu hu
    by_cases hvw : v = w
    · subst hvw
      exact absurd ⟨hwc, by rw [hl]; exact Option.some_ne_none _⟩ hnu
    · refine absurd ⟨?_, ?_⟩ hnu
      · simpa [applyNodeStepResult_crashed, receive_crashed] using hu.1
      · have h2 := hu.2
        rwa [applyNodeStepResult_getElem_other Pr w v res _ hvw, receive_getElem] at h2
  case deliverAdv =>
    intro d w e _ _ _ hnu hu
    exact absurd ⟨by simpa [receive_crashed] using hu.1, by simpa [receive_getElem] using hu.2⟩ hnu
  case corrupt =>
    intro d w _ hnu hu
    by_cases hvw : v = w
    · subst hvw
      have h2 : (Config.setNode v none d)[v] ≠ none := hu.2
      exact absurd (Config.setNode_self v none d) h2
    · refine absurd ⟨hu.1, ?_⟩ hnu
      have h2 : (Config.setNode w none d)[v] ≠ none := hu.2
      rwa [Config.setNode_other w v none d hvw] at h2
  case crash =>
    intro d w _ hnu hu
    exact absurd ⟨fun hm => hu.1 (Finset.mem_insert_of_mem hm), hu.2⟩ hnu
  case crashDuring =>
    intro d w na k l t res _ _ _ _ hnu hu
    by_cases hvw : v = w
    · subst hvw
      have hm : v ∈ (applyCrashDuring v res k (NodeAction.prepare v na d)).crashed := by
        rw [applyCrashDuring_crashed]
        exact Finset.mem_insert_self _ _
      exact absurd hm hu.1
    · refine absurd ⟨?_, ?_⟩ hnu
      · have h1 := hu.1
        rw [applyCrashDuring_crashed, NodeAction.prepare_crashed] at h1
        exact fun hm => h1 (Finset.mem_insert_of_mem hm)
      · have h2 := hu.2
        rwa [applyCrashDuring_getElem_other w v res k _ hvw, NodeAction.prepare_getElem] at h2
  case restart =>
    intro d w keep t _ _ _ hnu hu
    by_cases hvw : v = w
    · exact ⟨keep, by rw [hvw]⟩
    · refine absurd ⟨fun hm => hu.1 (Finset.mem_erase.2 ⟨hvw, hm⟩), ?_⟩ hnu
      have h2 : (Config.setNode w _ d)[v] ≠ none := hu.2
      rwa [Config.setNode_other w v _ d hvw] at h2
  case custom =>
    intro d w ev l t res _ hwc hl _ _ _ hnu hu
    by_cases hvw : v = w
    · subst hvw
      exact absurd ⟨hwc, by rw [hl]; exact Option.some_ne_none _⟩ hnu
    · refine absurd ⟨?_, ?_⟩ hnu
      · simpa [applyNodeStepResult_crashed] using hu.1
      · have h2 := hu.2
        rwa [applyNodeStepResult_getElem_other Pr w v res d hvw] at h2
  case adversarial =>
    intro d w m recipients _ hnu hu
    exact absurd hu hnu

/-- `restart_of_awake` on `activityOf π` and `toTrace init π`: a validator not awake before a trace
step and awake after it was restarted at that step.

Why: a trace step that is not the trace step of a step of the run keeps the run's configuration; a
step of the run that brings a validator up is its restart (`restart_of_up`), and a restart has a
clock, so the trace reads it as a restart.

The variables:
- `init`: the node states before a local state is known; `π`: the run. -/
theorem activityOf_restart_of_awake :
    ∀ (i : ℕ) (v : Node), v ∉ (activityOf π).awake i → v ∈ (activityOf π).awake (i + 1) →
      ∃ (t : ℕ) (keep : Bool), (toTrace init π).lbl i = Event.restart v t keep := by
  intro j v hn hu
  rcases newIdx_or_other init π j with ⟨k, rfl⟩ | ⟨-, ho⟩
  · rw [mem_awake_activityOf_newIdx] at hn
    rw [mem_awake_activityOf_newIdx_succ] at hu
    obtain ⟨keep, hl⟩ := restart_of_up π k v hn hu
    have hs := π.step_at k
    rw [hl] at hs
    obtain ⟨-, -, t, ht, -⟩ := hs.restart_eq
    exact ⟨t, keep, by rw [toTrace_lbl_newIdx]; exact (eventOf_eq_restart π).2 ⟨hl, ht⟩⟩
  · rw [mem_awake_activityOf] at hn hu
    rw [ho] at hu
    exact absurd hu hn

/-- `deliver_active` on `activityOf π` and `toTrace init π`: a delivery is to a validator active in the
configuration it starts from.

Why: the trace reads as a delivery only a delivery of the run to a validator up and outside the
corrupted set.

The variables:
- `init`: the node states before a local state is known; `π`: the run. -/
theorem activityOf_deliver_active :
    ∀ (i : ℕ) (v : Node) (sm : Framework.StsMultisetLog.SignedMsg Node Msg),
      (toTrace init π).lbl i = Event.deliver v sm → v ∈ (activityOf π).active i := by
  intro j v sm h
  obtain ⟨k, rfl, hk⟩ := exists_newIdx_of_lbl_ne_other init π (by rw [h]; simp)
  obtain ⟨e, -, -, hcr, hs, hadv⟩ := (eventOf_eq_deliver π).1 (hk.symm.trans h)
  rw [mem_active_activityOf, origBefore_newIdx]
  exact ⟨⟨hcr, hs⟩, hadv⟩

end ActivityFields

/-! ## 3. The fields of the clocks -/

section ClockFields

variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg] [Fintype Node]
  {Pr : Protocol Node Msg NodeState Ev} (init : (v : Node) → NodeState) (π : Exec Pr)

/-- `clock_mono` on `activityOf π` and `toTrace init π`: when `v` ticks or restarts at `t` at a trace
step and ticks or restarts at `t'` at a later one, `t ≤ t'`.

Why: the two are steps of the run taken while `v`'s clock reads `t` and then `t'`, and a clock never
goes back along a run (`Execution.clock_le_of_le`); the field's premise that `v` is outside the
adversary set is not needed.

The variables:
- `init`: the node states before a local state is known; `π`: the run. -/
theorem toTrace_clock_mono :
    ∀ (i j : ℕ) (v : Node) (t t' : ℕ), i < j → v ∉ (activityOf π).corrupted j →
      ((toTrace init π).lbl i = Event.tick v t ∨
        ∃ keep : Bool, (toTrace init π).lbl i = Event.restart v t keep) →
      ((toTrace init π).lbl j = Event.tick v t' ∨
        ∃ keep : Bool, (toTrace init π).lbl j = Event.restart v t' keep) → t ≤ t' := by
  intro i j v t t' hij _ hi hj
  obtain ⟨a, rfl, ha⟩ := exists_clock_of_tick_or_restart init π hi
  obtain ⟨b, rfl, hb⟩ := exists_clock_of_tick_or_restart init π hj
  exact π.clock_le_of_le ha hb ((newIdx_strictMono π).lt_iff_lt.1 hij).le

/-- `tick_active` on `activityOf π` and `toTrace init π`: a tick to `t` is by a validator active in
the configuration it starts from, at a step whose real time is in `[t − ΔClockAhead, t + ΔClockBehind]`.

Why: a tick of the run is enabled only at a validator up and honest; the step `setClock v t` came
before it, at a real time at least `t − ΔClockAhead` (`hSkew`); and a tick at the reading `t` is at a
real time at most `t + ΔClockBehind` (`hActs`).

The variables:
- `init`: the node states before a local state is known; `π`: the run; `ΔClockAhead`,
  `ΔClockBehind`: the clock bounds; `hSkew`: every `setClock` to `t` is at a real time in
  `[t − ΔClockAhead, t + ΔClockBehind]`; `hActs`: every tick and restart at the reading `t` is at a
  real time at most `t + ΔClockBehind`. -/
theorem toTrace_tick_active (ΔClockAhead ΔClockBehind : ℝ)
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π) :
    ∀ (i : ℕ) (v : Node) (t : ℕ), (toTrace init π).lbl i = Event.tick v t →
      v ∈ (activityOf π).active i ∧ (t : ℝ) - ΔClockAhead ≤ (toTrace init π).time i ∧
        (toTrace init π).time i ≤ t + ΔClockBehind := by
  intro j v t h
  obtain ⟨k, rfl, hl, hc⟩ := exists_of_lbl_tick init π h
  obtain ⟨hadv, hcr, l, -, hl', -⟩ := (π.step_at k).up_honest (Or.inl hl)
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_active_activityOf, origBefore_newIdx]
    exact ⟨⟨hcr, by rw [hl']; exact Option.some_ne_none _⟩, hadv⟩
  · rw [toTrace_time_newIdx]
    exact le_stamp_of_clock π ΔClockAhead ΔClockBehind hSkew hc
  · rw [toTrace_time_newIdx]
    exact hActs k v t (Or.inl hl) hc

omit [Fintype Node] in
/-- `restart_time` on `toTrace init π`: a restart at the clock value `t` is at a step whose real time
is in `[t − ΔClockAhead, t + ΔClockBehind]`.

Why: the step `setClock v t` came before it, at a real time at least `t − ΔClockAhead` (`hSkew`); and
a restart at the reading `t` is at a real time at most `t + ΔClockBehind` (`hActs`).

The variables:
- `init`: the node states before a local state is known; `π`: the run; `ΔClockAhead`,
  `ΔClockBehind`: the clock bounds; `hSkew`: every `setClock` to `t` is at a real time in
  `[t − ΔClockAhead, t + ΔClockBehind]`; `hActs`: every tick and restart at the reading `t` is at a
  real time at most `t + ΔClockBehind`. -/
theorem toTrace_restart_time (ΔClockAhead ΔClockBehind : ℝ)
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π) :
    ∀ (i : ℕ) (v : Node) (t : ℕ) (keep : Bool), (toTrace init π).lbl i = Event.restart v t keep →
      (t : ℝ) - ΔClockAhead ≤ (toTrace init π).time i ∧
        (toTrace init π).time i ≤ t + ΔClockBehind := by
  intro j v t keep h
  obtain ⟨k, rfl, hl, hc⟩ := exists_of_lbl_restart init π h
  rw [toTrace_time_newIdx]
  exact ⟨le_stamp_of_clock π ΔClockAhead ΔClockBehind hSkew hc, hActs k v t (Or.inr ⟨keep, hl⟩) hc⟩

end ClockFields

/-! ## 4. The window argument of `tick_of_active` -/

section TickOfActive

variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
  {Pr : Protocol Node Msg NodeState Ev} (π : Exec Pr)

/-- A validator up and honest through the window `[t − ΔClockAhead, t + ΔClockBehind]`, in a run whose
clocks keep the bounds, advance and tick and in which no crash interrupts a reaction, ticks at the
reading `t` at a step whose real time is in the window, provided some configuration in force at a
real time of the window exists.

Why: in that configuration `v`'s clock reads less than `t`, or it came to a reading at least `t` at a
step in the window, from a reading less than `t`. From a reading less than `t`, `ClockAdvancesWithin`
gives the step setting the clock to `t` (a crash or a corruption by `t + ΔClockBehind` would fall in
the window), at a real time in the window (`ClockWithinSkew`); `TicksWithin` then gives a tick at `t`
by `t + ΔClockBehind`, neither a crash, a crash during a reaction nor a corruption (each would leave
`v` crashed or corrupted in a configuration entered in the window).

The variables:
- `π`: the run; `ΔClockAhead`, `ΔClockBehind`: the clock bounds; `hSkew`: every `setClock` to `t` is
  at a real time in `[t − ΔClockAhead, t + ΔClockBehind]`; `hAdv`: a clock of a node up and honest
  comes to every greater reading unless the node crashes or is corrupted by its window's end;
  `hTicks`: a node up and honest when its clock comes to `t` ticks at `t` by `t + ΔClockBehind` unless
  it crashes or is corrupted first; `t`: the clock reading; `v`: the validator. -/
theorem exists_tick_of_upAndHonest_window (ΔClockAhead ΔClockBehind : ℝ)
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π) (t : ℕ) (v : Node)
    -- `v` is up and honest in every configuration entered at a real time in the window
    (hCfg : ∀ k : ℕ, (t : ℝ) - ΔClockAhead ≤ π.stamp k → π.stamp k ≤ t + ΔClockBehind →
      v ∉ π[k].crashed ∧ π[k][v] ≠ none ∧ v ∉ π[k].adv)
    -- `v` is up and honest in the configuration every step of the window is taken from
    (hStep : ∀ k : ℕ, (t : ℝ) - ΔClockAhead ≤ π.stamp (k + 1) →
      π.stamp (k + 1) ≤ t + ΔClockBehind → v ∉ π[k].crashed ∧ π[k][v] ≠ none ∧ v ∉ π[k].adv)
    -- some configuration, in force at a real time `r` of the window, has `v` up and honest
    (hSome : ∃ (k : ℕ) (r : ℝ), (t : ℝ) - ΔClockAhead ≤ r ∧ r ≤ t + ΔClockBehind ∧
      π.stamp k ≤ r ∧ r ≤ π.stamp (k + 1) ∧ v ∉ π[k].crashed ∧ π[k][v] ≠ none ∧ v ∉ π[k].adv) :
    ∃ k : ℕ, π.lbl k = .tick v ∧ π[k].clock v = some t ∧
      (t : ℝ) - ΔClockAhead ≤ π.stamp (k + 1) ∧ π.stamp (k + 1) ≤ t + ΔClockBehind := by
  -- a step in the window setting `v`'s clock to `t` is followed by `v`'s tick at `t` in the window
  have finish : ∀ j : ℕ, π.lbl j = .setClock v t → (t : ℝ) - ΔClockAhead ≤ π.stamp (j + 1) →
      π.stamp (j + 1) ≤ t + ΔClockBehind → ∃ k : ℕ, π.lbl k = .tick v ∧ π[k].clock v = some t ∧
        (t : ℝ) - ΔClockAhead ≤ π.stamp (k + 1) ∧ π.stamp (k + 1) ≤ t + ΔClockBehind := by
    intro j hj h1 h2
    obtain ⟨hcr, hst, hadv⟩ := hStep j h1 h2
    obtain ⟨k, hjk, hc, hle, hcase⟩ := hTicks j v t hj hcr hadv hst
    have hc' : π[k].clock v = some t := hc
    have hle' : π.stamp (k + 1) ≤ t + ΔClockBehind := hle
    have hge : (t : ℝ) - ΔClockAhead ≤ π.stamp (k + 1) := h1.trans (π.stamp_mono (by omega))
    rcases hcase with htk | hco | hcr' | ⟨a, n, hcd⟩
    · exact ⟨k, htk, hc', hge, hle'⟩
    · exfalso
      have hs := π.step_at k
      rw [show π.lbl k = .corrupt v from hco] at hs
      apply (hCfg (k + 1) hge hle').2.2
      rw [hs.corrupt_eq.2.2.2.2.2.1]
      exact Finset.mem_insert_self _ _
    · exfalso
      have hs := π.step_at k
      rw [show π.lbl k = .crash v from hcr'] at hs
      obtain ⟨-, he⟩ := hs
      have he' : π[k + 1] = { π[k] with crashed := insert v π[k].crashed } := he
      apply (hCfg (k + 1) hge hle').1
      rw [he']
      exact Finset.mem_insert_self _ _
    · exfalso
      have hs := π.step_at k
      rw [show π.lbl k = .crashDuring v a n from hcd] at hs
      obtain ⟨-, he⟩ := hs
      apply (hCfg (k + 1) hge hle').1
      rw [RStsVariant2.CrashDuringStep.crashed he]
      exact Finset.mem_insert_self _ _
  -- from a configuration `m` with `v` up and honest and its clock less than `t`, whose next step is
  -- at a real time at least `t − ΔClockAhead`
  have core : ∀ (m c₀ : ℕ), v ∉ π[m].crashed → π[m][v] ≠ none → v ∉ π[m].adv →
      π[m].clock v = some c₀ → c₀ < t → (t : ℝ) - ΔClockAhead ≤ π.stamp (m + 1) →
      ∃ k : ℕ, π.lbl k = .tick v ∧ π[k].clock v = some t ∧
        (t : ℝ) - ΔClockAhead ≤ π.stamp (k + 1) ∧ π.stamp (k + 1) ≤ t + ΔClockBehind := by
    intro m c₀ hcr hst hadv hc hlt hge
    rcases hAdv t v m c₀ hcr hst hadv hc hlt with ⟨j, hj⟩ | ⟨j, hmj, hle, hj⟩
    · obtain ⟨h1, h2⟩ := hSkew j v t hj
      exact finish j hj h1 h2
    · exfalso
      have hge' : (t : ℝ) - ΔClockAhead ≤ π.stamp j := hge.trans (π.stamp_mono (by omega))
      obtain ⟨hcr', -, hadv'⟩ := hCfg j hge' hle
      rcases hj with h | h
      · exact hcr' h
      · exact hadv' h
  obtain ⟨k₀, r, hr1, hr2, hk1, hk2, hcr₀, hst₀, hadv₀⟩ := hSome
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (π.clock_ne_none_of_getElem_ne_none k₀ v hst₀)
  by_cases hct : c < t
  · exact core k₀ c hcr₀ hst₀ hadv₀ hc hct (hr1.trans hk2)
  -- `v`'s clock came to a reading `c₁ ≥ t` at a step `s` before `k₀`, from a reading less than `t`
  classical
  have hP : ∃ n : ℕ, ∃ c' : ℕ, π[n].clock v = some c' ∧ t ≤ c' := ⟨k₀, c, hc, by omega⟩
  obtain ⟨n, ⟨c₁, hc₁, htc₁⟩, hmin⟩ : ∃ n : ℕ, (∃ c' : ℕ, π[n].clock v = some c' ∧ t ≤ c') ∧
      ∀ m : ℕ, m < n → ¬ ∃ c' : ℕ, π[m].clock v = some c' ∧ t ≤ c' :=
    ⟨Nat.find hP, Nat.find_spec hP, fun m hm => Nat.find_min hP hm⟩
  have hnk : n ≤ k₀ := by
    by_contra h
    exact hmin k₀ (by omega) ⟨c, hc, by omega⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h0 : π[0].clock v = none := π.init.2.1 v
    rw [h0] at hc₁; cases hc₁
  obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  rw [hs] at hc₁
  have hset : π.lbl s = .setClock v c₁ := by
    by_cases hset : ∃ t' : ℕ, π.lbl s = .setClock v t'
    · obtain ⟨t', ht'⟩ := hset
      have hst := π.step_at s
      rw [ht'] at hst
      obtain ⟨-, -, hcfg⟩ := hst.setClock_eq
      rw [hcfg, RStsVariant2.setClock_clock_self] at hc₁
      cases hc₁
      exact ht'
    · exfalso
      have hset' : ∀ t' : ℕ, π.lbl s ≠ .setClock v t' := fun t' h => hset ⟨t', h⟩
      by_cases hcor : π.lbl s = .corrupt v
      · have hst := π.step_at s
        rw [hcor] at hst
        rw [hst.corrupt_eq.2.2.1] at hc₁; cases hc₁
      · rw [π.clock_succ hset' hcor] at hc₁
        exact hmin s (by omega) ⟨c₁, hc₁, htc₁⟩
  have hge : (t : ℝ) - ΔClockAhead ≤ π.stamp (s + 1) := by
    have h1 : (c₁ : ℝ) - ΔClockAhead ≤ π.stamp (s + 1) := (hSkew s v c₁ hset).1
    have h2 : (t : ℝ) ≤ c₁ := by exact_mod_cast htc₁
    linarith
  have hle : π.stamp (s + 1) ≤ t + ΔClockBehind :=
    ((π.stamp_mono (show s + 1 ≤ k₀ by omega)).trans hk1).trans hr2
  obtain ⟨hcr, hst, hadv⟩ := hStep s hge hle
  obtain ⟨c₀, hc₀⟩ := Option.ne_none_iff_exists'.mp (π.clock_ne_none_of_getElem_ne_none s v hst)
  have hlt : c₀ < t := by
    by_contra h
    exact hmin s (by omega) ⟨c₀, hc₀, by omega⟩
  exact core s c₀ hcr hst hadv hc₀ hlt hge

variable [Fintype Node]

/-- The window argument of `tick_of_active` on `activityOf π` and `toTrace init π`: a validator active
at every trace step whose time is in the window `[t − ΔClockAhead, t + ΔClockBehind]` ticks to `t` at
a trace step whose time is in the window, provided some configuration of the trace has its time in
the window.

Why: the trace step `2 k + ⌊π.stamp k⌋₊` is the run's configuration `k` at the real time `π.stamp k`,
and the trace step `newIdx π k` is configuration `k` at the real time `π.stamp (k + 1)`, so the
field's premise says that `v` is up and honest in every configuration of the run entered in the
window and in the configuration every step of the window is taken from; the configuration of the
trace with its time in the window is the run's configuration `o` at a real time in
`[π.stamp o, π.stamp (o + 1)]`; `exists_tick_of_upAndHonest_window` does the rest.

The variables:
- `init`: the node states before a local state is known; `π`: the run; `ΔClockAhead`,
  `ΔClockBehind`: the clock bounds; `hSkew`, `hAdv`, `hTicks`: as in
  `exists_tick_of_upAndHonest_window`. -/
theorem toTrace_tick_of_active_of_time_mem (init : (v : Node) → NodeState)
    (ΔClockAhead ΔClockBehind : ℝ)
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π) :
    ∀ t : ℕ, ∀ v : Node,
      (∀ i : ℕ, (t : ℝ) - ΔClockAhead ≤ (toTrace init π).time i →
        (toTrace init π).time i ≤ t + ΔClockBehind → v ∈ (activityOf π).active i) →
      -- some configuration of the trace has its time in the window
      (∃ i : ℕ, (t : ℝ) - ΔClockAhead ≤ (toTrace init π).time i ∧
        (toTrace init π).time i ≤ t + ΔClockBehind) →
      ∃ i : ℕ, (toTrace init π).lbl i = Event.tick v t ∧
        (t : ℝ) - ΔClockAhead ≤ (toTrace init π).time i ∧
        (toTrace init π).time i ≤ t + ΔClockBehind := by
  intro t v hact ⟨i, hi1, hi2⟩
  have up : ∀ j : ℕ, v ∈ (activityOf π).active j →
      v ∉ π[origBefore π j].crashed ∧ π[origBefore π j][v] ≠ none ∧
        v ∉ π[origBefore π j].adv := by
    intro j h
    obtain ⟨⟨h1, h2⟩, h3⟩ := (mem_active_activityOf π j v).1 h
    exact ⟨h1, h2, h3⟩
  have hCfg : ∀ k : ℕ, (t : ℝ) - ΔClockAhead ≤ π.stamp k → π.stamp k ≤ t + ΔClockBehind →
      v ∉ π[k].crashed ∧ π[k][v] ≠ none ∧ v ∉ π[k].adv := by
    intro k h1 h2
    have h := up (2 * k + ⌊π.stamp k⌋₊)
      (hact _ (by rw [toTrace_time_entry]; exact h1) (by rw [toTrace_time_entry]; exact h2))
    rwa [origBefore_entry] at h
  have hStep : ∀ k : ℕ, (t : ℝ) - ΔClockAhead ≤ π.stamp (k + 1) →
      π.stamp (k + 1) ≤ t + ΔClockBehind → v ∉ π[k].crashed ∧ π[k][v] ≠ none ∧ v ∉ π[k].adv := by
    intro k h1 h2
    have h := up (newIdx π k)
      (hact _ (by rw [toTrace_time_newIdx]; exact h1) (by rw [toTrace_time_newIdx]; exact h2))
    rwa [origBefore_newIdx] at h
  have hSome : ∃ (k : ℕ) (r : ℝ), (t : ℝ) - ΔClockAhead ≤ r ∧ r ≤ t + ΔClockBehind ∧
      π.stamp k ≤ r ∧ r ≤ π.stamp (k + 1) ∧ v ∉ π[k].crashed ∧ π[k][v] ≠ none ∧
        v ∉ π[k].adv :=
    ⟨origBefore π i, (toTrace init π).time i, hi1, hi2, (toTrace_time_mem init π i).1,
      (toTrace_time_mem init π i).2, up i (hact i hi1 hi2)⟩
  obtain ⟨k, hl, hc, h1, h2⟩ := exists_tick_of_upAndHonest_window π ΔClockAhead ΔClockBehind hSkew
    hAdv hTicks t v hCfg hStep hSome
  refine ⟨newIdx π k, ?_, ?_, ?_⟩
  · rw [toTrace_lbl_newIdx]
    exact (eventOf_eq_tick π).2 ⟨hl, hc⟩
  · rw [toTrace_time_newIdx]; exact h1
  · rw [toTrace_time_newIdx]; exact h2

/-- `tick_of_active` on `activityOf π` and `toTrace init π`: a validator active at every trace step
whose time is in the window `[t − ΔClockAhead, t + ΔClockBehind]`, for a clock value `t ≥ 1`, ticks to
`t` at a trace step whose time is in that window.

Why: with `m` the run's configuration in force at the real time `t`, the trace step `2 m + t` is the
end of the step of the kind `other` that moves the time to `t` (`toTrace_time_of_inForce`), so its
time `t` is in the window when both bounds are not negative; the window argument
`toTrace_tick_of_active_of_time_mem` does the rest.

The variables:
- `init`: the node states before a local state is known; `π`: the run; `ΔClockAhead`,
  `ΔClockBehind`: the clock bounds, `hAhead`, `hBehind`: neither is negative; `hSkew`, `hAdv`,
  `hTicks`: as in `exists_tick_of_upAndHonest_window`. -/
theorem toTrace_tick_of_active (init : (v : Node) → NodeState) (ΔClockAhead ΔClockBehind : ℝ)
    (hAhead : 0 ≤ ΔClockAhead) (hBehind : 0 ≤ ΔClockBehind)
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π) :
    ∀ t : ℕ, 1 ≤ t → ∀ v : Node,
      (∀ i : ℕ, (t : ℝ) - ΔClockAhead ≤ (toTrace init π).time i →
        (toTrace init π).time i ≤ t + ΔClockBehind → v ∈ (activityOf π).active i) →
      ∃ i : ℕ, (toTrace init π).lbl i = Event.tick v t ∧
        (t : ℝ) - ΔClockAhead ≤ (toTrace init π).time i ∧
        (toTrace init π).time i ≤ t + ΔClockBehind := by
  intro t ht v hact
  obtain ⟨m, hm⟩ := π.exists_inForce (show (0 : ℝ) < t by exact_mod_cast ht)
  obtain ⟨-, -, -, hJt⟩ := toTrace_time_of_inForce init π ht hm
  exact toTrace_tick_of_active_of_time_mem π init ΔClockAhead ΔClockBehind hSkew hAdv hTicks t v
    hact ⟨2 * m + t, by rw [hJt]; linarith, by rw [hJt]; linarith⟩

end TickOfActive

end GoldilocksVariant.Final
