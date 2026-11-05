module
public import GoldilocksCorrectness.Statements.Executions.ExecutionDefs

@[expose] public section

/-! What the delivery lemma needs
about the order of the steps of an execution `x` of `GoldilocksCorrectness.Wiring.protocol S`
under the atomic semantics, and about the step `stepBefore x t` that `stateBefore` reads:

- `time_le_succ`, `time_succ_le`, `time_mono`, `lt_of_time_lt`: a step's time is the time of the
  step before it or one more, so times only grow along the steps;
- `time_of_lbl_tickAllAwake`, `time_succ_of_not_tickAllAwake`: the tick of every awake validator
  at `t` moves the time from `t − 1` to `t`; every other step keeps the time;
- `exists_time_eq`: every time up to a step's time is the time of some earlier step;
- `stepBefore_zero`, `stepBefore_eq_of_lbl`, `tickAllAwake_unique`, `stepBefore_spec`:
  `stepBefore x t` is the tick at `t`, the only one, for `t ≥ 1` once every time is reached;
- `time_lt_iff_le_stepBefore`, `lt_stepBefore_iff`, `stepBefore_lt_of_le_time`,
  `le_time_add_one_of_stepBefore_le`: a step is at a time before `t` exactly when it comes no
  later than `stepBefore x t`;
- `stepBefore_mono`: a later time has a later step before it;
- `lt_stepBefore_of_not_tickAllAwake`, `deliver_before_of_time`: a step at a time before `t`
  other than a tick, a delivery in particular, has its effect in `x[stepBefore x t]`;
- `rel_of_forall_step`, `rel_stateBefore_of_step`, `rel_getElem_stateBefore`,
  `rel_stateBefore_getElem`: a relation preserved by each step holds from a step to a later one,
  and from the node state before a time to the node state before a later time, so that a
  per-step monotonicity lemma about a node lifts to `stateBefore x t v` and `stateBefore x t' v`.

The steps' own times are those of the framework's `atomic_time_stepwise` and
`tickAllAwake_of_time`, read for this protocol.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

namespace GoldilocksCorrectness.Proofs.Executions

open GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg atomic_time_stepwise
  tickAllAwake_of_time)
open Goldilocks (NodeState NamedObject RootOrder)
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable {S : Setup V} {Sched : Schedule V} (x : AtomicExec (protocol S) Sched)

/-! ## Times along the steps -/

/-- A step's configuration is at the time of the configuration before it, or later.

The variables:
- `x`: the execution; `i`: the step.

Read aloud: time never goes back from one step to the next. -/
theorem time_le_succ (i : ℕ) : x[i].time ≤ x[i + 1].time := by
  rcases atomic_time_stepwise x i with h | h <;> omega

/-- A step moves the time by at most one.

The variables:
- `x`: the execution; `i`: the step.

Read aloud: the configuration after the step `i` is at the time of the one before it, or one
more. -/
theorem time_succ_le (i : ℕ) : x[i + 1].time ≤ x[i].time + 1 := by
  rcases atomic_time_stepwise x i with h | h <;> omega

/-- Times only grow along the steps.

The variables:
- `x`: the execution; `i`, `j`: two steps, `i` no later than `j`.

Read aloud: a later configuration is at the same time or later. -/
theorem time_mono {i j : ℕ} (hij : i ≤ j) : x[i].time ≤ x[j].time :=
  monotone_nat_of_le_succ (f := fun i => x[i].time) (time_le_succ x) hij

/-- A configuration at an earlier time comes at an earlier step.

The variables:
- `x`: the execution; `i`, `j`: two steps.

Read aloud: if the configuration after `i` steps is at an earlier time than the one after `j`
steps, then `i` is less than `j`. -/
theorem lt_of_time_lt {i j : ℕ} (h : x[i].time < x[j].time) : i < j := by
  by_contra hji
  exact absurd (time_mono x (Nat.le_of_not_lt hji)) (Nat.not_le.2 h)

/-- The tick of every awake validator at `t` is enabled at the time `t − 1` and moves the time to
`t`.

The variables:
- `x`: the execution; `i`: the step; `t`: the time of the tick.

Read aloud: the step that ticks every awake validator at `t` starts at `t − 1` and ends at `t`. -/
theorem time_of_lbl_tickAllAwake {i t : ℕ} (hl : x.lbl i = AtomicAction.tickAllAwake t) :
    x[i].time + 1 = t ∧ x[i + 1].time = t := by
  have hs := x.step i
  rw [hl] at hs
  obtain ⟨hen, w, tk, -, -, hc⟩ := hs
  refine ⟨hen, ?_⟩
  show (x.cfg (i + 1)).time = t
  rw [hc]
  rfl

/-- A step other than a tick keeps the time.

The variables:
- `x`: the execution; `i`: the step.

Read aloud: a delivery, a protocol event, an adversarial send or a forward happens at the time of
the configuration it starts from, and leaves the time as it was. -/
theorem time_succ_of_not_tickAllAwake {i : ℕ}
    -- the step `i` is not the tick of every awake validator at any time
    (hl : ∀ t, x.lbl i ≠ AtomicAction.tickAllAwake t) :
    x[i + 1].time = x[i].time := by
  rcases atomic_time_stepwise x i with h | h
  · exact h
  · obtain ⟨j, hj, hlj, hj1, -⟩ := tickAllAwake_of_time x (i + 1) h (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hji | rfl
    · have := time_mono x (show j + 1 ≤ i by omega)
      omega
    · exact absurd hlj (hl _)

/-- Every time up to a configuration's time is the time of a configuration at or before it: the
time starts at `0` and moves by at most one per step.

The variables:
- `x`: the execution; `i`: a step; `t`: a time no later than `x[i].time`;
- `j`: the step found.

Read aloud: the execution passes through every time on its way to `x[i].time`. -/
theorem exists_time_eq {i t : ℕ} (h : t ≤ x[i].time) : ∃ j ≤ i, x[j].time = t := by
  induction i with
  | zero =>
      have h0 : x[0].time = 0 := x.init.1
      exact ⟨0, le_rfl, by omega⟩
  | succ i ih =>
      by_cases hle : t ≤ x[i].time
      · obtain ⟨j, hj, hjt⟩ := ih hle
        exact ⟨j, by omega, hjt⟩
      · have := time_succ_le x i
        exact ⟨i + 1, le_rfl, by omega⟩

/-! ## The step before a time -/

/-- No step ticks at the time `0`, so `stepBefore x 0` is the first step.

The variables:
- `x`: the execution.

Read aloud: the configuration before the time `0` is the initial one. -/
theorem stepBefore_zero : stepBefore x 0 = 0 := by
  unfold stepBefore
  rw [dif_neg]
  rintro ⟨i, hi⟩
  have := (time_of_lbl_tickAllAwake x hi).1
  omega

open Classical in
/-- The facts `Nat.find` gives about `stepBefore x t` when some step ticks at `t`: it ticks at `t`,
and no earlier step does. -/
private theorem stepBefore_of_exists {t : ℕ} (h : ∃ i, x.lbl i = AtomicAction.tickAllAwake t) :
    x.lbl (stepBefore x t) = AtomicAction.tickAllAwake t ∧
      ∀ i, x.lbl i = AtomicAction.tickAllAwake t → stepBefore x t ≤ i := by
  unfold stepBefore
  rw [dif_pos h]
  exact ⟨Nat.find_spec h, fun i hi => Nat.find_min' h hi⟩

/-- The step that ticks every awake validator at `t` is `stepBefore x t`: there is only one.

The variables:
- `x`: the execution; `i`: the step; `t`: the time of its tick.

Read aloud: if the step `i` ticks at `t`, it is the step `stepBefore x t` reads. -/
theorem stepBefore_eq_of_lbl {i t : ℕ} (hl : x.lbl i = AtomicAction.tickAllAwake t) :
    stepBefore x t = i := by
  obtain ⟨hlb, hmin⟩ := stepBefore_of_exists x ⟨i, hl⟩
  have hle := hmin i hl
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · have h1 := (time_of_lbl_tickAllAwake x hlb).2
    have h2 := (time_of_lbl_tickAllAwake x hl).1
    have := time_mono x (show stepBefore x t + 1 ≤ i by omega)
    omega
  · exact heq

/-- Two steps that tick every awake validator at the same time `t` are the same step.

The variables:
- `x`: the execution; `i`, `j`: the two steps; `t`: the time of their tick.

Read aloud: each time has at most one tick of every awake validator. -/
theorem tickAllAwake_unique {i j t : ℕ} (hi : x.lbl i = AtomicAction.tickAllAwake t)
    (hj : x.lbl j = AtomicAction.tickAllAwake t) : i = j :=
  (stepBefore_eq_of_lbl x hi).symm.trans (stepBefore_eq_of_lbl x hj)

/-- Once every time is reached, some step ticks at each time from `1` on.

The variables:
- `x`: the execution; `t`: the time.

Read aloud: every time after `0` has its tick. -/
theorem exists_lbl_tickAllAwake (hdiv : TimeDiverges x.toTrace) {t : ℕ} (ht : 1 ≤ t) :
    ∃ i, x.lbl i = AtomicAction.tickAllAwake t := by
  obtain ⟨i, hi⟩ := hdiv t
  obtain ⟨j, -, hj⟩ := exists_time_eq x hi
  obtain ⟨k, -, hk, -⟩ := tickAllAwake_of_time x j hj (by omega)
  exact ⟨k, hk⟩

/-- What `stepBefore x t` is, for a time `t ≥ 1` of an execution that reaches every time: the
step that ticks every awake validator at `t`, which starts at the time `t − 1` and ends at `t`.

The variables:
- `x`: the execution; `t`: the time.

Read aloud: the configuration `stateBefore` reads at `t` is the last one at the time `t − 1`, the
one the tick at `t` starts from. -/
theorem stepBefore_spec (hdiv : TimeDiverges x.toTrace) {t : ℕ} (ht : 1 ≤ t) :
    x.lbl (stepBefore x t) = AtomicAction.tickAllAwake t ∧ x[stepBefore x t].time + 1 = t ∧
      x[stepBefore x t + 1].time = t := by
  have hl := (stepBefore_of_exists x (exists_lbl_tickAllAwake x hdiv ht)).1
  exact ⟨hl, time_of_lbl_tickAllAwake x hl⟩

/-- A configuration is at a time before `t ≥ 1` exactly when its step comes no later than
`stepBefore x t`.

The variables:
- `x`: the execution; `i`: the step; `t`: the time.

Read aloud: the configurations before the time `t` are those up to the one the tick at `t` starts
from. -/
theorem time_lt_iff_le_stepBefore (hdiv : TimeDiverges x.toTrace) {i t : ℕ} (ht : 1 ≤ t) :
    x[i].time < t ↔ i ≤ stepBefore x t := by
  obtain ⟨-, h1, h2⟩ := stepBefore_spec x hdiv ht
  constructor
  · intro hi
    by_contra hlt
    have := time_mono x (show stepBefore x t + 1 ≤ i by omega)
    omega
  · intro hle
    have := time_mono x hle
    omega

/-- A step comes strictly before `stepBefore x t` exactly when the configuration it produces is
at a time before `t`, so its effect is in `x[stepBefore x t]`. No condition on `t`: at `t = 0`
neither side holds.

The variables:
- `x`: the execution; `i`: the step; `t`: the time.

Read aloud: the steps whose effect `stateBefore x t` holds are those that end before the time
`t`. -/
theorem lt_stepBefore_iff (hdiv : TimeDiverges x.toTrace) {i t : ℕ} :
    i < stepBefore x t ↔ x[i + 1].time < t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [stepBefore_zero]
    omega
  · rw [time_lt_iff_le_stepBefore x hdiv ht]
    omega

/-- A configuration at the time `t ≥ 1` or later comes after `stepBefore x t`.

The variables:
- `x`: the execution; `j`: the step; `t`: the time.

Read aloud: a configuration at `t` or later is past the one the tick at `t` starts from. -/
theorem stepBefore_lt_of_le_time (hdiv : TimeDiverges x.toTrace) {j t : ℕ} (ht : 1 ≤ t)
    (hj : t ≤ x[j].time) : stepBefore x t < j := by
  by_contra hle
  have := (time_lt_iff_le_stepBefore x hdiv ht).2 (Nat.le_of_not_lt hle)
  omega

/-- A configuration at or after `stepBefore x t` is at the time `t − 1` or later.

The variables:
- `x`: the execution; `i`: the step; `t`: the time.

Read aloud: from the tick at `t` on, the time is at least `t − 1`. -/
theorem le_time_add_one_of_stepBefore_le (hdiv : TimeDiverges x.toTrace) {i t : ℕ}
    (hi : stepBefore x t ≤ i) : t ≤ x[i].time + 1 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · omega
  · have h1 := (stepBefore_spec x hdiv ht).2.1
    have := time_mono x hi
    omega

/-- A later time has a later step before it.

The variables:
- `x`: the execution; `t`, `t'`: two times, `t` no later than `t'`.

Read aloud: the configuration before `t'` comes no earlier than the configuration before `t`. -/
theorem stepBefore_mono (hdiv : TimeDiverges x.toTrace) {t t' : ℕ} (h : t ≤ t') :
    stepBefore x t ≤ stepBefore x t' := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [stepBefore_zero]
    exact Nat.zero_le _
  · have h1 := (stepBefore_spec x hdiv ht).2.1
    exact (time_lt_iff_le_stepBefore x hdiv (by omega)).1 (by omega)

/-- A step at a time before `t` that is not a tick comes strictly before `stepBefore x t`, so the
configuration it produces is at or before `x[stepBefore x t]`.

The variables:
- `x`: the execution; `i`: the step; `t`: the time.

Read aloud: a step other than a tick, taken before the time `t`, has its effect in what
`stateBefore x t` reads. -/
theorem lt_stepBefore_of_not_tickAllAwake (hdiv : TimeDiverges x.toTrace) {i t : ℕ}
    -- the step `i` is not the tick of every awake validator at any time
    (hl : ∀ t', x.lbl i ≠ AtomicAction.tickAllAwake t')
    -- the step `i` starts before `t`
    (hi : x[i].time < t) : i < stepBefore x t := by
  rw [lt_stepBefore_iff x hdiv, time_succ_of_not_tickAllAwake x hl]
  exact hi

/-- A delivery at a time before `t` comes strictly before `stepBefore x t`: the node state the
delivery produces, `x[j + 1][v].st`, is at or before the one `stateBefore x t v` reads.

The variables:
- `x`: the execution; `j`: the step of the delivery; `v`: the receiver; `sm`: the signed message
  delivered; `t`: the time.

Read aloud: what a validator receives before the time `t` is in its node state before `t`. -/
theorem deliver_before_of_time (hdiv : TimeDiverges x.toTrace) {j t : ℕ} {v : V}
    {sm : SignedMsg V (NamedObject V)} (hl : x.lbl j = AtomicAction.deliver v sm)
    -- the delivery happens before `t`
    (hj : x[j].time < t) : j < stepBefore x t :=
  lt_stepBefore_of_not_tickAllAwake x hdiv (fun t' h => by rw [hl] at h; cases h) hj

/-! ## Lifting a per-step relation -/

omit [RootOrder] in
/-- A relation preserved by every step from `i` to `j` holds from the `i`-th to the `j`-th term of
the sequence, for a reflexive and transitive relation. Applied with `f i := x[i][v].st` and a per-step monotonicity lemma about a node, it gives the relation
between the node's states at two steps.

The variables:
- `R`: the relation; `f`: the sequence, indexed by steps; `i`, `j`: two steps, `i` no later
  than `j`.

Read aloud: if each step from `i` to `j` keeps the relation, the relation holds from the `i`-th
term to the `j`-th. -/
theorem rel_of_forall_step {α : Type} (R : α → α → Prop)
    -- the relation is reflexive
    (hrefl : ∀ a, R a a)
    -- the relation is transitive
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (f : ℕ → α) {i j : ℕ} (hij : i ≤ j)
    -- every step from `i` to `j` keeps the relation
    (hstep : ∀ i', i ≤ i' → i' < j → R (f i') (f (i' + 1))) : R (f i) (f j) := by
  induction j, hij using Nat.le_induction with
  | base => exact hrefl _
  | succ j hij ih =>
      exact htrans _ _ _ (ih fun i' h1 h2 => hstep i' h1 (by omega)) (hstep j hij (by omega))

/-- A relation on node states that every step from `stepBefore x t` to `stepBefore x t'` keeps
for the validator `v` holds from `v`'s node state before `t` to its node state before `t'`, for
`t ≤ t'`. A step `i` of that range starts at a time from `t − 1` on
(`le_time_add_one_of_stepBefore_le`) and ends before `t'` (`lt_stepBefore_iff`).

The variables:
- `x`: the execution; `R`: the relation; `t`, `t'`: two times, `t` no later than `t'`; `v`: the
  validator.

Read aloud: what each step keeps between `v`'s node states holds between `v`'s node state before
`t` and its node state before `t'`. -/
theorem rel_stateBefore_of_step (hdiv : TimeDiverges x.toTrace) (R : NodeState V → NodeState V → Prop)
    -- the relation is reflexive
    (hrefl : ∀ n, R n n)
    -- the relation is transitive
    (htrans : ∀ n n' n'', R n n' → R n' n'' → R n n'')
    {t t' : ℕ} (h : t ≤ t') (v : V)
    -- every step from the one before `t` to the one before `t'` keeps the relation for `v`
    (hstep : ∀ i, stepBefore x t ≤ i → i < stepBefore x t' → R x[i][v].st x[i + 1][v].st) :
    R (stateBefore x t v) (stateBefore x t' v) :=
  rel_of_forall_step R hrefl htrans (fun i => x[i][v].st) (stepBefore_mono x hdiv h) hstep

/-- A relation on node states that every step from `j` to `stepBefore x t` keeps for the
validator `v` holds from `v`'s node state at the step `j` to its node state before `t`, when the
configuration `x[j]` is at a time before `t ≥ 1`.

The variables:
- `x`: the execution; `R`: the relation; `j`: the step; `t`: the time; `v`: the validator.

Read aloud: what each step keeps between `v`'s node states holds between `v`'s node state at a
configuration before `t` and its node state before `t`. -/
theorem rel_getElem_stateBefore (hdiv : TimeDiverges x.toTrace) (R : NodeState V → NodeState V → Prop)
    -- the relation is reflexive
    (hrefl : ∀ n, R n n)
    -- the relation is transitive
    (htrans : ∀ n n' n'', R n n' → R n' n'' → R n n'')
    {j t : ℕ} (ht : 1 ≤ t)
    -- the configuration `x[j]` is at a time before `t`
    (hj : x[j].time < t) (v : V)
    -- every step from `j` to the one before `t` keeps the relation for `v`
    (hstep : ∀ i, j ≤ i → i < stepBefore x t → R x[i][v].st x[i + 1][v].st) :
    R x[j][v].st (stateBefore x t v) :=
  rel_of_forall_step R hrefl htrans (fun i => x[i][v].st)
    ((time_lt_iff_le_stepBefore x hdiv ht).1 hj) hstep

/-- A relation on node states that every step from `stepBefore x t` to `j` keeps for the
validator `v` holds from `v`'s node state before `t` to its node state at the step `j`, when the
configuration `x[j]` is at the time `t ≥ 1` or later.

The variables:
- `x`: the execution; `R`: the relation; `t`: the time; `j`: the step; `v`: the validator.

Read aloud: what each step keeps between `v`'s node states holds between `v`'s node state before
`t` and its node state at a configuration at `t` or later. -/
theorem rel_stateBefore_getElem (hdiv : TimeDiverges x.toTrace) (R : NodeState V → NodeState V → Prop)
    -- the relation is reflexive
    (hrefl : ∀ n, R n n)
    -- the relation is transitive
    (htrans : ∀ n n' n'', R n n' → R n' n'' → R n n'')
    {t j : ℕ} (ht : 1 ≤ t)
    -- the configuration `x[j]` is at `t` or later
    (hj : t ≤ x[j].time) (v : V)
    -- every step from the one before `t` to `j` keeps the relation for `v`
    (hstep : ∀ i, stepBefore x t ≤ i → i < j → R x[i][v].st x[i + 1][v].st) :
    R (stateBefore x t v) x[j][v].st :=
  rel_of_forall_step R hrefl htrans (fun i => x[i][v].st)
    (Nat.le_of_lt (stepBefore_lt_of_le_time x hdiv ht hj)) hstep

end GoldilocksCorrectness.Proofs.Executions
