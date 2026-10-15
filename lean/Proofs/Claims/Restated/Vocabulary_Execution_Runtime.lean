import Proofs.Vocabulary.Execution.Runtime
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_NamedNode
import Model.Conditions.Vocabulary_Execution_Runtime
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Events, worlds and invariants along a run

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`. One event leads
to a set of worlds; these theorems say what a tick, a delivery or another validator's event does to
a validator's node state, that every world of a run satisfies the node invariant, and how the clock
and the finalized block of a store move along a run.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedRuntime
open Execution

omit [DecidableEq V] [Fintype V] in
/-- An event whose key is at most another's has a time at most the other's. -/
private theorem time_le_of_key_le' {e f : Record.Event V} (h : e.key ≤ f.key) :
    e.time ≤ f.time := by
  rcases Prod.Lex.le_iff.mp h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, every event before index `i` has a time at most the time of the event at
    index `i`. -/
private theorem time_le_of_mem_take' (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {i : Nat} {f : Record.Event V} (hf : rho.events[i]? = some f)
    (e : Record.Event V) (he : e ∈ rho.events.take i) : e.time ≤ f.time := by
  obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp hf
  have hsplit : rho.events = rho.events.take i ++ f :: rho.events.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i rho.events]
    rw [List.drop_eq_getElem_cons hi, hget]
  have hp := hsorted
  rw [hsplit] at hp
  exact time_le_of_key_le' ((List.pairwise_append.mp hp).2.2 e he f (List.mem_cons_self ..))

omit [DecidableEq V] [Fintype V] in
/-- A sublist of a list sorted by key is sorted by time. -/
private theorem pairwise_time_of_sorted {l l' : List (Record.Event V)}
    (hs : l.Pairwise (fun e f => e.key ≤ f.key)) (hsub : l'.Sublist l) :
    l'.Pairwise (fun e f => e.time ≤ f.time) :=
  (hs.sublist hsub).imp time_le_of_key_le'

omit [DecidableEq V] [Fintype V] in
/-- When the event at index `i` of `rho` is `e`, the events `i` to `i` of `rho` are the list `[e]`. -/
private theorem drop_take_succ {rho : Record.Run V} {i : Nat} {e : Record.Event V}
    (hi : rho.events[i]? = some e) : (rho.events.drop i).take (i + 1 - i) = [e] := by
  rw [Nat.add_sub_cancel_left, List.take_one, List.head?_drop, hi]
  rfl

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, the events with time before `t` form a prefix. -/
private theorem filter_eq_take_sorted' (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (p : Record.Event V → Bool)
    (hdown : ∀ e f : Record.Event V, e.key ≤ f.key → p f = true → p e = true) :
    rho.events.filter p = rho.events.take (rho.events.filter p).length := by
  refine List.prefix_iff_eq_take.mp ?_
  rw [Proofs.Bridges.filter_eq_takeWhile_of_pairwise hdown _ hsorted]
  exact List.takeWhile_prefix _

omit [DecidableEq V] [Fintype V] in
/-- If `e.key ≤ f.key` and `f`'s time is before `t`, then `e`'s time is before `t`. -/
private theorem downward_lt' (t : Time) :
    ∀ e f : Record.Event V, e.key ≤ f.key → decide (f.time < t) = true →
      decide (e.time < t) = true := by
  intro e f hk hf
  simp only [decide_eq_true_eq] at hf ⊢
  exact lt_of_le_of_lt (time_le_of_key_le' hk) hf

/-- The worlds the one-event list `[e]` leads to from `w` are the worlds
    `Record.worldStepOf M S w e`. -/
private theorem mem_foldlM_singleton (S : Setup V) (w w₂ : V → M.N) (e : Record.Event V) :
    w₂ ∈ [e].foldlM (Record.worldStepOf M S) w ↔ w₂ ∈ Record.worldStepOf M S w e := by
  rw [List.foldlM_cons, Set.bind_def]
  constructor
  · intro h
    obtain ⟨w', hw', h2⟩ := Set.mem_iUnion₂.mp h
    obtain rfl := Set.mem_singleton_iff.mp h2
    exact hw'
  · intro h
    exact Set.mem_iUnion₂.mpr ⟨w₂, h, Set.mem_singleton w₂⟩

/-- The one world a wake of `u` leads to from `w` is `w` with `u`'s node state replaced by `M.wake`
    of it. -/
private theorem mem_worldStepOf_wake (S : Setup V) (w w' : V → M.N) (u : V) (t : Time) :
    w' ∈ Record.worldStepOf M S w (.wake u t) ↔ w' = Function.update w u (M.wake (w u)) :=
  Iff.rfl

/-- In every world a wake leads to from `w`, every validator's store, signing record and grade cache
    are the ones in `w`. -/
private theorem wake_world_parts (facts : Record.Facts M) (S : Setup V) (w : V → M.N) (u : V)
    (t : Time) :
    ∀ w' ∈ Record.worldStepOf M S w (.wake u t), ∀ v,
      (w' v).st = (w v).st ∧ (w' v).record = (w v).record ∧ (w' v).cache = (w v).cache := by
  intro w' hw' v
  rw [mem_worldStepOf_wake] at hw'
  subst hw'
  by_cases hv : v = u
  · subst hv
    rw [Function.update_self]
    exact ⟨(facts.nd.wake_st_record _).1, (facts.nd.wake_st_record _).2, facts.nd.wake_cache _⟩
  · rw [Function.update_of_ne hv]
    exact ⟨rfl, rfl, rfl⟩

/-- After one event, the clock of `v`'s store in every world the event can lead to is the clock
    before it, or `v` is the event's validator and the clock is the event's time. -/
private theorem step_clock_cases (facts : Record.Facts M) (S : Setup V) (w : V → M.N)
    (e : Record.Event V) (v : V) :
    ∀ w' ∈ Record.worldStepOf M S w e,
      (w' v).st.core.t = (w v).st.core.t ∨ (v = e.node ∧ (w' v).st.core.t = e.time) := by
  intro w' hw'
  cases e with
  | wake u t =>
    left
    rw [(wake_world_parts facts S w u t w' hw' v).1]
  | tick u t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
    rcases hw' with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
    · by_cases hv : v = u
      · subst hv
        rw [Function.update_self]
        exact Or.inr ⟨rfl, (facts.nd.tick_clock S v (w v) t out hout).1⟩
      · rw [Function.update_of_ne hv]
        exact Or.inl rfl
    · exact Or.inl rfl
  | deliver u o t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
    rcases hw' with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
    · by_cases hv : v = u
      · subst hv
        rw [Function.update_self]
        exact Or.inl (facts.nd.process_clock S (w v) o n' hn').1
      · rw [Function.update_of_ne hv]
        exact Or.inl rfl
    · exact Or.inl rfl

/-- If the clock of `v`'s store in `w` and every event time of `l` are at most `bound`, so is the
    clock of `v`'s store in every world `l` can lead to from `w`. -/
private theorem foldlM_clock_le (facts : Record.Facts M) (S : Setup V) (v : V) (bound : Time) :
    ∀ (l : List (Record.Event V)) (w : V → M.N), (w v).st.core.t ≤ bound →
      (∀ e ∈ l, e.time ≤ bound) →
      ∀ w₂ ∈ l.foldlM (Record.worldStepOf M S) w, (w₂ v).st.core.t ≤ bound := by
  intro l
  induction l with
  | nil =>
    intro w hw _ w₂ hw₂
    obtain rfl := Set.mem_singleton_iff.mp hw₂
    exact hw
  | cons e l ih =>
    intro w hw hl w₂ hw₂
    rw [List.foldlM_cons, Set.bind_def] at hw₂
    obtain ⟨w', hw', hw₂'⟩ := Set.mem_iUnion₂.mp hw₂
    refine ih w' ?_ (fun f hf => hl f (List.mem_cons_of_mem _ hf)) w₂ hw₂'
    rcases step_clock_cases facts S w e v w' hw' with h | ⟨-, h⟩
    · rw [h]; exact hw
    · rw [h]; exact hl e (List.mem_cons_self ..)

/-- If `l` is sorted by time and the clock of `v`'s store in `w` is at most every event time of `l`,
    the clock of `v`'s store in every world `l` can lead to from `w` is at least the clock in `w`. -/
private theorem foldlM_clock_mono (facts : Record.Facts M) (S : Setup V) (v : V) :
    ∀ (l : List (Record.Event V)) (w : V → M.N), (∀ e ∈ l, (w v).st.core.t ≤ e.time) →
      l.Pairwise (fun e f => e.time ≤ f.time) →
      ∀ w₂ ∈ l.foldlM (Record.worldStepOf M S) w, (w v).st.core.t ≤ (w₂ v).st.core.t := by
  intro l
  induction l with
  | nil =>
    intro w _ _ w₂ hw₂
    obtain rfl := Set.mem_singleton_iff.mp hw₂
    exact le_rfl
  | cons e l ih =>
    intro w hl hp w₂ hw₂
    rw [List.foldlM_cons, Set.bind_def] at hw₂
    obtain ⟨w', hw', hw₂'⟩ := Set.mem_iUnion₂.mp hw₂
    have hp' := List.pairwise_cons.mp hp
    have hstep : (w v).st.core.t ≤ (w' v).st.core.t ∧
        ∀ f ∈ l, (w' v).st.core.t ≤ f.time := by
      rcases step_clock_cases facts S w e v w' hw' with h | ⟨-, h⟩
      · rw [h]; exact ⟨le_rfl, fun f hf => hl f (List.mem_cons_of_mem _ hf)⟩
      · rw [h]; exact ⟨hl e (List.mem_cons_self ..), hp'.1⟩
    exact hstep.1.trans (ih w' hstep.2 hp'.2 w₂ hw₂')

/-- One event moves the finalized block of `v`'s store, in every world the event can lead to, to a
    descendant of (or the same block as) the finalized block before it. -/
private theorem step_F_mono' (facts : Record.Facts M) (S : Setup V) (w : V → M.N)
    (e : Record.Event V) (v : V) :
    ∀ w' ∈ Record.worldStepOf M S w e, Block.Preceq (w v).st.core.F (w' v).st.core.F := by
  intro w' hw'
  cases e with
  | wake u t =>
    rw [(wake_world_parts facts S w u t w' hw' v).1]
    exact Proofs.ModelProperties.Preceq_self _
  | tick u t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
    rcases hw' with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
    · by_cases hu : u = v
      · subst u
        rw [Function.update_self]
        exact facts.nd.node_tick_F S v (w v) t out hout
      · rw [Function.update_of_ne (Ne.symm hu)]
        exact Proofs.ModelProperties.Preceq_self _
    · exact Proofs.ModelProperties.Preceq_self _
  | deliver u o t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
    rcases hw' with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
    · by_cases hu : u = v
      · subst u
        rw [Function.update_self]
        exact facts.nd.node_process_F S (w v) o n' hn'
      · rw [Function.update_of_ne (Ne.symm hu)]
        exact Proofs.ModelProperties.Preceq_self _
    · exact Proofs.ModelProperties.Preceq_self _

/-- In every world `w'` that `v`'s tick at `t` can lead to from `w`, `v`'s node state is the first
    component of an outcome of the tick, or the tick has no outcome and `v`'s node state is
    unchanged. -/
theorem Vocabulary.Proofs.NamedRuntime.step_tick (facts : Record.Facts M) (S : Setup V) (w : (V → M.N)) (v : V) (t : Time) :
    ∀ w' ∈ Record.worldStepOf M S w (.tick v t),
      (∃ out, M.tick S v (w v) t ⇢ out ∧ w' v = out.1) ∨
      ((∀ out, ¬ M.tick S v (w v) t ⇢ out) ∧ w' v = w v) := by
  intro w' hw'
  simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
  rcases hw' with ⟨out, hout, rfl⟩ | ⟨hno, rfl⟩
  · exact Or.inl ⟨out, hout, Function.update_self ..⟩
  · exact Or.inr ⟨hno, rfl⟩

/-- In every world `w'` that the delivery of `o` to `v` can lead to from `w`, `v`'s node state is an
    outcome of `v`'s receipt of `o`, or the receipt has no outcome and `v`'s node state is
    unchanged. -/
theorem Vocabulary.Proofs.NamedRuntime.step_deliver (facts : Record.Facts M) (S : Setup V) (w : (V → M.N)) (v : V) (o : NamedObject V) (t : Time) :
    ∀ w' ∈ Record.worldStepOf M S w (.deliver v o t),
      M.process S (w v) o ⇢ w' v ∨
      ((∀ n', ¬ M.process S (w v) o ⇢ n') ∧ w' v = w v) := by
  intro w' hw'
  simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
  rcases hw' with ⟨n', hn', rfl⟩ | ⟨hno, rfl⟩
  · left
    rw [Function.update_self]
    exact hn'
  · exact Or.inr ⟨hno, rfl⟩

/-- In every world `w'` that an event of another validator can lead to from `w`, `v`'s node state is
    the one in `w`. -/
theorem Vocabulary.Proofs.NamedRuntime.step_other (facts : Record.Facts M) (S : Setup V) (w : (V → M.N)) (e : Record.Event V) (v : V)
    (h : v ≠ e.node) : ∀ w' ∈ Record.worldStepOf M S w e, w' v = w v := by
  intro w' hw'
  cases e with
  | wake u t =>
    rw [mem_worldStepOf_wake] at hw'
    subst hw'
    exact Function.update_of_ne h _ _
  | tick u t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
    rcases hw' with ⟨out, -, rfl⟩ | ⟨-, rfl⟩
    · exact Function.update_of_ne h _ _
    · rfl
  | deliver u o t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
    rcases hw' with ⟨n', -, rfl⟩ | ⟨-, rfl⟩
    · exact Function.update_of_ne h _ _
    · rfl

/-- The node state `M.initial S v` that validator `v` starts from under setup `S` satisfies the node
    invariant. -/
theorem Vocabulary.Proofs.NamedRuntime.initial_invariant (facts : Record.Facts M) (S : Setup V) (v : V) :
    Restated.Vocabulary.Proofs.NamedRuntime.NodeInvariant M S (M.initial S v) :=
  ⟨(facts.nd.initial_invariants S v).1, (facts.nd.initial_invariants S v).2,
    facts.nd.cache_clipped_initial S v⟩

/-- If every validator's node state in `w` satisfies the node invariant, so does every validator's
    node state in every world one event can lead to from `w`. -/
private theorem step_invariant (facts : Record.Facts M) (S : Setup V) (w : V → M.N)
    (e : Record.Event V) (h : ∀ v, Restated.Vocabulary.Proofs.NamedRuntime.NodeInvariant M S (w v)) :
    ∀ w' ∈ Record.worldStepOf M S w e,
      ∀ v, Restated.Vocabulary.Proofs.NamedRuntime.NodeInvariant M S (w' v) := by
  intro w' hw' v
  cases e with
  | wake u t =>
    rw [mem_worldStepOf_wake] at hw'
    subst hw'
    by_cases hv : v = u
    · subst hv
      rw [Function.update_self]
      exact ⟨by rw [(facts.nd.wake_st_record (w v)).1]; exact (h v).1,
        by rw [(facts.nd.wake_st_record (w v)).2]; exact (h v).2.1,
        facts.nd.wake_cache_clipped (w v) (h v).2.2⟩
    · rw [Function.update_of_ne hv]
      exact h v
  | tick u t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
    rcases hw' with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
    · by_cases hv : v = u
      · subst hv
        rw [Function.update_self]
        exact ⟨facts.nd.confirmation_invariant_tick S v (w v) t (h v).1 out hout,
          facts.nd.record_invariant_tick S v (w v) t (h v).2.1 out hout,
          facts.nd.cache_clipped_tick S v (w v) t out hout⟩
      · rw [Function.update_of_ne hv]
        exact h v
    · exact h v
  | deliver u o t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
    rcases hw' with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
    · by_cases hv : v = u
      · subst hv
        rw [Function.update_self]
        exact ⟨(facts.nd.invariants_process S (w v) o (h v).1 (h v).2.1 n' hn').1,
          (facts.nd.invariants_process S (w v) o (h v).1 (h v).2.1 n' hn').2,
          facts.nd.cache_clipped_process S (w v) o n' hn'⟩
      · rw [Function.update_of_ne hv]
        exact h v
    · exact h v

/-- If every validator's node state in `w` satisfies the node invariant, so does every validator's
    node state in every world the events `l` can lead to from `w`. -/
private theorem fold_invariant (facts : Record.Facts M) (S : Setup V) :
    ∀ (l : List (Record.Event V)) (w : V → M.N),
      (∀ v, Restated.Vocabulary.Proofs.NamedRuntime.NodeInvariant M S (w v)) →
      ∀ w₂ ∈ l.foldlM (Record.worldStepOf M S) w,
        ∀ v, Restated.Vocabulary.Proofs.NamedRuntime.NodeInvariant M S (w₂ v) := by
  intro l
  induction l with
  | nil =>
    intro w h w₂ hw₂
    obtain rfl := Set.mem_singleton_iff.mp hw₂
    exact h
  | cons e l ih =>
    intro w h w₂ hw₂
    rw [List.foldlM_cons, Set.bind_def] at hw₂
    obtain ⟨w', hw', hw₂'⟩ := Set.mem_iUnion₂.mp hw₂
    exact ih w' (step_invariant facts S w e h w' hw') w₂ hw₂'

/-- In every world before the `i`-th event of `rho`, `v`'s node state satisfies the node invariant. -/
theorem Vocabulary.Proofs.NamedRuntime.stateBefore_invariants (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V) :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
      Restated.Vocabulary.Proofs.NamedRuntime.NodeInvariant M S (w₁ v) := fun w₁ hw₁ =>
  fold_invariant facts S (rho.events.take i) (fun u => M.initial S u)
    (Restated.Vocabulary.Proofs.NamedRuntime.initial_invariant facts S) w₁ hw₁ v

/-- In every world after the events of `rho` before time `t`, `v`'s node state satisfies the node
    invariant. -/
theorem Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t,
      Restated.Vocabulary.Proofs.NamedRuntime.NodeInvariant M S (w₁ v) := fun w₁ hw₁ =>
  fold_invariant facts S _ (fun u => M.initial S u)
    (Restated.Vocabulary.Proofs.NamedRuntime.initial_invariant facts S) w₁ hw₁ v

/-- In every world after the events of `rho` at or before time `t`, `v`'s node state satisfies the
    node invariant. -/
theorem Vocabulary.Proofs.NamedRuntime.readAt_invariants (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.NamedRun.readAt M S rho t,
      Restated.Vocabulary.Proofs.NamedRuntime.NodeInvariant M S (w₁ v) := fun w₁ hw₁ =>
  fold_invariant facts S _ (fun u => M.initial S u)
    (Restated.Vocabulary.Proofs.NamedRuntime.initial_invariant facts S) w₁ hw₁ v

/-- Before the first event of `rho`, the one world is the one where every validator `v` holds
    `M.initial S v`. -/
theorem Vocabulary.Proofs.NamedRuntime.stateBefore_zero (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) :
    Record.stateBeforeOf M S rho 0 = {fun v => M.initial S v} := rfl

/-- The worlds before the `(i + 1)`-th event of `rho` are the worlds the `i`-th event (if there is
    one) can lead to from a world before the `i`-th event. -/
theorem Vocabulary.Proofs.NamedRuntime.stateBefore_succ (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) :
    Record.stateBeforeOf M S rho (i + 1) =
      (Record.stateBeforeOf M S rho i >>= fun w₁ =>
        (rho.events[i]?.toList).foldlM (Record.worldStepOf M S) w₁) := by
  unfold Record.stateBeforeOf
  rw [List.take_add_one, List.foldlM_append]

/-- When the `i`-th event of `rho` is `v`'s tick at `t`, for every world `w₁` before it and every
    world `w₂` the tick can lead to from `w₁`, `v`'s node state in `w₂` is the first component of an
    outcome of the tick from `v`'s node state in `w₁`, or the tick has no outcome and `v`'s node
    state is unchanged. -/
theorem Vocabulary.Proofs.NamedRuntime.stateBefore_tick (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t)) :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    ∀ w₂ ∈ ((rho.events.drop i).take (i + 1 - i)).foldlM (Record.worldStepOf M S) w₁,
      (∃ out, M.tick S v (w₁ v) t ⇢ out ∧ w₂ v = out.1) ∨
      ((∀ out, ¬ M.tick S v (w₁ v) t ⇢ out) ∧ w₂ v = w₁ v) := by
  intro w₁ _ w₂ hw₂
  rw [drop_take_succ hi, mem_foldlM_singleton] at hw₂
  exact Restated.Vocabulary.Proofs.NamedRuntime.step_tick facts S w₁ v t w₂ hw₂

/-- When the `i`-th event of `rho` is the delivery of `o` to `v`, for every world `w₁` before it and
    every world `w₂` the delivery can lead to from `w₁`, `v`'s node state in `w₂` is an outcome of
    `v`'s receipt of `o` from its node state in `w₁`, or the receipt has no outcome and `v`'s node
    state is unchanged. -/
theorem Vocabulary.Proofs.NamedRuntime.stateBefore_deliver (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    {i : Nat} {v : V} {o : NamedObject V} {t : Time}
    (hi : rho.events[i]? = some (.deliver v o t)) :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    ∀ w₂ ∈ ((rho.events.drop i).take (i + 1 - i)).foldlM (Record.worldStepOf M S) w₁,
      M.process S (w₁ v) o ⇢ w₂ v ∨
      ((∀ n', ¬ M.process S (w₁ v) o ⇢ n') ∧ w₂ v = w₁ v) := by
  intro w₁ _ w₂ hw₂
  rw [drop_take_succ hi, mem_foldlM_singleton] at hw₂
  exact Restated.Vocabulary.Proofs.NamedRuntime.step_deliver facts S w₁ v o t w₂ hw₂

/-- When the `i`-th event of `rho` is an event of a validator other than `v`, for every world `w₁`
    before it and every world `w₂` the event can lead to from `w₁`, `v`'s node state in `w₂` is the
    one in `w₁`. -/
theorem Vocabulary.Proofs.NamedRuntime.stateBefore_other (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) {i : Nat} {e : Record.Event V}
    (hi : rho.events[i]? = some e) (v : V) (hv : v ≠ e.node) :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    ∀ w₂ ∈ ((rho.events.drop i).take (i + 1 - i)).foldlM (Record.worldStepOf M S) w₁,
      w₂ v = w₁ v := by
  intro w₁ _ w₂ hw₂
  rw [drop_take_succ hi, mem_foldlM_singleton] at hw₂
  exact Restated.Vocabulary.Proofs.NamedRuntime.step_other facts S w₁ e v hv w₂ hw₂

/-- For every path `W` of `rho`, if `v` is honest and `B` is among the bodies of `v`'s store in
    `W i`, then `B` is a block directly in the run read along `W`. -/
theorem Vocabulary.Proofs.NamedRuntime.directBlock_of_prefix (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {v : V}
    (hv : v ∈ rho.honest) (i : Nat) {B : NamedBlock V}
    (hB : B ∈ (W i v).st.bodies) :
    Restated.Vocabulary.Execution.NamedRun.directBlockInRun M S rho W B := Or.inr ⟨v, hv, i, hB⟩

/-- For every path `W` of `rho`, a block directly in the run read along `W` is in the run read along
    `W`. -/
theorem Vocabulary.Proofs.NamedRuntime.blockInRun_of_direct (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {B : NamedBlock V}
    (h : Restated.Vocabulary.Execution.NamedRun.directBlockInRun M S rho W B) :
    Restated.Vocabulary.Execution.NamedRun.blockInRun M S rho W B :=
  ⟨B, h, by cases B <;> simp [NamedBlock.Preceq, NamedBlock.preceq]⟩

/-- For `i ≤ j`, every world `w₁` before the `i`-th event of `rho` and every world `w₂` the events
    `i` to `j - 1` can lead to from `w₁`, the finalized block of `v`'s store in `w₁` is an ancestor
    of, or the same block as, the finalized block of `v`'s store in `w₂`. -/
theorem Vocabulary.Proofs.NamedRuntime.stateBefore_F_mono (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (v : V)
    {i j : Nat} (hij : i ≤ j) :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    ∀ w₂ ∈ ((rho.events.drop i).take (j - i)).foldlM (Record.worldStepOf M S) w₁,
    Block.Preceq (w₁ v).st.core.F (w₂ v).st.core.F := by
  intro w₁ _
  suffices h : ∀ (l : List (Record.Event V)) (w : V → M.N),
      ∀ w₂ ∈ l.foldlM (Record.worldStepOf M S) w,
        Block.Preceq (w v).st.core.F (w₂ v).st.core.F from h _ w₁
  intro l
  induction l with
  | nil =>
      intro w w₂ hw₂
      obtain rfl := Set.mem_singleton_iff.mp hw₂
      exact Proofs.ModelProperties.Preceq_self _
  | cons e l ih =>
      intro w w₂ hw₂
      rw [List.foldlM_cons, Set.bind_def] at hw₂
      obtain ⟨w', hw', hw₂'⟩ := Set.mem_iUnion₂.mp hw₂
      exact Proofs.ModelProperties.Preceq_trans
        (step_F_mono' facts S w e v w' hw') (ih w' w₂ hw₂')

/-- In a run sorted by key, when the `i`-th event `e` has a nonnegative time, the clock of `v`'s
    store in every world before the `i`-th event is at most `e`'s time. -/
theorem Vocabulary.Proofs.NamedRuntime.stateBefore_clock_le_event (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {i : Nat} {e : Record.Event V} (hi : rho.events[i]? = some e) (hnonneg : 0 ≤ e.time) (v : V) :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho i, (w₁ v).st.core.t ≤ e.time := by
  intro w₁ hw₁
  refine foldlM_clock_le facts S v e.time (rho.events.take i) (fun u => M.initial S u) ?_
    (time_le_of_mem_take' rho hsorted hi) w₁ hw₁
  show (M.initial S v).st.core.t ≤ e.time
  rw [facts.nd.initial_st S v, facts.hd.initial_core_t]
  exact hnonneg

/-- In a run sorted by key with nonnegative event times, for `i ≤ j`, every world `w₁` before the
    `i`-th event and every world `w₂` the events `i` to `j - 1` can lead to from `w₁`, the clock of
    `v`'s store in `w₁` is at most the clock of `v`'s store in `w₂`. -/
theorem Vocabulary.Proofs.NamedRuntime.stateBefore_clock_mono (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (hnonneg : ∀ e ∈ rho.events, 0 ≤ e.time) (v : V) {i j : Nat} (hij : i ≤ j) :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    ∀ w₂ ∈ ((rho.events.drop i).take (j - i)).foldlM (Record.worldStepOf M S) w₁,
    (w₁ v).st.core.t ≤ (w₂ v).st.core.t := by
  intro w₁ hw₁ w₂ hw₂
  refine foldlM_clock_mono facts S v _ w₁ ?_
    (pairwise_time_of_sorted hsorted ((List.take_sublist _ _).trans (List.drop_sublist _ _)))
    w₂ hw₂
  intro e he
  have hed : e ∈ rho.events.drop i := List.mem_of_mem_take he
  cases hf : rho.events[i]? with
  | none =>
    rw [List.getElem?_eq_none_iff] at hf
    rw [List.drop_eq_nil_of_le hf] at hed
    simp at hed
  | some f =>
    have h1 := Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_clock_le_event facts S rho
      hsorted hf (hnonneg f (List.mem_of_getElem? hf)) v w₁ hw₁
    obtain ⟨hil, hget⟩ := List.getElem?_eq_some_iff.mp hf
    have hp := hsorted.sublist (List.drop_sublist i rho.events)
    rw [List.drop_eq_getElem_cons hil, hget] at hed hp
    rcases List.mem_cons.mp hed with rfl | hrest
    · exact h1
    · exact h1.trans (time_le_of_key_le' ((List.pairwise_cons.mp hp).1 e hrest))

/-- Along a path `W` of `rho`, the world `W (m + d)` is one the events `m` to `m + d - 1` of `rho`
    can lead to from `W m`. -/
private theorem onePath_fold (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (m : Nat) :
    ∀ d : Nat, W (m + d) ∈ ((rho.events.drop m).take d).foldlM (Record.worldStepOf M S) (W m)
  | 0 => Set.mem_singleton _
  | d + 1 => by
      have h := onePath_fold S rho W hW m d
      have hs := (hW (m + d)).2
      rw [Nat.add_sub_cancel_left] at hs
      rw [List.take_add, List.foldlM_append, Set.bind_def, List.drop_drop]
      exact Set.mem_iUnion₂.mpr ⟨W (m + d), h, hs⟩

/-- In a run sorted by key with nonnegative event times, along a path `W` on which every tick event
    has an outcome from the node state the path holds before it, if the `j`-th event is `v`'s tick
    at `t` and `j < i`, then the clock of `v`'s store in `W i` is at least `t`. -/
theorem Vocabulary.Proofs.NamedRuntime.tick_time_le_clock (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (hnonneg : ∀ e ∈ rho.events, 0 ≤ e.time)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hto : ∀ (i : Nat) (u : V) (t : Int), rho.events[i]? = some (Record.Event.tick u t) →
      ∃ out, M.tick S u (W i u) t ⇢ out)
    {i j : Nat} {v : V} {t : Time}
    (hj : rho.events[j]? = some (.tick v t)) (hji : j < i) :
    t ≤ (W i v).st.core.t := by
  have hstep := (hW j).2
  rw [drop_take_succ hj, mem_foldlM_singleton] at hstep
  have ht : (W (j + 1) v).st.core.t = t := by
    rcases Restated.Vocabulary.Proofs.NamedRuntime.step_tick facts S (W j) v t (W (j + 1)) hstep with
      ⟨out, hout, h⟩ | ⟨hno, -⟩
    · rw [h]
      exact (facts.nd.tick_clock S v (W j v) t out hout).1
    · obtain ⟨out, hout⟩ := hto j v t hj
      exact absurd hout (hno out)
  rw [← ht]
  have hfold := onePath_fold S rho W hW (j + 1) (i - (j + 1))
  rw [show j + 1 + (i - (j + 1)) = i by omega] at hfold
  exact Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_clock_mono facts S rho hsorted hnonneg v
    (by omega : j + 1 ≤ i) (W (j + 1)) (hW (j + 1)).1 (W i) hfold

/-- In a run sorted by key, for every time `t` there is an index `n` such that the worlds strictly
    before time `t` are the worlds before the `n`-th event, and every event before index `n` has a
    time before `t`. -/
theorem Vocabulary.Proofs.NamedRuntime.stateBeforeTime_eq_prefix (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (t : Time) :
    ∃ n, Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t = Record.stateBeforeOf M S rho n ∧
      ∀ j e, j < n → rho.events[j]? = some e → e.time < t := by
  let p : Record.Event V → Bool := fun e => decide (e.time < t)
  have hf := filter_eq_take_sorted' rho hsorted p (downward_lt' t)
  refine ⟨(rho.events.filter p).length, ?_, ?_⟩
  · exact congrArg (fun events => events.foldlM (Record.worldStepOf M S) (fun u => M.initial S u)) hf
  · intro j e hj he
    have hm : e ∈ rho.events.filter p := by
      rw [hf]
      exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj]; exact he)
    simpa only [p, decide_eq_true_eq] using (List.mem_filter.mp hm).2

end

end DecoupledConsensusModel.Sts.Restated
