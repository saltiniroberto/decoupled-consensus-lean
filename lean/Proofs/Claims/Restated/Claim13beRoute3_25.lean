import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_CacheProvenance
import Model.Conditions.Vocabulary_Internal_Definitions_NamedExecutionQueries
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Alignment
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Event
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Protocol_Grades_CacheProvenance
import Model.Conditions.Vocabulary_Protocol_Handlers_Pool
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25

/-!
# Runs sorted by key: worlds, ticks, caches and pools

Facts about a run whose events are sorted by key, read over the worlds the run can reach: a tick
reads the node state strictly before its time, completed cache phases come from an earlier tick,
store clocks are at most event times, pool votes keep their stamps, and a validator emits at most
one Goldfish vote per slot. Stated over a model `M : Record.Model V`.
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
open Execution

omit [DecidableEq V] [Fintype V] in
/-- An event whose key is at most another's has a time at most the other's. -/
private theorem time_le_of_key_le₂ {e f : Record.Event V} (h : e.key ≤ f.key) :
    e.time ≤ f.time := by
  rcases Prod.Lex.le_iff.mp h with hlt | ⟨heq, _⟩
  · exact hlt.le
  · exact heq.le

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, the events satisfying a test that holds downward in the key order form a
    prefix. -/
private theorem filter_eq_take_sorted₂ (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (p : Record.Event V → Bool)
    (hdown : ∀ e f : Record.Event V, e.key ≤ f.key → p f = true → p e = true) :
    rho.events.filter p = rho.events.take (rho.events.filter p).length := by
  refine List.prefix_iff_eq_take.mp ?_
  rw [Proofs.Bridges.filter_eq_takeWhile_of_pairwise hdown _ hsorted]
  exact List.takeWhile_prefix _

omit [DecidableEq V] [Fintype V] in
/-- "Time before `t`" holds of an event whose key is at most the key of an event with time before
    `t`. -/
private theorem downward_lt₂ (t : Time) :
    ∀ e f : Record.Event V, e.key ≤ f.key → decide (f.time < t) = true →
      decide (e.time < t) = true := by
  intro e f hk hf
  simp only [decide_eq_true_eq] at hf ⊢
  exact lt_of_le_of_lt (time_le_of_key_le₂ hk) hf

omit [DecidableEq V] [Fintype V] in
/-- When the event at index `i` of `rho` is `e`, the events `i` to `i` of `rho` are the list `[e]`. -/
private theorem drop_take_succ₂ {rho : Record.Run V} {i : Nat} {e : Record.Event V}
    (hi : rho.events[i]? = some e) : (rho.events.drop i).take (i + 1 - i) = [e] := by
  rw [Nat.add_sub_cancel_left, List.take_one, List.head?_drop, hi]
  rfl

omit [DecidableEq V] [Fintype V] in
/-- When `rho` has no event at index `i`, the events `i` to `i` of `rho` are the empty list. -/
private theorem drop_take_succ_none₂ {rho : Record.Run V} {i : Nat}
    (hi : rho.events[i]? = none) : (rho.events.drop i).take (i + 1 - i) = [] := by
  rw [List.getElem?_eq_none_iff] at hi
  rw [List.drop_eq_nil_of_le hi]
  exact List.take_nil

omit [DecidableEq V] [Fintype V] in
/-- For `m ≤ j ≤ n`, the elements `m` to `n - 1` of a list are the elements `m` to `j - 1` followed
    by the elements `j` to `n - 1`. -/
private theorem slice_split₂ {α : Type} (l : List α) {m j n : Nat} (hmj : m ≤ j) (hjn : j ≤ n) :
    (l.drop m).take (n - m) = (l.drop m).take (j - m) ++ (l.drop j).take (n - j) := by
  have h : n - m = (j - m) + (n - j) := by omega
  rw [h, List.take_add, List.drop_drop, Nat.add_sub_cancel' hmj]

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key in which a tick event sits at one index only, if the `i`-th event is
    `v`'s tick at `t`, then the number `n_t` of events with a time before `t` is at most `i`, and
    every event from index `n_t` to `i - 1` is not at `v` or is `v`'s wake at `t`. -/
private theorem tick_index_facts₂ (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (huniq : Restated.TickIndexUnique rho) {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t)) :
    (rho.events.filter (fun e => decide (e.time < t))).length ≤ i ∧
    ∀ j e, (rho.events.filter (fun e => decide (e.time < t))).length ≤ j → j < i →
      rho.events[j]? = some e → e.node ≠ v ∨ e = Record.Event.wake v t := by
  have hfilter := filter_eq_take_sorted₂ rho hsorted _ (downward_lt₂ t)
  refine ⟨?_, ?_⟩
  · by_contra hcon
    have hlt : i < (rho.events.filter (fun e => decide (e.time < t))).length :=
      Nat.lt_of_not_ge hcon
    have hmem : Record.Event.tick v t ∈ rho.events.filter (fun e => decide (e.time < t)) := by
      rw [hfilter]
      exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hlt]; exact hi)
    have hp := (List.mem_filter.mp hmem).2
    simp only [decide_eq_true_eq, Record.Event.time] at hp
    exact lt_irrefl _ hp
  · intro j e hj hji hget
    have hlow : t ≤ e.time := by
      have hf := Restated.filter_false_of_index_ge_sorted rho hsorted _ (downward_lt₂ t) hj hget
      simpa using hf
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hget
    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
    have hkey : Record.Event.key e ≤ Record.Event.key (Record.Event.tick v t) := by
      have hp := (List.pairwise_iff_getElem.mp hsorted) j i hjl hil hji
      rw [hje, hie] at hp
      exact hp
    have hteq : Record.Event.time e = t :=
      le_antisymm (time_le_of_key_le₂ hkey) hlow
    by_cases hnode : e.node = v
    · right
      cases e with
      | wake u t' =>
        simp only [Record.Event.node] at hnode
        simp only [Record.Event.time] at hteq
        rw [hnode, hteq]
      | tick u t' =>
        exfalso
        simp only [Record.Event.node] at hnode
        simp only [Record.Event.time] at hteq
        have heq : Record.Event.tick u t' = Record.Event.tick v t := by rw [hnode, hteq]
        have hev : rho.events[j] = rho.events[i] := by rw [hje, hie, heq]
        have hij : j = i := huniq (hje.trans heq) hev
        omega
      | deliver u o t' =>
        exfalso
        simp only [Record.Event.time] at hteq
        subst hteq
        simp [Record.Event.key, Record.Event.time, Record.Event.phase, Prod.Lex.toLex_le_toLex] at hkey
    · exact Or.inl hnode

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, an event at an index less than the number of events with a time before
    `t` has a time before `t`. -/
private theorem time_lt_of_lt_filter₂ (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (t : Time) {j : Nat}
    {e : Record.Event V} (hj : j < (rho.events.filter (fun e => decide (e.time < t))).length)
    (he : rho.events[j]? = some e) : e.time < t := by
  have hfilter := filter_eq_take_sorted₂ rho hsorted _ (downward_lt₂ t)
  have hm : e ∈ rho.events.filter (fun e => decide (e.time < t)) := by
    rw [hfilter]
    exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj]; exact he)
  simpa only [decide_eq_true_eq] using (List.mem_filter.mp hm).2

/-- The worlds the one-event list `[e]` leads to from `w` are the worlds
    `Record.worldStepOf M S w e`. -/
private theorem mem_foldlM_singleton₂ (S : Setup V) (w w₂ : V → M.N) (e : Record.Event V) :
    w₂ ∈ [e].foldlM (Record.worldStepOf M S) w ↔ w₂ ∈ Record.worldStepOf M S w e := by
  rw [List.foldlM_cons, Set.bind_def]
  constructor
  · intro h
    obtain ⟨w', hw', h2⟩ := Set.mem_iUnion₂.mp h
    obtain rfl := Set.mem_singleton_iff.mp h2
    exact hw'
  · intro h
    exact Set.mem_iUnion₂.mpr ⟨w₂, h, Set.mem_singleton w₂⟩

/-- A world the events `l₁ ++ l₂` lead to from `w` is one the events `l₂` lead to from a world the
    events `l₁` lead to from `w`, and conversely. -/
private theorem mem_foldlM_append₂ (S : Setup V) (l₁ l₂ : List (Record.Event V)) (w w₂ : V → M.N) :
    w₂ ∈ (l₁ ++ l₂).foldlM (Record.worldStepOf M S) w ↔
      ∃ w' ∈ l₁.foldlM (Record.worldStepOf M S) w,
        w₂ ∈ l₂.foldlM (Record.worldStepOf M S) w' := by
  rw [List.foldlM_append, Set.bind_def]
  constructor
  · intro h
    obtain ⟨w', hw', h2⟩ := Set.mem_iUnion₂.mp h
    exact ⟨w', hw', h2⟩
  · rintro ⟨w', hw', h2⟩
    exact Set.mem_iUnion₂.mpr ⟨w', hw', h2⟩

/-- For `i ≤ j`, a world `w₂` can hold before the `j`-th event of `rho` exactly when it is reached,
    by the events `i` to `j - 1` of `rho`, from a world that can hold before the `i`-th event. -/
private theorem mem_stateBeforeOf_split₂ (S : Setup V) (rho : Record.Run V) {i j : Nat}
    (hij : i ≤ j) (w₂ : V → M.N) :
    w₂ ∈ Record.stateBeforeOf M S rho j ↔
      ∃ w₁ ∈ Record.stateBeforeOf M S rho i,
        w₂ ∈ ((rho.events.drop i).take (j - i)).foldlM (Record.worldStepOf M S) w₁ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  unfold Record.stateBeforeOf
  rw [Nat.add_sub_cancel_left, List.take_add, List.foldlM_append, Set.bind_def]
  constructor
  · intro h
    obtain ⟨w₁, hw₁, h2⟩ := Set.mem_iUnion₂.mp h
    exact ⟨w₁, hw₁, h2⟩
  · rintro ⟨w₁, hw₁, h2⟩
    exact Set.mem_iUnion₂.mpr ⟨w₁, hw₁, h2⟩

/-- For `m ≤ j ≤ n`, a world the events `m` to `n - 1` of `rho` lead to from `w` is one the events
    `j` to `n - 1` lead to from a world the events `m` to `j - 1` lead to from `w`, and conversely. -/
private theorem mem_slice_split₂ (S : Setup V) (rho : Record.Run V) {m j n : Nat} (hmj : m ≤ j)
    (hjn : j ≤ n) (w w₂ : V → M.N) :
    w₂ ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) w ↔
      ∃ w' ∈ ((rho.events.drop m).take (j - m)).foldlM (Record.worldStepOf M S) w,
        w₂ ∈ ((rho.events.drop j).take (n - j)).foldlM (Record.worldStepOf M S) w' := by
  rw [slice_split₂ rho.events hmj hjn]
  exact mem_foldlM_append₂ S _ _ w w₂

/-- In a run sorted by key, the worlds strictly before `t` are the worlds before the event whose
    index is the number of events with a time before `t`. -/
private theorem stateBeforeTime_eq₂ (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (t : Time) :
    Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t =
      Record.stateBeforeOf M S rho (rho.events.filter (fun e => decide (e.time < t))).length := by
  show (rho.events.filter (fun e => decide (e.time < t))).foldlM (Record.worldStepOf M S)
      (fun v => M.initial S v) =
    (rho.events.take (rho.events.filter (fun e => decide (e.time < t))).length).foldlM
      (Record.worldStepOf M S) (fun v => M.initial S v)
  rw [← filter_eq_take_sorted₂ rho hsorted _ (downward_lt₂ t)]

/-- If a world `w₂` is reached from `w` by the events `n` to `n` of `rho`, then either `rho` has no
    event at index `n` and `w₂` is `w`, or the `n`-th event is some `e` and `w₂` is one of the
    worlds `e` can lead to from `w`. -/
private theorem step_cases₂ (S : Setup V) (rho : Record.Run V) (n : Nat) (w w₂ : V → M.N)
    (h : w₂ ∈ ((rho.events.drop n).take (n + 1 - n)).foldlM (Record.worldStepOf M S) w) :
    (rho.events[n]? = none ∧ w₂ = w) ∨
      ∃ e, rho.events[n]? = some e ∧ w₂ ∈ Record.worldStepOf M S w e := by
  rcases hev : rho.events[n]? with _ | e
  · rw [drop_take_succ_none₂ hev] at h
    exact Or.inl ⟨rfl, Set.mem_singleton_iff.mp h⟩
  · rw [drop_take_succ₂ hev, mem_foldlM_singleton₂] at h
    exact Or.inr ⟨e, rfl, h⟩

/-- If every event of `l` is not at `v` or is a wake of `v`, then in every world the events of `l`
    lead to from `w`, `v`'s store is the one in `w`. -/
private theorem foldlM_st_of_ne_or_wake₂ (facts : Record.Facts M) (S : Setup V) (v : V) :
    ∀ (l : List (Record.Event V)) (w : V → M.N),
      (∀ e ∈ l, e.node ≠ v ∨ ∃ t, e = Record.Event.wake v t) →
      ∀ w₂ ∈ l.foldlM (Record.worldStepOf M S) w, (w₂ v).st = (w v).st := by
  intro l
  induction l with
  | nil =>
    intro w _ w₂ hw₂
    rw [Set.mem_singleton_iff.mp hw₂]
  | cons e l ih =>
    intro w hl w₂ hw₂
    rw [List.foldlM_cons, Set.bind_def] at hw₂
    obtain ⟨w', hw', hw₂'⟩ := Set.mem_iUnion₂.mp hw₂
    rw [ih w' (fun e' he' => hl e' (List.mem_cons_of_mem _ he')) w₂ hw₂']
    rcases hl e (List.mem_cons.mpr (Or.inl rfl)) with hne | ⟨t, rfl⟩
    · cases e with
      | wake u t =>
        have hu : u ≠ v := hne
        have h' : w' = Function.update w u (M.wake (w u)) := hw'
        rw [h', Function.update_of_ne (Ne.symm hu)]
      | tick u t =>
        have hu : u ≠ v := hne
        rcases hw' with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
        · rw [Function.update_of_ne (Ne.symm hu)]
        · rfl
      | deliver u o t =>
        have hu : u ≠ v := hne
        rcases hw' with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
        · rw [Function.update_of_ne (Ne.symm hu)]
        · rfl
    · have h' : w' = Function.update w v (M.wake (w v)) := hw'
      rw [h', Function.update_self, (facts.nd.wake_st_record _).1]

/-- If every event of `l` is not at `v` or is a wake of `v`, then in every world the events of `l`
    lead to from `w`, `v`'s node state is the one in `w` or its wake `M.wake (w v)`. -/
private theorem foldlM_eq_or_wake_of_ne_or_wake₂ (facts : Record.Facts M) (S : Setup V) (v : V) :
    ∀ (l : List (Record.Event V)) (w : V → M.N),
      (∀ e ∈ l, e.node ≠ v ∨ ∃ t, e = Record.Event.wake v t) →
      ∀ w₂ ∈ l.foldlM (Record.worldStepOf M S) w, w₂ v = w v ∨ w₂ v = M.wake (w v) := by
  intro l
  induction l with
  | nil =>
    intro w _ w₂ hw₂
    exact Or.inl (by rw [Set.mem_singleton_iff.mp hw₂])
  | cons e l ih =>
    intro w hl w₂ hw₂
    rw [List.foldlM_cons, Set.bind_def] at hw₂
    obtain ⟨w', hw', hw₂'⟩ := Set.mem_iUnion₂.mp hw₂
    have hrest := ih w' (fun e' he' => hl e' (List.mem_cons_of_mem _ he')) w₂ hw₂'
    rcases hl e (List.mem_cons.mpr (Or.inl rfl)) with hne | ⟨t, rfl⟩
    · have hw'v : w' v = w v := by
        cases e with
        | wake u t =>
          have hu : u ≠ v := hne
          have h' : w' = Function.update w u (M.wake (w u)) := hw'
          rw [h', Function.update_of_ne (Ne.symm hu)]
        | tick u t =>
          have hu : u ≠ v := hne
          rcases hw' with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
          · rw [Function.update_of_ne (Ne.symm hu)]
          · rfl
        | deliver u o t =>
          have hu : u ≠ v := hne
          rcases hw' with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
          · rw [Function.update_of_ne (Ne.symm hu)]
          · rfl
      rw [hw'v] at hrest
      exact hrest
    · have h' : w' = Function.update w v (M.wake (w v)) := hw'
      rw [h', Function.update_self, facts.nd.wake_idem] at hrest
      exact Or.inr (hrest.elim id id)

/-- If every event from index `m` to `n - 1` of `rho` is not at `v` or is a wake of `v`, then in
    every world the events `m` to `n - 1` lead to from `w₁`, `v`'s store is the one in `w₁`. -/
private theorem slice_st_of_ne_or_wake₂ (facts : Record.Facts M) (S : Setup V)
    (rho : Record.Run V) (v : V) {m n : Nat}
    (h : ∀ j e, m ≤ j → j < n → rho.events[j]? = some e →
      e.node ≠ v ∨ ∃ t, e = Record.Event.wake v t)
    (w₁ : V → M.N) :
    ∀ w₂ ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) w₁,
      (w₂ v).st = (w₁ v).st := by
  refine foldlM_st_of_ne_or_wake₂ facts S v _ w₁ ?_
  intro e he
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp he
  by_cases hkn : k < n - m
  · rw [List.getElem?_take_of_lt hkn, List.getElem?_drop] at hk
    exact h (m + k) e (by omega) (by omega) hk
  · rw [List.getElem?_eq_none_iff.mpr (by simp; omega)] at hk
    cases hk

/-- If every receipt and every tick of `v` from a store whose clock is at most the tick's time is a
    `PoolStep`, then one event from `w` to `w₂`, where a tick of `v` is at a time at least the clock
    of `v`'s store in `w`, keeps every vote and stamp of `v`'s store and keeps its four pool
    conditions. -/
private theorem step_pool₂ (facts : Record.Facts M) (S : Setup V) (v : V)
    (hproc : ∀ (n : M.N) (o : NamedObject V) (n' : M.N), M.process S n o ⇢ n' →
      Restated.Vocabulary.Protocol.PoolStep M n.st.core n'.st.core)
    (htickstep : ∀ (n : M.N) (t : Time) (out : M.N × List (NamedObject V)),
      M.tick S v n t ⇢ out → n.st.core.t ≤ t →
      Restated.Vocabulary.Protocol.PoolStep M n.st.core out.1.st.core)
    (w w₂ : V → M.N) (e : Record.Event V) (hw₂ : w₂ ∈ Record.worldStepOf M S w e)
    (hclock : ∀ t, e = .tick v t → (w v).st.core.t ≤ t)
    (hst : Restated.Vocabulary.Protocol.PoolStamps M (w v).st.core) :
    Restated.Vocabulary.Protocol.PoolCarry M (w v).st.core (w₂ v).st.core ∧
      Restated.Vocabulary.Protocol.PoolStamps M (w₂ v).st.core := by
  cases e with
  | wake u t =>
    have h' : w₂ = Function.update w u (M.wake (w u)) := hw₂
    subst h'
    by_cases hv : v = u
    · subst hv
      rw [Function.update_self, (facts.nd.wake_st_record _).1]
      exact ⟨⟨fun _ _ h => h, fun _ _ h => h⟩, hst⟩
    · rw [Function.update_of_ne hv]
      exact ⟨⟨fun _ _ h => h, fun _ _ h => h⟩, hst⟩
  | tick u t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw₂
    rcases hw₂ with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
    · by_cases hv : v = u
      · subst hv
        rw [Function.update_self]
        exact htickstep (w v) t out hout (hclock t rfl) hst
      · rw [Function.update_of_ne hv]
        exact ⟨⟨fun _ _ h => h, fun _ _ h => h⟩, hst⟩
    · exact ⟨⟨fun _ _ h => h, fun _ _ h => h⟩, hst⟩
  | deliver u o t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw₂
    rcases hw₂ with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
    · by_cases hv : v = u
      · subst hv
        rw [Function.update_self]
        exact hproc (w v) o n' hn' hst
      · rw [Function.update_of_ne hv]
        exact ⟨⟨fun _ _ h => h, fun _ _ h => h⟩, hst⟩
    · exact ⟨⟨fun _ _ h => h, fun _ _ h => h⟩, hst⟩

/-- If the initial store satisfies the four pool conditions and every receipt and every tick from a
    store whose clock is at most the tick's time is a `PoolStep`, then in a run sorted by key with
    nonnegative event times, `v`'s store in every world before every event satisfies the four pool
    conditions. -/
private theorem poolStamps_core₂ (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V}
    (hsorted : ρ.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (hin : ∀ e ∈ ρ.events, 0 ≤ e.time ∧ e.time ≤ ρ.horizon)
    (hinit : Restated.Vocabulary.Protocol.PoolStamps M (M.ns_initial : M.NS).core)
    (hproc : ∀ (n : M.N) (o : NamedObject V) (n' : M.N), M.process S n o ⇢ n' →
      Restated.Vocabulary.Protocol.PoolStep M n.st.core n'.st.core)
    (htickstep : ∀ (v : V) (n : M.N) (t : Time) (out : M.N × List (NamedObject V)),
      M.tick S v n t ⇢ out → n.st.core.t ≤ t →
      Restated.Vocabulary.Protocol.PoolStep M n.st.core out.1.st.core)
    (v : V) : ∀ n : Nat, ∀ w₁ ∈ Record.stateBeforeOf M S ρ n,
      Restated.Vocabulary.Protocol.PoolStamps M (w₁ v).st.core := by
  intro n
  induction n with
  | zero =>
    intro w₁ hw₁
    rw [Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_zero facts] at hw₁
    obtain rfl := Set.mem_singleton_iff.mp hw₁
    show Restated.Vocabulary.Protocol.PoolStamps M (M.initial S v).st.core
    rw [facts.nd.initial_st]
    exact hinit
  | succ n ih =>
    intro w₁ hw₁
    obtain ⟨w, hw, hw₁'⟩ := (mem_stateBeforeOf_split₂ S ρ (Nat.le_succ n) w₁).mp hw₁
    rcases step_cases₂ S ρ n w w₁ hw₁' with ⟨-, hww⟩ | ⟨e, hev, hstep⟩
    · rw [hww]
      exact ih w hw
    · refine (step_pool₂ facts S v hproc (htickstep v) w w₁ e hstep ?_ (ih w hw)).2
      intro t he
      subst he
      exact Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_clock_le_event facts S ρ hsorted hev
        (hin _ (List.mem_of_getElem? hev)).1 v w hw

/-- Under the hypotheses of `poolStamps_core₂`, from a world before event `m` to a world the events
    `m` to `n - 1` lead to, with `m ≤ n`, `v`'s store keeps every vote and every stamp. -/
private theorem pool_carry_core₂ (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V}
    (hsorted : ρ.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (hin : ∀ e ∈ ρ.events, 0 ≤ e.time ∧ e.time ≤ ρ.horizon)
    (hinit : Restated.Vocabulary.Protocol.PoolStamps M (M.ns_initial : M.NS).core)
    (hproc : ∀ (n : M.N) (o : NamedObject V) (n' : M.N), M.process S n o ⇢ n' →
      Restated.Vocabulary.Protocol.PoolStep M n.st.core n'.st.core)
    (htickstep : ∀ (v : V) (n : M.N) (t : Time) (out : M.N × List (NamedObject V)),
      M.tick S v n t ⇢ out → n.st.core.t ≤ t →
      Restated.Vocabulary.Protocol.PoolStep M n.st.core out.1.st.core)
    (v : V) {m : Nat} : ∀ w₁ ∈ Record.stateBeforeOf M S ρ m, ∀ n : Nat, m ≤ n →
      ∀ w₂ ∈ ((ρ.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) w₁,
      Restated.Vocabulary.Protocol.PoolCarry M (w₁ v).st.core (w₂ v).st.core := by
  intro w₁ hw₁ n
  induction n with
  | zero =>
    intro hle w₂ hw₂
    rw [Nat.zero_sub, List.take_zero] at hw₂
    obtain rfl := Set.mem_singleton_iff.mp hw₂
    exact ⟨fun _ _ h => h, fun _ _ h => h⟩
  | succ n ih =>
    intro hle w₂ hw₂
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · have hmn : m ≤ n := Nat.lt_succ_iff.mp hlt
      obtain ⟨w', hw', hw₂'⟩ := (mem_slice_split₂ S ρ hmn (Nat.le_succ n) w₁ w₂).mp hw₂
      have hc1 := ih hmn w' hw'
      have hw'mem : w' ∈ Record.stateBeforeOf M S ρ n :=
        (mem_stateBeforeOf_split₂ S ρ hmn w').mpr ⟨w₁, hw₁, hw'⟩
      have hc2 : Restated.Vocabulary.Protocol.PoolCarry M (w' v).st.core (w₂ v).st.core := by
        rcases step_cases₂ S ρ n w' w₂ hw₂' with ⟨-, rfl⟩ | ⟨e, hev, hstep⟩
        · exact ⟨fun _ _ h => h, fun _ _ h => h⟩
        · refine (step_pool₂ facts S v hproc (htickstep v) w' w₂ e hstep ?_
            (poolStamps_core₂ facts S hsorted hin hinit hproc htickstep v n w' hw'mem)).1
          intro t he
          subst he
          exact Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_clock_le_event facts S ρ
            hsorted hev (hin _ (List.mem_of_getElem? hev)).1 v w' hw'mem
      exact ⟨fun k u hu => hc2.mem k u (hc1.mem k u hu),
        fun u c hc => hc2.stamp u c (hc1.stamp u c hc)⟩
    · have hmn : m = n + 1 := Nat.le_antisymm hle hge
      subst hmn
      rw [Nat.sub_self, List.take_zero] at hw₂
      obtain rfl := Set.mem_singleton_iff.mp hw₂
      exact ⟨fun _ _ h => h, fun _ _ h => h⟩

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedRuntime
open Execution

/-- In a run sorted by key in which a tick event sits at one index only, if the `i`-th event is
    `v`'s tick at `t`, then for every world `w₁` strictly before `t` and every world `w₂` the events
    `n_t` to `i - 1` lead to from `w₁`, `v`'s node state in `w₂` is the one in `w₁` or its wake
    `M.wake (w₁ v)`, where `n_t` is the number of events with a time before `t`. -/
theorem Vocabulary.Proofs.NamedRuntime.tick_prefix_eq_strict_of_fields (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (huniq : Restated.TickIndexUnique rho) {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t)) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t,
    ∀ w₂ ∈ ((rho.events.drop (rho.events.filter (fun e => decide (e.time < t))).length).take
        (i - (rho.events.filter (fun e => decide (e.time < t))).length)).foldlM
        (Record.worldStepOf M S) w₁,
    w₂ v = w₁ v ∨ w₂ v = M.wake (w₁ v) := by
  intro w₁ _ w₂ hw₂
  obtain ⟨-, hne⟩ := tick_index_facts₂ rho hsorted huniq hi
  refine foldlM_eq_or_wake_of_ne_or_wake₂ facts S v _ w₁ ?_ w₂ hw₂
  intro e he
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp he
  by_cases hkn : k < i - (rho.events.filter (fun e => decide (e.time < t))).length
  · rw [List.getElem?_take_of_lt hkn, List.getElem?_drop] at hk
    rcases hne (_ + k) e (by omega) (by omega) hk with h | h
    · exact Or.inl h
    · exact Or.inr ⟨t, h⟩
  · rw [List.getElem?_eq_none_iff.mpr (by simp; omega)] at hk
    cases hk

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedCacheProvenance
open Execution DecoupledConsensusModel.Protocol

/-- In a run sorted by key in which a tick event sits at one index only, for every world `w₁` before
    event `i`, if the cache of `v`'s node state in `w₁` has the completed result `root` for round
    `r` and phase `p`, then `r = 0` and `root` is empty, or some event `j < i` is `v`'s tick at the
    phase's domain instant `t`, and some world `w` strictly before `t`, from which the events `n_t`
    to `i - 1` lead to `w₁`, has `root` as every frozen root `v`'s store in `w` can compute, clipped
    to the finalized block of `v`'s store in `w₁`. Here `n_t` is the number of events with a time
    before `t`. -/
theorem Vocabulary.Proofs.NamedCacheProvenance.completed_phase_origin_strict_of_fields (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (huniq : Restated.TickIndexUnique rho)
    (i : Nat) (v : V) (r : Round) (p : Phase) (root : Option (Block V)) :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    M.phaseResult (M.cacheAtRound (w₁ v).cache r) p = some root →
    (r = 0 ∧ root = none) ∨ ∃ (j : Nat) (t : Time),
      j < i ∧ rho.events[j]? = some (.tick v t) ∧ t = M.domain S.E S.hc r p ∧
      ∃ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t,
      w₁ ∈ ((rho.events.drop (rho.events.filter (fun e => decide (e.time < t))).length).take
        (i - (rho.events.filter (fun e => decide (e.time < t))).length)).foldlM
        (Record.worldStepOf M S) w ∧
      ∀ fr, M.freezeRoot S.E
        (M.gradeView (M.toHealing (w v).st.core))
        (w v).st.core.F S.hc.η_SG r
        (M.early S.E S.hc r p) (M.late S.E S.hc r p) ⇢ fr →
      root = fr.map (fun B => M.clipGrade B (w₁ v).st.core.F) := by
  intro w₁ hw₁ h
  rcases Restated.Vocabulary.Proofs.NamedCacheProvenance.completed_phase_origin facts S rho i v r p
      root w₁ hw₁ h with hzero | ⟨j, t, hj, he, ht, w, hw, hw₁', hr⟩
  · exact Or.inl hzero
  · refine Or.inr ⟨j, t, hj, he, ht, ?_⟩
    obtain ⟨hnj, hne⟩ := tick_index_facts₂ rho hsorted huniq he
    obtain ⟨w', hw', hww'⟩ := (mem_stateBeforeOf_split₂ S rho hnj w).mp hw
    have hvv : (w v).st = (w' v).st :=
      slice_st_of_ne_or_wake₂ facts S rho v
        (fun j' e a b c => (hne j' e a b c).imp id (fun h => ⟨t, h⟩)) w' w hww'
    refine ⟨w', by rw [stateBeforeTime_eq₂ S rho hsorted t]; exact hw', ?_, ?_⟩
    · exact (mem_slice_split₂ S rho hnj hj.le w' w₁).mpr ⟨w, hww', hw₁'⟩
    · rw [← hvv]
      exact hr

/-- In a run sorted by key in which a tick event sits at one index only, for every world `w₁`
    strictly before `read`, if the cache of `v`'s node state in `w₁` has the completed result `root`
    for round `r` and phase `p`, then `r = 0` and `root` is empty, or some event is `v`'s tick at a
    time `t < read` that is the phase's domain instant, and some world `w` strictly before `t`, from
    which the events `n_t` to `n_read - 1` lead to `w₁`, has `root` as every frozen root `v`'s store
    in `w` can compute, clipped to the finalized block of `v`'s store in `w₁`. Here `n_t` and
    `n_read` count the events with a time before `t` and before `read`. -/
theorem Vocabulary.Proofs.NamedCacheProvenance.completed_phase_before_read_of_fields (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (huniq : Restated.TickIndexUnique rho)
    (read : Time) (v : V) (r : Round) (p : Phase) (root : Option (Block V)) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho read,
    M.phaseResult (M.cacheAtRound (w₁ v).cache r) p = some root →
    (r = 0 ∧ root = none) ∨ ∃ (j : Nat) (t : Time),
      rho.events[j]? = some (.tick v t) ∧ t < read ∧ t = M.domain S.E S.hc r p ∧
      ∃ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t,
      w₁ ∈ ((rho.events.drop (rho.events.filter (fun e => decide (e.time < t))).length).take
        ((rho.events.filter (fun e => decide (e.time < read))).length -
          (rho.events.filter (fun e => decide (e.time < t))).length)).foldlM
        (Record.worldStepOf M S) w ∧
      ∀ fr, M.freezeRoot S.E
        (M.gradeView (M.toHealing (w v).st.core))
        (w v).st.core.F S.hc.η_SG r
        (M.early S.E S.hc r p) (M.late S.E S.hc r p) ⇢ fr →
      root = fr.map (fun B => M.clipGrade B (w₁ v).st.core.F) := by
  intro w₁ hw₁ h
  rw [stateBeforeTime_eq₂ S rho hsorted read] at hw₁
  rcases Restated.Vocabulary.Proofs.NamedCacheProvenance.completed_phase_origin_strict_of_fields
      facts S rho hsorted huniq _ v r p root w₁ hw₁ h with hzero | ⟨j, t, hj, he, ht, hrest⟩
  · exact Or.inl hzero
  · exact Or.inr ⟨j, t, he, time_lt_of_lt_filter₂ rho hsorted read hj he, ht, hrest⟩

end

section
open DecoupledConsensusModel.Protocol
open Internal
open Execution

/-- In a run sorted by key and inside its horizon, the clock of any validator's store in every world
    before the event at index `n` is at most the time of that event. -/
theorem Vocabulary.Protocol.store_time_le_event_time_of_fields (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V}
    (hsorted : ρ.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (hin : ∀ e ∈ ρ.events, 0 ≤ e.time ∧ e.time ≤ ρ.horizon)
    {n : Nat} {e : Record.Event V} (he : ρ.events[n]? = some e) (v : V) : ∀ w₁ ∈ Record.stateBeforeOf M S ρ n,
    ((w₁ v)).st.t ≤ e.time :=
  Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_clock_le_event facts S ρ hsorted he
    (hin e (List.mem_of_getElem? he)).1 v

/-- In a run sorted by key and inside its horizon, `v`'s store in every world before every event
    satisfies the pool-stamp conditions. -/
theorem Vocabulary.Protocol.poolStamps_stateBefore_of_fields (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V}
    (hsorted : ρ.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (hin : ∀ e ∈ ρ.events, 0 ≤ e.time ∧ e.time ≤ ρ.horizon)
    (v : V) : ∀ n : Nat, ∀ w₁ ∈ Record.stateBeforeOf M S ρ n,
      Restated.Vocabulary.Protocol.PoolStamps M (w₁ v).st.core :=
  poolStamps_core₂ facts S hsorted hin facts.hd.poolStamps_initial (facts.ndRun.poolStep_process S)
    (fun u n t out hout hle => (facts.ndRun.voteInsertStep_onTickEmit S u n t out hout hle).poolStep)
    v

/-- In a run sorted by key and inside its horizon, for every world `w₁` before event `m` and every
    world `w₂` the events `m` to `n - 1` lead to from `w₁`, with `m ≤ n`, a vote in `v`'s pool in
    `w₁` is in `v`'s pool in `w₂`, with the stamp it was first given. -/
theorem Vocabulary.Protocol.pool_carry_of_fields (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V}
    (hsorted : ρ.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (hin : ∀ e ∈ ρ.events, 0 ≤ e.time ∧ e.time ≤ ρ.horizon) (v : V)
    {m : Nat} : ∀ w₁ ∈ Record.stateBeforeOf M S ρ m, ∀ n : Nat, m ≤ n →
      ∀ w₂ ∈ ((ρ.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) w₁,
      Restated.Vocabulary.Protocol.PoolCarry M (w₁ v).st.core (w₂ v).st.core :=
  pool_carry_core₂ facts S hsorted hin facts.hd.poolStamps_initial (facts.ndRun.poolStep_process S)
    (fun u n t out hout hle => (facts.ndRun.voteInsertStep_onTickEmit S u n t out hout hle).poolStep)
    v

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open Internal
open Execution

/-- In a run sorted by key, the worlds strictly before `t` are the worlds reached by the events
    before `t`, which are a prefix of the run. -/
theorem Vocabulary.Proofs.Optimistic.stateBeforeTime_eq_take_of_sorted (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V}
    (hsorted : ρ.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (t : Time) :
    Restated.Vocabulary.Execution.Run.stateBeforeTime M S ρ t =
      (Record.stateBeforeOf M S ρ (ρ.events.filter (fun e => decide (e.time < t))).length) :=
  stateBeforeTime_eq₂ S ρ hsorted t

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedRawRelay
open Execution DecoupledConsensusModel.Protocol

/-- In a run sorted by key and inside its horizon, along a path `W` on which every tick event has an
    outcome from the node state the path holds before it (`hto`), a tick of the reader at `p` before
    a delivery to it at `td ≥ p` is at most the clock of the reader's store in `W i`, the path's
    world before that delivery. -/
theorem Vocabulary.Proofs.NamedRawRelay.tick_le_clock_before_delivery_of_fields (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (hin : ∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hto : ∀ (i : Nat) (u : V) (t : Int), rho.events[i]? = some (Record.Event.tick u t) →
      ∃ out, M.tick S u (W i u) t ⇢ out)
    {i : Nat} {reader : V} {o : NamedObject V} {td p : Time}
    (he : rho.events[i]? = some (.deliver reader o td))
    (hp : Record.Event.tick reader p ∈ rho.events) (hpt : p ≤ td) :
    p ≤ (W i reader).st.core.t := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hp
  have hji : j < i := by
    by_contra hn
    have hij : i ≤ j := Nat.le_of_not_gt hn
    have hne : i ≠ j := by
      intro h
      subst j
      rw [he] at hj
      cases hj
    obtain ⟨hiLen, hiGet⟩ := List.getElem?_eq_some_iff.mp he
    obtain ⟨hjLen, hjGet⟩ := List.getElem?_eq_some_iff.mp hj
    have hkey := (List.pairwise_iff_getElem.mp hsorted) i j hiLen hjLen (lt_of_le_of_ne hij hne)
    rw [hiGet, hjGet] at hkey
    have hbad : ¬ Record.Event.key (Record.Event.deliver reader o td) ≤
        Record.Event.key (Record.Event.tick reader p) := by
      simp only [Record.Event.key, Record.Event.time, Record.Event.phase, Prod.Lex.le_iff]
      rintro (hlt | ⟨_, hphase⟩)
      · exact (not_lt_of_ge hpt) hlt
      · norm_num at hphase
    exact hbad hkey
  exact Restated.Vocabulary.Proofs.NamedRuntime.tick_time_le_clock facts S rho hsorted
    (fun e he => (hin e he).1) W hW hto hj hji

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open Internal
open Execution

/-- In a run in which a tick event sits at one index only, along a path `W` of the run on which
    every node state of `v` is one a run reaches and runs as `v`, `v` emits at most one Goldfish
    vote per slot. -/
theorem Vocabulary.Proofs.Optimistic.emits_gfVote_unique_of_fields (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V}
    (huniq : Restated.TickIndexUnique ρ) (W : Nat → V → M.N)
    {v : V} {u₁ u₂ : GoldfishVote V} {t₁ t₂ : Time}
    (h₁ : (Restated.Vocabulary.Execution.Run.emits M S ρ W v (Object.gfVote u₁) t₁))
    (h₂ : (Restated.Vocabulary.Execution.Run.emits M S ρ W v (Object.gfVote u₂) t₂))
    (hslot : u₁.slot = u₂.slot) (hn : ∀ i, M.reachedNode (W i v)) (hv : ∀ i, M.runs_as (W i v) v) :
    u₁ = u₂ := by
  obtain ⟨-, ht₁, -, hu₁⟩ := Restated.Vocabulary.Proofs.Optimistic.emits_gfVote_shape facts S W h₁ hn hv
  obtain ⟨-, ht₂, -, hu₂⟩ := Restated.Vocabulary.Proofs.Optimistic.emits_gfVote_shape facts S W h₂ hn hv
  have hteq : t₁ = t₂ := by
    rw [ht₁, ht₂, ← hu₁, ← hu₂, hslot]
  subst hteq
  obtain ⟨i₁, hi₁, out₁, hout₁, -, ho₁⟩ := h₁
  obtain ⟨i₂, hi₂, out₂, hout₂, -, ho₂⟩ := h₂
  obtain ⟨hb₁, he₁⟩ := List.getElem?_eq_some_iff.mp hi₁
  obtain ⟨hb₂, he₂⟩ := List.getElem?_eq_some_iff.mp hi₂
  have hidx : i₁ = i₂ := huniq he₁ (by rw [he₁, he₂])
  subst hidx
  have _hr := hn i₁
  have _hv := hv i₁
  obtain ⟨-, -, hd₁, -, -⟩ :=
    Restated.Vocabulary.Proofs.Optimistic.gfVote_emitted_shape facts S v (W i₁ v) t₁ out₁ hout₁ ho₁
  obtain ⟨-, -, hd₂, -, -⟩ :=
    Restated.Vocabulary.Proofs.Optimistic.gfVote_emitted_shape facts S v (W i₁ v) t₁ out₂ hout₂ ho₂
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W i₁ v).st.core.toHealing t₁
    (W i₁ v).cache
  obtain ⟨D, hD⟩ := facts.dt.goldfish_vote_with_nonempty (M.frameContract c) S.E S.hc (S.node v)
    (M.ns_setClock S.E (W i₁ v).st t₁)
  have e₁ := hd₁ c hc D hD
  rw [hd₂ c hc D hD] at e₁
  exact (Option.some_inj.mp e₁).symm

end

end DecoupledConsensusModel.Sts.Restated
