import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Projection
import Model.Conditions.RunAll
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Record.Wiring
import Proofs.Claims.RunAll

/-!
# The events of an sts execution and the path of its run

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M` about the events
each step of an sts execution contributes and the run they form: where each event comes from,
folding events into worlds, real time along the execution, the sent log after tick and delivery
steps, and `runAllPath`, the path of the run that the execution itself follows, with the tick
outcomes and emissions along it.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-! ## One step's events -/

/-- If `tick v₁ t'` is among `v₀`'s events of one step with label `a`, then `a` is `tickAllAwake τ`
    with `τ = t'`, `v₁` is awake and not adversarial at `τ`, and `τ` is a whole multiple of `S.E.Δ`. -/
theorem tickAllAwake_of_mem_actionEventsOf {S : Setup V} {Sched : Schedule V} {v₀ v₁ : V}
    {t t' : Int} {a : AtomicAction V (NamedObject V) Empty}
    (he : (Record.Event.tick v₁ t' : Record.Event V) ∈ Record.actionEventsOf M S Sched v₀ t a) :
    ∃ τ : Nat, a = AtomicAction.tickAllAwake τ ∧ (τ : Int) = t' ∧
      v₁ ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) ∧ (τ : Int) % S.E.Δ = 0 := by
  cases a with
  | tickAllAwake τ =>
      simp only [Record.actionEventsOf, List.mem_append] at he
      rcases he with he | he
      · split at he
        · simp at he
        · simp at he
      · split at he
        · next h =>
          rw [List.mem_singleton] at he
          injection he with h1 h2
          subst h1
          exact ⟨τ, rfl, h2.symm, h.1, h.2⟩
        · simp at he
  | deliver p m =>
      simp only [Record.actionEventsOf] at he
      split at he <;> simp at he
  | custom _ ev => exact ev.elim
  | adversarial p m => simp [Record.actionEventsOf] at he
  | forward p m => simp [Record.actionEventsOf] at he

/-- If `deliver v₁ o t'` is among `v₀`'s events of one step with label `a` at time `t`, then `a`
    delivers to `v₁` some message `m` whose payload is `o`, and `t' = t`. -/
theorem deliver_of_mem_actionEventsOf {S : Setup V} {Sched : Schedule V} {v₀ v₁ : V}
    {o : NamedObject V} {t t' : Int} {a : AtomicAction V (NamedObject V) Empty}
    (he : (Record.Event.deliver v₁ o t' : Record.Event V) ∈ Record.actionEventsOf M S Sched v₀ t a) :
    ∃ m : SignedMsg V (NamedObject V), a = AtomicAction.deliver v₁ m ∧ m.msg = o ∧ t' = t := by
  rcases Record.mem_actionEventsOf_cases he with ⟨τ, -, h | h⟩ | ⟨p, m, hl, hp, h⟩
  · cases h
  · cases h
  · injection h with h1 h2 h3
    exact ⟨m, by rw [hl, hp, h1], h2.symm, h3⟩

/-- If `wake v₁ t'` is among `v₀`'s events of one step with label `a`, then `a` is `tickAllAwake τ`
    with `τ = t'`, `v₁` is `v₀`, the model records its wakes, and `v₁` enters the awake set at `τ`. -/
theorem wake_of_mem_actionEventsOf {S : Setup V} {Sched : Schedule V} {v₀ v₁ : V}
    {t t' : Int} {a : AtomicAction V (NamedObject V) Empty}
    (he : (Record.Event.wake v₁ t' : Record.Event V) ∈ Record.actionEventsOf M S Sched v₀ t a) :
    ∃ τ : Nat, a = AtomicAction.tickAllAwake τ ∧ (τ : Int) = t' ∧ v₁ = v₀ ∧
      M.wakeEvents = true ∧ v₁ ∈ entrants Sched τ := by
  cases a with
  | tickAllAwake τ =>
      simp only [Record.actionEventsOf, List.mem_append] at he
      rcases he with he | he
      · split at he
        · next h =>
          rw [List.mem_singleton] at he
          injection he with h1 h2
          subst h1
          exact ⟨τ, rfl, h2.symm, rfl, h.1, h.2⟩
        · simp at he
      · split at he
        · simp at he
        · simp at he
  | deliver p m =>
      simp only [Record.actionEventsOf] at he
      split at he <;> simp at he
  | custom _ ev => exact ev.elim
  | adversarial p m => simp [Record.actionEventsOf] at he
  | forward p m => simp [Record.actionEventsOf] at he

/-- The events `u` contributes at one step are none, exactly one, or, at a `tickAllAwake t` step,
    the wake of `u` at `t` followed by the tick of `u` at `t`. -/
theorem actionEventsOf_cases (S : Setup V) (Sched : Schedule V) (u : V) (now : Int)
    (a : AtomicAction V (NamedObject V) Empty) :
    Record.actionEventsOf M S Sched u now a = [] ∨
      (∃ e, Record.actionEventsOf M S Sched u now a = [e]) ∨
      ∃ t : Nat, a = AtomicAction.tickAllAwake t ∧
        Record.actionEventsOf M S Sched u now a
          = [Record.Event.wake u (t : Int), Record.Event.tick u (t : Int)] := by
  cases a with
  | tickAllAwake t =>
      simp only [Record.actionEventsOf]
      split_ifs
      · exact Or.inr (Or.inr ⟨t, rfl, rfl⟩)
      · exact Or.inr (Or.inl ⟨_, rfl⟩)
      · exact Or.inr (Or.inl ⟨_, rfl⟩)
      · exact Or.inl rfl
  | deliver p m =>
      simp only [Record.actionEventsOf]
      split_ifs
      · exact Or.inr (Or.inl ⟨_, rfl⟩)
      · exact Or.inl rfl
  | custom _ ev => exact ev.elim
  | adversarial _ _ => exact Or.inl rfl
  | forward _ _ => exact Or.inl rfl

/-- Over a list of validators without repetitions that contains `v₀`, keeping `v₀`'s events out of
    every validator's events of one step gives `v₀`'s own. -/
private theorem filter_flatMap_actionEventsOf (S : Setup V) (Sched : Schedule V) (now : Int)
    (a : AtomicAction V (NamedObject V) Empty) {v₀ : V} :
    ∀ l : List V, l.Nodup → v₀ ∈ l →
      (l.flatMap (fun v₁ => Record.actionEventsOf M S Sched v₁ now a)).filter
        (fun e => decide (Record.Event.node e = v₀)) = Record.actionEventsOf M S Sched v₀ now a
  | [], _, hv => absurd hv List.not_mem_nil
  | v₁ :: l, hnd, hv => by
      rw [List.flatMap_cons, List.filter_append]
      by_cases h : v₁ = v₀
      · subst h
        have hself : (Record.actionEventsOf M S Sched v₁ now a).filter
            (fun e => decide (Record.Event.node e = v₁)) = Record.actionEventsOf M S Sched v₁ now a :=
          List.filter_eq_self.2 (fun e he => by simp [Record.node_of_mem_actionEventsOf he])
        have hrest : (l.flatMap (fun v₂ => Record.actionEventsOf M S Sched v₂ now a)).filter
            (fun e => decide (Record.Event.node e = v₁)) = [] := by
          refine List.filter_eq_nil_iff.2 (fun e he => ?_)
          obtain ⟨v₂, hv₂, he'⟩ := List.mem_flatMap.1 he
          rw [Record.node_of_mem_actionEventsOf he']
          intro h2
          have h2' : v₂ = v₁ := of_decide_eq_true h2
          subst h2'
          exact (List.nodup_cons.1 hnd).1 hv₂
        rw [hself, hrest, List.append_nil]
      · have hnil : (Record.actionEventsOf M S Sched v₁ now a).filter
            (fun e => decide (Record.Event.node e = v₀)) = [] :=
          List.filter_eq_nil_iff.2 (fun e he => by simp [Record.node_of_mem_actionEventsOf he, h])
        rw [hnil, List.nil_append]
        exact filter_flatMap_actionEventsOf S Sched now a l (List.nodup_cons.1 hnd).2
          ((List.mem_cons.1 hv).resolve_left (fun hh => h hh.symm))

/-- The events of step `k`, filtered at `v₀`, are `v₀`'s own events of that step. -/
theorem filter_stepEvents (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v₀ : V) (k : Nat) :
    (Restated.stepEvents M S Sched x k).filter (fun e => decide (Record.Event.node e = v₀))
      = Record.actionEventsOf M S Sched v₀ (x[k].time : Int) (x.lbl k) :=
  filter_flatMap_actionEventsOf S Sched _ _ _ (Finset.nodup_toList _)
    (Finset.mem_toList.2 (Finset.mem_univ v₀))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The events of the run over the first `n` steps, filtered at `v₀`, are `v₀`'s own events of those
    steps. -/
theorem filter_runEvents (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v₀ : V) (n : Nat) :
    (Restated.runEvents M S Sched x n).filter (fun e => decide (Record.Event.node e = v₀))
      = Record.veventsOf M S Sched x v₀ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show Restated.runEvents M S Sched x (n + 1)
            = Restated.runEvents M S Sched x n ++ Restated.stepEvents M S Sched x n from rfl,
        List.filter_append, ih, Restated.filter_stepEvents facts]
      rfl

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open scoped DC

/-- For every world `w` and event `e`, some world is among the worlds `e` can lead to from `w`. -/
private theorem worldStepOf_nonempty (M : Record.Model V) (S : Setup V) (w : V → M.N)
    (e : Record.Event V) : ∃ u, u ∈ Record.worldStepOf M S w e := by
  classical
  cases e with
  | wake v₁ t => exact ⟨_, Set.mem_singleton _⟩
  | tick v₁ t =>
      by_cases hex : ∃ out : M.N × List (NamedObject V), M.tick S v₁ (w v₁) t ⇢ out
      · obtain ⟨out, hout⟩ := hex
        exact ⟨Function.update w v₁ out.1, Or.inl ⟨out, hout, rfl⟩⟩
      · exact ⟨w, Or.inr ⟨fun out hout => hex ⟨out, hout⟩, rfl⟩⟩
  | deliver v₁ o t =>
      by_cases hex : ∃ n' : M.N, M.process S (w v₁) o ⇢ n'
      · obtain ⟨n', hn'⟩ := hex
        exact ⟨Function.update w v₁ n', Or.inl ⟨n', hn', rfl⟩⟩
      · exact ⟨w, Or.inr ⟨fun n' hn' => hex ⟨n', hn'⟩, rfl⟩⟩

/-- If the event `e` is not `v₀`'s, every world `e` can lead to from `w` holds at `v₀` what `w`
    holds there. -/
private theorem worldStepOf_at_other {M : Record.Model V} (S : Setup V) {v₀ : V}
    {w u : V → M.N} {e : Record.Event V} (hn : ¬ Record.Event.node e = v₀)
    (hu : u ∈ Record.worldStepOf M S w e) : u v₀ = w v₀ := by
  cases e with
  | wake v₁ t =>
      have hne : v₀ ≠ v₁ := fun hh => hn hh.symm
      rw [Set.mem_singleton_iff.1 hu]
      exact Function.update_of_ne hne _ _
  | tick v₁ t =>
      have hne : v₀ ≠ v₁ := fun hh => hn hh.symm
      rcases hu with ⟨out, -, rfl⟩ | ⟨-, rfl⟩
      · exact Function.update_of_ne hne _ _
      · rfl
  | deliver v₁ o t =>
      have hne : v₀ ≠ v₁ := fun hh => hn hh.symm
      rcases hu with ⟨n', -, rfl⟩ | ⟨-, rfl⟩
      · exact Function.update_of_ne hne _ _
      · rfl

/-- If the event `e` is `v₀`'s and `w`, `w'` agree at `v₀`, then for every world `u` that `e` can
    lead to from `w`, some world `e` can lead to from `w'` agrees with `u` at `v₀`. -/
private theorem worldStepOf_at_self {M : Record.Model V} (S : Setup V) {v₀ : V}
    {w w' u : V → M.N} {e : Record.Event V} (hn : Record.Event.node e = v₀) (h : w v₀ = w' v₀)
    (hu : u ∈ Record.worldStepOf M S w e) :
    ∃ u' ∈ Record.worldStepOf M S w' e, u' v₀ = u v₀ := by
  cases e with
  | wake v₁ t =>
      have hv : v₁ = v₀ := hn
      subst hv
      rw [Set.mem_singleton_iff.1 hu]
      refine ⟨Function.update w' v₁ (M.wake (w' v₁)), Set.mem_singleton _, ?_⟩
      simp only [Function.update_self, h]
  | tick v₁ t =>
      have hv : v₁ = v₀ := hn
      subst hv
      rcases hu with ⟨out, hout, rfl⟩ | ⟨hno, rfl⟩
      · refine ⟨Function.update w' v₁ out.1, Or.inl ⟨out, by rw [← h]; exact hout, rfl⟩, ?_⟩
        simp only [Function.update_self]
      · exact ⟨w', Or.inr ⟨by rw [← h]; exact hno, rfl⟩, h.symm⟩
  | deliver v₁ o t =>
      have hv : v₁ = v₀ := hn
      subst hv
      rcases hu with ⟨n', hn', rfl⟩ | ⟨hno, rfl⟩
      · refine ⟨Function.update w' v₁ n', Or.inl ⟨n', by rw [← h]; exact hn', rfl⟩, ?_⟩
        simp only [Function.update_self]
      · exact ⟨w', Or.inr ⟨by rw [← h]; exact hno, rfl⟩, h.symm⟩

/-- When `w` and `w'` agree at `v₀`, the values `v₀` can hold after folding `es` from `w` are
    exactly those it can hold after folding only `v₀`'s events of `es` from `w'`. -/
theorem foldl_step_apply (facts : Record.Facts M) (S : Setup V) (v₀ : V) :
    ∀ (es : List (Record.Event V)) (w w' : (V → M.N)), w v₀ = w' v₀ →
      (fun u => u v₀) '' (es.foldlM (Record.worldStepOf M S) w)
        = (fun u => u v₀) '' ((es.filter (fun e => decide (Record.Event.node e = v₀))).foldlM
            (Record.worldStepOf M S) w')
  | [], w, w', h => by
      simp only [List.filter_nil, List.foldlM_nil, Set.pure_def, Set.image_singleton, h]
  | e :: es, w, w', h => by
      by_cases hn : Record.Event.node e = v₀
      · rw [List.filter_cons_of_pos (by simp [hn]), List.foldlM_cons, List.foldlM_cons,
          Set.bind_def, Set.bind_def, Set.image_iUnion₂, Set.image_iUnion₂]
        ext y
        simp only [Set.mem_iUnion, exists_prop]
        constructor
        · rintro ⟨u, hu, hy⟩
          obtain ⟨u', hu', huv⟩ := worldStepOf_at_self S hn h hu
          refine ⟨u', hu', ?_⟩
          rw [← foldl_step_apply facts S v₀ es u u' huv.symm]
          exact hy
        · rintro ⟨u', hu', hy⟩
          obtain ⟨u, hu, huv⟩ := worldStepOf_at_self S hn h.symm hu'
          refine ⟨u, hu, ?_⟩
          rw [foldl_step_apply facts S v₀ es u u' huv]
          exact hy
      · rw [List.filter_cons_of_neg (by simp [hn]), List.foldlM_cons, Set.bind_def,
          Set.image_iUnion₂]
        ext y
        simp only [Set.mem_iUnion, exists_prop]
        constructor
        · rintro ⟨u, hu, hy⟩
          rw [foldl_step_apply facts S v₀ es u w'
            ((worldStepOf_at_other S hn hu).trans h)] at hy
          exact hy
        · intro hy
          obtain ⟨u, hu⟩ := worldStepOf_nonempty M S w e
          refine ⟨u, hu, ?_⟩
          rw [foldl_step_apply facts S v₀ es u w' ((worldStepOf_at_other S hn hu).trans h)]
          exact hy

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The values `v₀` can hold after folding `es` from the initial world are exactly those it can hold
    after folding only `v₀`'s events of `es` from it. -/
theorem foldl_step_apply_init (facts : Record.Facts M) (S : Setup V) (v₀ : V) (es : List (Record.Event V)) :
    (fun u => u v₀) '' (es.foldlM (Record.worldStepOf M S) (fun v' => M.initial S v'))
      = (fun u => u v₀) '' ((es.filter (fun e => decide (Record.Event.node e = v₀))).foldlM
          (Record.worldStepOf M S) (fun v' => M.initial S v')) :=
  Restated.foldl_step_apply facts S v₀ es _ _ rfl

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For `i ≤ n`, the run over the first `i` steps is a prefix of the run over the first `n` steps. -/
theorem runEvents_append (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {i n : Nat} (h : i ≤ n) :
    ∃ l : List (Record.Event V), Restated.runEvents M S Sched x n = Restated.runEvents M S Sched x i ++ l := by
  induction n, h using Nat.le_induction with
  | base => exact ⟨[], (List.append_nil _).symm⟩
  | succ n h ih =>
      obtain ⟨l, hl⟩ := ih
      exact ⟨l ++ Restated.stepEvents M S Sched x n, by
        rw [show Restated.runEvents M S Sched x (n + 1)
              = Restated.runEvents M S Sched x n ++ Restated.stepEvents M S Sched x n from rfl, hl,
          List.append_assoc]⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For `i ≤ n`, cutting the run over the first `n` steps at the length of the run over the first
    `i` steps gives the latter. -/
theorem take_runEvents (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {i n : Nat} (h : i ≤ n) :
    (Restated.runEvents M S Sched x n).take (Restated.runEvents M S Sched x i).length = Restated.runEvents M S Sched x i := by
  obtain ⟨l, hl⟩ := Restated.runEvents_append facts S Sched x h
  rw [hl, List.take_left]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The events of one step are pairwise distinct. -/
theorem stepEvents_nodup (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (k : Nat) :
    (Restated.stepEvents M S Sched x k).Nodup := by
  rw [Restated.stepEvents, List.nodup_flatMap]
  refine ⟨fun v₁ _ => ?_, (Finset.nodup_toList _).imp (fun {a b} hab => ?_)⟩
  · rcases actionEventsOf_cases S Sched v₁ (x[k].time : Int) (x.lbl k) with h | ⟨e, h⟩ | ⟨t, -, h⟩
    · rw [h]; exact List.nodup_nil
    · rw [h]; exact List.nodup_singleton e
    · rw [h]; simp
  · intro z hza hzb
    exact hab ((Record.node_of_mem_actionEventsOf hza).symm.trans
      (Record.node_of_mem_actionEventsOf hzb))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- An event a validator contributes at step `k` is an event of that step. -/
theorem mem_stepEvents_of_mem_actionEvents (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (k : Nat) {v₀ : V} {e : Record.Event V}
    (he : e ∈ Record.actionEventsOf M S Sched v₀ (x[k].time : Int) (x.lbl k)) :
    e ∈ Restated.stepEvents M S Sched x k :=
  List.mem_flatMap.2 ⟨v₀, Finset.mem_toList.2 (Finset.mem_univ v₀), he⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- An event a validator contributes at a step before `n` is an event of the run over the first `n`
    steps. -/
theorem mem_runEvents_of_mem_actionEvents (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) :
    ∀ (n k : Nat), k < n → ∀ (v₀ : V) (e : Record.Event V),
      e ∈ Record.actionEventsOf M S Sched v₀ (x[k].time : Int) (x.lbl k) → e ∈ Restated.runEvents M S Sched x n
  | 0, k, hk, _, _, _ => absurd hk (Nat.not_lt_zero k)
  | n + 1, k, hk, v₀, e, he => by
      rw [show Restated.runEvents M S Sched x (n + 1)
            = Restated.runEvents M S Sched x n ++ Restated.stepEvents M S Sched x n from rfl]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
      · exact List.mem_append_left _
          (mem_runEvents_of_mem_actionEvents facts S Sched x n k h v₀ e he)
      · subst h
        exact List.mem_append_right _ (Restated.mem_stepEvents_of_mem_actionEvents facts S Sched x k he)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every event of the run over the first `n` steps was contributed by its own validator at some
    step before `n`. -/
theorem exists_step_of_mem_runEvents (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) :
    ∀ (n : Nat) {e : Record.Event V}, e ∈ Restated.runEvents M S Sched x n →
      ∃ k < n, e ∈ Record.actionEventsOf M S Sched (Record.Event.node e) (x[k].time : Int) (x.lbl k)
  | 0, e, he => absurd he (by
      rw [show Restated.runEvents M S Sched x 0 = [] from rfl]; exact List.not_mem_nil)
  | n + 1, e, he => by
      rw [show Restated.runEvents M S Sched x (n + 1)
            = Restated.runEvents M S Sched x n ++ Restated.stepEvents M S Sched x n from rfl,
        List.mem_append] at he
      rcases he with he | he
      · obtain ⟨k, hk, hmem⟩ := exists_step_of_mem_runEvents facts S Sched x n he
        exact ⟨k, Nat.lt_succ_of_lt hk, hmem⟩
      · obtain ⟨v₀, -, hmem⟩ := List.mem_flatMap.1 he
        have hnode := Record.node_of_mem_actionEventsOf hmem
        exact ⟨n, Nat.lt_succ_self n, by rw [hnode]; exact hmem⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `l[m]` is `e` and `p e` holds, filtering `l` by `p` gives the filtered entries before index
    `m`, then `e`, then the filtered entries after `m`. -/
private theorem filter_take_cons_drop {l : List (Record.Event V)} {m : Nat} {e : Record.Event V}
    (he : l[m]? = some e) (p : Record.Event V → Bool) (hp : p e = true) :
    (l.take m).filter p ++ e :: (l.drop (m + 1)).filter p = l.filter p := by
  obtain ⟨hm, rfl⟩ := List.getElem?_eq_some_iff.1 he
  have hsplit : l = l.take m ++ l[m] :: l.drop (m + 1) := by
    rw [← List.drop_eq_getElem_cons hm, List.take_append_drop]
  conv_rhs => rw [hsplit]
  rw [List.filter_append, List.filter_cons_of_pos hp]

/-- An event at index `idx` of the run over the first `n` steps comes from a step `k < n`, and
    either it is the first event its validator contributes at step `k` and the run's prefix before
    it, restricted to that validator, is the validator's events of the first `k` steps; or it is the
    tick of a step at which the validator also woke, and that prefix is those events followed by the
    wake. -/
theorem filter_take_runEvents (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) :
    ∀ (n idx : Nat) {e : Record.Event V}, (Restated.runEvents M S Sched x n)[idx]? = some e →
      ∃ k < n, e ∈ Record.actionEventsOf M S Sched (Record.Event.node e) (x[k].time : Int) (x.lbl k) ∧
        ((((Restated.runEvents M S Sched x n).take idx).filter
            (fun e' => decide (Record.Event.node e' = Record.Event.node e))
          = Record.veventsOf M S Sched x (Record.Event.node e) k ∧
          ∃ post, Record.actionEventsOf M S Sched (Record.Event.node e) (x[k].time : Int) (x.lbl k)
            = e :: post) ∨
         ∃ t : Nat, Record.actionEventsOf M S Sched (Record.Event.node e) (x[k].time : Int) (x.lbl k)
             = [Record.Event.wake (Record.Event.node e) (t : Int),
                 Record.Event.tick (Record.Event.node e) (t : Int)] ∧
           e = Record.Event.tick (Record.Event.node e) (t : Int) ∧
           ((Restated.runEvents M S Sched x n).take idx).filter
               (fun e' => decide (Record.Event.node e' = Record.Event.node e))
             = Record.veventsOf M S Sched x (Record.Event.node e) k ++
                 [Record.Event.wake (Record.Event.node e) (t : Int)])
  | 0, idx, e, he => by
      rw [show Restated.runEvents M S Sched x 0 = [] from rfl] at he
      exact absurd he (by simp)
  | n + 1, idx, e, he => by
      rw [show Restated.runEvents M S Sched x (n + 1)
            = Restated.runEvents M S Sched x n ++ Restated.stepEvents M S Sched x n from rfl] at he ⊢
      by_cases hidx : idx < (Restated.runEvents M S Sched x n).length
      · rw [List.getElem?_append_left hidx] at he
        obtain ⟨k, hk, hmem, hfil⟩ := filter_take_runEvents facts S Sched x n idx he
        refine ⟨k, Nat.lt_succ_of_lt hk, hmem, ?_⟩
        rw [List.take_append_of_le_length (Nat.le_of_lt hidx)]
        exact hfil
      · have hle : (Restated.runEvents M S Sched x n).length ≤ idx := Nat.not_lt.1 hidx
        rw [List.getElem?_append_right hle] at he
        have hmem : e ∈ Record.actionEventsOf M S Sched (Record.Event.node e) (x[n].time : Int)
            (x.lbl n) := by
          obtain ⟨v₀, -, hmem⟩ := List.mem_flatMap.1
            (List.mem_of_getElem? he : e ∈ Restated.stepEvents M S Sched x n)
          have hnode := Record.node_of_mem_actionEventsOf hmem
          rw [hnode]; exact hmem
        refine ⟨n, Nat.lt_succ_self n, hmem, ?_⟩
        rw [List.take_append, List.take_of_length_le hle, List.filter_append,
          Restated.filter_runEvents facts]
        have hsplit := filter_take_cons_drop he
          (fun e' => decide (Record.Event.node e' = Record.Event.node e)) (by simp)
        rw [Restated.filter_stepEvents facts] at hsplit
        rcases actionEventsOf_cases S Sched (Record.Event.node e) (x[n].time : Int) (x.lbl n) with
          hA | ⟨e', hA⟩ | ⟨t, -, hA⟩
        · rw [hA] at hsplit; simp at hsplit
        · rw [hA] at hsplit
          refine Or.inl ?_
          cases hpre : ((Restated.stepEvents M S Sched x n).take
              (idx - (Restated.runEvents M S Sched x n).length)).filter
              (fun e' => decide (Record.Event.node e' = Record.Event.node e)) with
          | nil =>
              rw [hpre, List.nil_append, List.cons.injEq] at hsplit
              exact ⟨List.append_nil _, [], by rw [hA, hsplit.1]⟩
          | cons a l => rw [hpre] at hsplit; simp at hsplit
        · rw [hA] at hsplit
          cases hpre : ((Restated.stepEvents M S Sched x n).take
              (idx - (Restated.runEvents M S Sched x n).length)).filter
              (fun e' => decide (Record.Event.node e' = Record.Event.node e)) with
          | nil =>
              rw [hpre, List.nil_append, List.cons.injEq] at hsplit
              exact Or.inl ⟨List.append_nil _, [Record.Event.tick (Record.Event.node e) (t : Int)],
                by rw [hA, ← hsplit.1]⟩
          | cons a l =>
              rw [hpre] at hsplit
              cases l with
              | nil =>
                  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hsplit
                  obtain ⟨ha, hte, -⟩ := hsplit
                  exact Or.inr ⟨t, hA, hte, by rw [ha]⟩
              | cons b l' => simp at hsplit

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Real time never decreases: for `i ≤ n`, `x[i].time ≤ x[n].time`. -/
theorem time_mono (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {i n : Nat} (h : i ≤ n) : x[i].time ≤ x[n].time := by
  induction n, h using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ n h ih =>
      rcases atomic_time_stepwise x n with hstep | hstep <;> omega

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A `tickAllAwake t` step at index `k` has `x[k].time + 1 = t` and `x[k + 1].time = t`. -/
theorem tickAllAwake_time (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {k t : Nat}
    (hl : x.lbl k = AtomicAction.tickAllAwake t) :
    x[k].time + 1 = t ∧ x[k + 1].time = t := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  obtain ⟨hen, w, tk, -, -, hc⟩ := hs
  exact ⟨hen, by rw [hc]; rfl⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Two steps of the execution carrying the same label `tickAllAwake t` are the same step. -/
theorem tickAllAwake_step_unique (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {j k t : Nat}
    (hj : x.lbl j = AtomicAction.tickAllAwake t)
    (hk : x.lbl k = AtomicAction.tickAllAwake t) : j = k := by
  obtain ⟨hj1, hj2⟩ := Restated.tickAllAwake_time facts S Sched x hj
  obtain ⟨hk1, hk2⟩ := Restated.tickAllAwake_time facts S Sched x hk
  rcases Nat.lt_trichotomy j k with h | h | h
  · have := Restated.time_mono facts S Sched x (show j + 1 ≤ k from h)
    omega
  · exact h
  · have := Restated.time_mono facts S Sched x (show k + 1 ≤ j from h)
    omega

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The sent log of the initial configuration is empty. -/
theorem sent_zero (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) :
    x[0].sent = 0 := x.init.2.2

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A message in a validator's view after `i` steps is in the sent log `x[i].sent`. -/
theorem mem_sent_of_mem_view (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {p : V}
    {sm : SignedMsg V (NamedObject V)} {i : Nat} (h : sm ∈ x[i][p].view) :
    sm ∈ x[i].sent := by
  induction i with
  | zero =>
      obtain ⟨-, hn, -⟩ := x.init
      rw [show x[0][p] = _ from hn p] at h
      simp at h
  | succ i ih =>
      have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl i) x[i] x[i + 1] := x.step i
      refine AtomicStep.elim
        (motive := fun _ d d' =>
          (sm ∈ d[p].view → sm ∈ d.sent) → (sm ∈ d'[p].view → sm ∈ d'.sent))
        hs ?_ ?_ ?_ ?_ ?_ ih h
      · intro d t w tk _ _ _ hv hm
        have hview : (tickAllAwakeUpdate Sched t d w tk)[p].view = d[p].view := by
          by_cases hp : p ∈ Sched.awake (t : Int)
          · by_cases hadv : p ∈ Sched.adv (t : Int)
            · exact (tickAllAwakeUpdate_getElem_adv hadv).2
            · rw [tickAllAwakeUpdate_getElem_awake hp hadv]
          · rw [tickAllAwakeUpdate_getElem_asleep hp]
        rw [hview] at hm
        exact Multiset.mem_add.2 (Or.inl (hv hm))
      · intro d q m res hen _ hv hm
        have hen' : m ∈ d.sent ∧ q ∈ Sched.awake (d.time : Int) ∧
            q ∉ Sched.adv (d.time : Int) := hen
        have hsent : (applyNodeStepResult q res (receive q m d)).sent
            = d.sent + res.send.map (SignedMsg.mk q) := rfl
        rw [hsent, Multiset.mem_add]
        by_cases hpq : q = p
        · subst hpq
          have hview : (applyNodeStepResult q res (receive q m d))[q].view
              = insert m d[q].view := by
            show ((receive q m d).setNode q
              { (receive q m d)[q] with st := res.state })[q].view = _
            rw [Config.setNode_apply, if_pos rfl]
            show (receive q m d)[q].view = _
            rw [receive, Config.setNode_apply, if_pos rfl]
          rw [hview, Finset.mem_insert] at hm
          rcases hm with rfl | hm
          · exact Or.inl hen'.1
          · exact Or.inl (hv hm)
        · have hview : (applyNodeStepResult q res (receive q m d))[p] = d[p] := by
            show (if q = p then _ else (receive q m d)[p]) = _
            rw [if_neg hpq]
            show (if q = p then _ else d[p]) = _
            rw [if_neg hpq]
          rw [hview] at hm
          exact Or.inl (hv hm)
      · intro d q ev res _ _ _ _
        exact ev.elim
      · intro d q m _ hv hm
        exact Multiset.mem_cons.2 (Or.inr (hv hm))
      · intro d q m _ hv hm
        exact Multiset.mem_cons.2 (Or.inr (hv hm))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- At a `tickAllAwake t` step, if `v` reacts at `t`, `t` is a whole multiple of `S.E.Δ`, and the
    tick of `v` from the node state its wake stage leaves at `t` has an outcome, then `v`'s tick
    result is `{ state := out.1, send := out.2 }` for some outcome `out` of that tick. -/
private theorem tick_outcome_of_step {M : Record.Model V} (S : Setup V) (Sched : Schedule V)
    {t : Nat} {c : Config V (NamedObject V) M.N} {v : V}
    {w tk : V → NodeStepResult M.N (NamedObject V)}
    (hwake : ∀ p, TickAllAwakeWake (Record.protocolOf M S) Sched t c p (w p))
    (htick : ∀ p ∈ Sched.awake (t : Int) \ Sched.adv (t : Int),
      (Record.protocolOf M S).step p t c[p].view (w p).state .tick (tk p))
    (haw : v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int))
    (hdvd : (t : Int) % S.E.Δ = 0)
    (hne : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (t : Int) c v) (t : Int) ⇢ out) :
    ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (t : Int) c v) (t : Int) ⇢ out ∧
        tk v = { state := out.1, send := (out.2 : Multiset (NamedObject V)) } := by
  have hwst : (w v).state = Record.wakeStage M Sched (t : Int) c v :=
    Record.wakeStage_of_TickAllAwakeWake M S Sched (hwake v)
  have hmem : tk v ∈ Record.reactionsOf M S v ((w v).state) (t : Int) .tick := by
    rcases htick v haw with h | ⟨hempty, -⟩
    · exact h
    · exfalso
      obtain ⟨out, hout⟩ := hne
      have h' : ({ state := out.1, send := (out.2 : Multiset (NamedObject V)) } :
          NodeStepResult M.N (NamedObject V)) ∈
          Record.reactionsOf M S v ((w v).state) (t : Int) .tick := by
        simp only [Record.reactionsOf, if_pos hdvd, Set.mem_setOf_eq]
        exact ⟨out, by rw [hwst]; exact hout, rfl⟩
      rw [hempty] at h'
      exact h'
  simp only [Record.reactionsOf, if_pos hdvd, Set.mem_setOf_eq] at hmem
  obtain ⟨out, hout, htkv⟩ := hmem
  rw [hwst] at hout
  exact ⟨out, hout, htkv⟩

/-- If the tick of `v` at a tick step `k`, whose instant is a whole multiple of `S.E.Δ`, from the
    node state its wake stage leaves, has an outcome, and every outcome sends `o`, then `o`, signed
    by `v`, is in the sent log `x[k + 1].sent`. -/
theorem mem_sent_of_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {k t : Nat} {v : V} {o : NamedObject V}
    (hl : x.lbl k = AtomicAction.tickAllAwake t)
    (haw : v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int))
    (hdvd : (t : Int) % S.E.Δ = 0)
    (ho : ∀ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (t : Int) x[k] v) (t : Int) ⇢ out → o ∈ out.2)
    (hne : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (t : Int) x[k] v) (t : Int) ⇢ out) :
    (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  obtain ⟨-, w, tk, hwake, htick, hc⟩ := hs
  obtain ⟨out, hout, htkv⟩ := tick_outcome_of_step S Sched hwake htick haw hdvd hne
  have hsent : x[k + 1].sent = x[k].sent
      + (Sched.awake (t : Int) \ Sched.adv (t : Int)).sum
          (fun q => ((w q).send + (tk q).send).map (SignedMsg.mk q)) := by
    rw [hc]; rfl
  rw [hsent]
  refine Multiset.mem_add.2 (Or.inr (Multiset.mem_sum.2 ⟨v, haw, ?_⟩))
  refine Multiset.mem_map.2 ⟨o, Multiset.mem_add.2 (Or.inr ?_), rfl⟩
  rw [htkv]
  exact Multiset.mem_coe.2 (ho out hout)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- After a step that delivers `sm` to `w`, if `w`'s receipt of `sm.msg` has an outcome, the sent
    log is the one before the step plus every object of `relayedObjects sm.msg`, signed by `w`. -/
theorem sent_succ_of_deliver (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {k : Nat} {w : V}
    {sm : SignedMsg V (NamedObject V)} (hl : x.lbl k = AtomicAction.deliver w sm)
    (hne : ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[k][w].st) sm.msg ⇢ n') :
    x[k + 1].sent = x[k].sent + (relayedObjects sm.msg).map (SignedMsg.mk w) := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  obtain ⟨-, hns⟩ := hs
  have hstep : NodeStep (Record.protocolOf M S) w (.recv sm) (receive w sm x[k]) x[k + 1] := hns
  have hst : (receive w sm x[k])[w].st = x[k][w].st := by simp [receive]
  have hres := hstep.1
  have hsend : (extract w (receive w sm x[k]) x[k + 1]).send = relayedObjects sm.msg := by
    rcases hres with h | ⟨hempty, -⟩
    · simp only [Record.reactionsOf, Set.mem_setOf_eq] at h
      obtain ⟨n', -, h⟩ := h
      rw [h]
    · exfalso
      obtain ⟨n', hn'⟩ := hne
      have h' : ({ state := n', send := relayedObjects sm.msg } :
          NodeStepResult M.N (NamedObject V)) ∈
          Record.reactionsOf M S w ((receive w sm x[k])[w].st)
            ((receive w sm x[k])[w].clock : Int) (.recv sm) := by
        simp only [Record.reactionsOf, Set.mem_setOf_eq]
        exact ⟨n', by rw [hst]; exact hn', rfl⟩
      rw [hempty] at h'
      exact h'
  calc x[k + 1].sent
      = (applyNodeStepResult w (extract w (receive w sm x[k]) x[k + 1])
          (receive w sm x[k])).sent := congrArg Config.sent hstep.2
    _ = (receive w sm x[k]).sent
          + (extract w (receive w sm x[k]) x[k + 1]).send.map (SignedMsg.mk w) := rfl
    _ = x[k].sent + (relayedObjects sm.msg).map (SignedMsg.mk w) := by rw [hsend]; rfl

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- When step `k` delivers `sm` to `w` and `w`'s receipt of `sm.msg` has an outcome, every object of
    `relayedObjects sm.msg`, signed by `w`, is in the multiset difference
    `x[k + 1].sent - x[k].sent`. -/
theorem mem_sent_diff_of_deliver (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {k : Nat} {w : V}
    {sm : SignedMsg V (NamedObject V)} {o : NamedObject V}
    (hl : x.lbl k = AtomicAction.deliver w sm) (ho : o ∈ relayedObjects sm.msg)
    (hne : ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[k][w].st) sm.msg ⇢ n') :
    (⟨w, o⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent - x[k].sent := by
  rw [Restated.sent_succ_of_deliver facts S Sched x hl hne, add_tsub_cancel_left]
  exact Multiset.mem_map.2 ⟨o, ho, rfl⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If the tick of `v` at a tick step `k`, whose instant is a whole multiple of `S.E.Δ`, from the
    node state its wake stage leaves, has an outcome, and every outcome sends `o`, then `o`, signed
    by `v`, is in the multiset difference `x[k + 1].sent - x[k].sent`. -/
theorem mem_sent_diff_of_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {k t : Nat} {v : V} {o : NamedObject V}
    (hl : x.lbl k = AtomicAction.tickAllAwake t)
    (haw : v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int))
    (hdvd : (t : Int) % S.E.Δ = 0)
    (ho : ∀ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (t : Int) x[k] v) (t : Int) ⇢ out → o ∈ out.2)
    (hne : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (t : Int) x[k] v) (t : Int) ⇢ out) :
    (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent - x[k].sent := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  obtain ⟨-, w, tk, hwake, htick, hc⟩ := hs
  obtain ⟨out, hout, htkv⟩ := tick_outcome_of_step S Sched hwake htick haw hdvd hne
  have hsent : x[k + 1].sent = x[k].sent
      + (Sched.awake (t : Int) \ Sched.adv (t : Int)).sum
          (fun q => ((w q).send + (tk q).send).map (SignedMsg.mk q)) := by
    rw [hc]; rfl
  rw [hsent, add_tsub_cancel_left]
  refine Multiset.mem_sum.2 ⟨v, haw, ?_⟩
  refine Multiset.mem_map.2 ⟨o, Multiset.mem_add.2 (Or.inr ?_), rfl⟩
  rw [htkv]
  exact Multiset.mem_coe.2 (ho out hout)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If keeping `u`'s events of `l` gives `u`'s own events of the first `k` steps, some world the
    fold of `l` from the initial world reaches holds `x[k][u].st` at `u`. -/
private theorem exists_fold_of_filter_eq (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (u : V) (k : Nat)
    (l : List (Record.Event V))
    (hfil : l.filter (fun e => decide (Record.Event.node e = u)) = Record.veventsOf M S Sched x u k) :
    ∃ w ∈ l.foldlM (Record.worldStepOf M (Setup.alwaysAwake S))
        (fun v' => M.initial (Setup.alwaysAwake S) v'), w u = x[k][u].st := by
  obtain ⟨w, hw, hwv⟩ := Record.fold_veventsOf M S Sched x facts.nd.wake_events_or_id u k
  have himg := Restated.foldl_step_apply_init facts (Setup.alwaysAwake S) u l
  rw [hfil] at himg
  have hmem2 : w u ∈ (fun w' => w' u) '' (l.foldlM (Record.worldStepOf M (Setup.alwaysAwake S))
      (fun v' => M.initial (Setup.alwaysAwake S) v')) := by
    rw [himg]; exact ⟨w, hw, rfl⟩
  obtain ⟨w', hw', hw'v⟩ := hmem2
  exact ⟨w', hw', hw'v.trans hwv⟩

/-- If keeping `u`'s events of `l` gives `u`'s own events of the first `k` steps followed by a wake
    of `u`, some world the fold of `l` from the initial world reaches holds `M.wake x[k][u].st` at
    `u`. -/
private theorem exists_fold_of_filter_eq_wake (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (u : V) (k : Nat)
    (t : DecoupledConsensusModel.Time) (l : List (Record.Event V))
    (hfil : l.filter (fun e => decide (Record.Event.node e = u))
      = Record.veventsOf M S Sched x u k ++ [Record.Event.wake u t]) :
    ∃ w ∈ l.foldlM (Record.worldStepOf M (Setup.alwaysAwake S))
        (fun v' => M.initial (Setup.alwaysAwake S) v'), w u = M.wake x[k][u].st := by
  obtain ⟨w, hw, hwv⟩ := Record.fold_veventsOf M S Sched x facts.nd.wake_events_or_id u k
  have hw₁ : Function.update w u (M.wake (w u)) ∈
      (Record.veventsOf M S Sched x u k ++ [Record.Event.wake u t]).foldlM
        (Record.worldStepOf M (Setup.alwaysAwake S)) (fun v' => M.initial (Setup.alwaysAwake S) v') := by
    rw [List.foldlM_append, Set.bind_def]
    refine Set.mem_biUnion hw ?_
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
    exact Set.mem_singleton _
  have himg := Restated.foldl_step_apply_init facts (Setup.alwaysAwake S) u l
  rw [hfil] at himg
  have hmem2 : M.wake x[k][u].st ∈ (fun w' => w' u) ''
      (l.foldlM (Record.worldStepOf M (Setup.alwaysAwake S))
        (fun v' => M.initial (Setup.alwaysAwake S) v')) := by
    rw [himg]; exact ⟨_, hw₁, by simp only [Function.update_self, hwv]⟩
  obtain ⟨w', hw', hw'v⟩ := hmem2
  exact ⟨w', hw', hw'v⟩

/-- If `v`'s events of the `tickAllAwake τ` step start with its tick, the node state `v`'s tick
    reads at `τ` from `c` is `v`'s node state in `c`. -/
private theorem wakeStage_of_head_tick (facts : Record.Facts M) {S : Setup V}
    {Sched : Schedule V} {v : V} {now : Int} {τ : Nat} (c : Config V (NamedObject V) M.N)
    {t' : DecoupledConsensusModel.Time} {post : List (Record.Event V)}
    (h : Record.actionEventsOf M S Sched v now (AtomicAction.tickAllAwake τ)
      = Record.Event.tick v t' :: post) :
    Record.wakeStage M Sched (τ : Int) c v = c[v].st := by
  rw [Record.wakeStage_coe]
  by_cases he : v ∈ entrants Sched τ
  · rw [if_pos he]
    rcases facts.nd.wake_events_or_id with hw | hw
    · simp [Record.actionEventsOf, hw, he] at h
    · exact hw _
  · rw [if_neg he]

/-- If `wake v t` is among `v₀`'s events of a step, the node state `v`'s tick reads at `t` from `c`
    is `M.wake` of `v`'s node state in `c`. -/
private theorem wakeStage_of_mem_wake {S : Setup V} {Sched : Schedule V} {v₀ v : V} {now : Int}
    {a : AtomicAction V (NamedObject V) Empty} {t : Int} (c : Config V (NamedObject V) M.N)
    (h : Record.Event.wake v t ∈ Record.actionEventsOf M S Sched v₀ now a) :
    Record.wakeStage M Sched t c v = M.wake c[v].st := by
  obtain ⟨τ, -, hτ, -, -, hent⟩ := wake_of_mem_actionEventsOf h
  rw [← hτ, Record.wakeStage_coe, if_pos hent]

/-- An event `e` at index `idx` of the run over the first `n` steps comes from a step `k < n`, and
    some world the run can reach before `e` holds at `e`'s validator `x[k]`'s node state when `e` is
    a wake or a delivery, and the node state `Record.wakeStage M Sched t x[k]` that the tick reads
    when `e` is a tick. -/
theorem stateBefore_of_getElem?_runEvents (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    (n idx : Nat) {e : Record.Event V}
    (he : (Restated.runEvents M S Sched x n)[idx]? = some e) :
    ∃ k < n, e ∈ Record.actionEventsOf M S Sched (Record.Event.node e) (x[k].time : Int) (x.lbl k) ∧
      ∃ w ∈ Record.stateBeforeOf M (Setup.alwaysAwake S) (Restated.runAll M S Sched x v n) idx,
        (∃ t, e = Record.Event.wake (Record.Event.node e) t ∧
          w (Record.Event.node e) = x[k][Record.Event.node e].st) ∨
        (∃ t, e = Record.Event.tick (Record.Event.node e) t ∧
          w (Record.Event.node e) = Record.wakeStage M Sched t x[k] (Record.Event.node e)) ∨
        (∃ o t, e = Record.Event.deliver (Record.Event.node e) o t ∧
          w (Record.Event.node e) = x[k][Record.Event.node e].st) := by
  obtain ⟨k, hk, hmem, hfil⟩ := Restated.filter_take_runEvents facts S Sched x n idx he
  refine ⟨k, hk, hmem, ?_⟩
  show ∃ w ∈ ((Restated.runEvents M S Sched x n).take idx).foldlM
      (Record.worldStepOf M (Setup.alwaysAwake S)) (fun v' => M.initial (Setup.alwaysAwake S) v'), _
  rcases hfil with ⟨hfil, post, hpost⟩ | ⟨t, hA, hte, hfil⟩
  · obtain ⟨w, hw, hwv⟩ := exists_fold_of_filter_eq facts S Sched x _ k _ hfil
    refine ⟨w, hw, ?_⟩
    rcases Record.mem_actionEventsOf_cases hmem with ⟨τ, hl, he' | he'⟩ | ⟨p, m, hl, hp, he'⟩
    · exact Or.inl ⟨_, he', hwv⟩
    · refine Or.inr (Or.inl ⟨_, he', ?_⟩)
      rw [hwv]
      rw [hl] at hpost
      exact (wakeStage_of_head_tick facts x[k] (hpost.trans (congrArg (· :: post) he'))).symm
    · exact Or.inr (Or.inr ⟨_, _, he', hwv⟩)
  · obtain ⟨w, hw, hwv⟩ := exists_fold_of_filter_eq_wake facts S Sched x _ k _ _ hfil
    refine ⟨w, hw, Or.inr (Or.inl ⟨_, hte, ?_⟩)⟩
    rw [hwv, wakeStage_of_mem_wake x[k] (show Record.Event.wake (Record.Event.node e) (t : Int)
      ∈ Record.actionEventsOf M S Sched (Record.Event.node e) (x[k].time : Int) (x.lbl k) by
        rw [hA]; exact List.mem_cons_self ..)]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Folding any list of events from any world `u` reaches some world. -/
private theorem foldlM_worldStepOf_nonempty (M : Record.Model V) (S : Setup V) :
    ∀ (l : List (Record.Event V)) (u : V → M.N), ∃ u', u' ∈ l.foldlM (Record.worldStepOf M S) u
  | [], u => ⟨u, Set.mem_singleton u⟩
  | e :: l, u => by
      obtain ⟨u₁, hu₁⟩ := worldStepOf_nonempty M S u e
      obtain ⟨u', hu'⟩ := foldlM_worldStepOf_nonempty M S l u₁
      refine ⟨u', ?_⟩
      rw [List.foldlM_cons, Set.bind_def]
      exact Set.mem_biUnion hu₁ hu'

/-- There is a sequence of worlds `g` with `g 0 = u` and, for every `m`, `g (m + 1)` among the
    worlds the event at index `s + m` of `es` can lead to from `g m` (or `g m` itself past the end
    of `es`). -/
private theorem exists_path_from (M : Record.Model V) (S : Setup V) (es : List (Record.Event V))
    (s : Nat) (u : V → M.N) :
    ∃ g : Nat → V → M.N, g 0 = u ∧
      ∀ m, g (m + 1) ∈ ((es.drop (s + m)).take 1).foldlM (Record.worldStepOf M S) (g m) := by
  choose f hf using fun (m : Nat) (u' : V → M.N) =>
    foldlM_worldStepOf_nonempty M S ((es.drop (s + m)).take 1) u'
  exact ⟨fun m => Nat.rec u (fun m gm => f m gm) m, rfl, fun m => hf m _⟩

/-- If `W` follows `es` one event at a time and `w'` is a world the event `i` can lead to from
    `W i`, some sequence `W'` follows `es`, agrees with `W` up to `i`, and has `W' (i + 1) = w'`. -/
private theorem path_splice (M : Record.Model V) (S : Setup V) (es : List (Record.Event V))
    (W : Nat → V → M.N)
    (hW : ∀ j, W (j + 1) ∈ ((es.drop j).take 1).foldlM (Record.worldStepOf M S) (W j))
    (i : Nat) (w' : V → M.N)
    (hw' : w' ∈ ((es.drop i).take 1).foldlM (Record.worldStepOf M S) (W i)) :
    ∃ W' : Nat → V → M.N,
      (∀ j, W' (j + 1) ∈ ((es.drop j).take 1).foldlM (Record.worldStepOf M S) (W' j)) ∧
      (∀ j, j ≤ i → W' j = W j) ∧ W' (i + 1) = w' := by
  classical
  obtain ⟨g, hg0, hg⟩ := exists_path_from M S es (i + 1) w'
  refine ⟨fun j => if j ≤ i then W j else g (j - (i + 1)), ?_, ?_, ?_⟩
  · intro j
    rcases Nat.lt_trichotomy j i with hj | hj | hj
    · have h1 : j ≤ i := Nat.le_of_lt hj
      have h2 : j + 1 ≤ i := hj
      simp only [if_pos h1, if_pos h2]
      exact hW j
    · subst hj
      have h2 : ¬ j + 1 ≤ j := Nat.not_succ_le_self j
      simp only [if_pos (Nat.le_refl j), if_neg h2, Nat.sub_self, hg0]
      exact hw'
    · have h1 : ¬ j ≤ i := Nat.not_le_of_lt hj
      have h2 : ¬ j + 1 ≤ i := fun h => h1 (Nat.le_of_succ_le h)
      simp only [if_neg h1, if_neg h2]
      have he : j + 1 - (i + 1) = (j - (i + 1)) + 1 := by omega
      have hs : i + 1 + (j - (i + 1)) = j := by omega
      rw [he]
      have := hg (j - (i + 1))
      rw [hs] at this
      exact this
  · intro j hj
    simp only [if_pos hj]
  · have h2 : ¬ i + 1 ≤ i := Nat.not_succ_le_self i
    simp only [if_neg h2, Nat.sub_self, hg0]

/-- If `w` is among the worlds the first `i` events of `es` can reach from `w₀`, some sequence `W`
    with `W 0 = w₀` follows `es` one event at a time and has `W i = w`. -/
private theorem path_of_mem_take (M : Record.Model V) (S : Setup V) (es : List (Record.Event V))
    (w₀ : V → M.N) :
    ∀ (i : Nat) (w : V → M.N), w ∈ (es.take i).foldlM (Record.worldStepOf M S) w₀ →
      ∃ W : Nat → V → M.N, W 0 = w₀ ∧
        (∀ j, W (j + 1) ∈ ((es.drop j).take 1).foldlM (Record.worldStepOf M S) (W j)) ∧
        W i = w
  | 0, w, hw => by
      have hw0 : w = w₀ := by
        simpa [List.take_zero, List.foldlM_nil] using hw
      obtain ⟨g, hg0, hg⟩ := exists_path_from M S es 0 w₀
      refine ⟨g, hg0, fun j => by simpa using hg j, by rw [hg0, hw0]⟩
  | i + 1, w, hw => by
      rw [List.take_add, List.foldlM_append, Set.bind_def] at hw
      obtain ⟨u, hu, hwu⟩ := Set.mem_iUnion₂.1 hw
      obtain ⟨W, hW0, hW, hWi⟩ := path_of_mem_take M S es w₀ i u hu
      obtain ⟨W', hW', hW'le, hW'i⟩ := path_splice M S es W hW i w (by rw [hWi]; exact hwu)
      exact ⟨W', by rw [hW'le 0 (Nat.zero_le i), hW0], hW', hW'i⟩

/-- A sequence of worlds that starts at the initial world and follows the events of `rho` one at a
    time is a path of `rho`. -/
private theorem onePath_of_follows (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW0 : W 0 = fun v' => M.initial S v')
    (hW : ∀ j, W (j + 1) ∈ ((rho.events.drop j).take 1).foldlM (Record.worldStepOf M S) (W j)) :
    Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W := by
  have hmem : ∀ i, W i ∈ Record.stateBeforeOf M S rho i := by
    intro i
    induction i with
    | zero =>
        show W 0 ∈ (rho.events.take 0).foldlM (Record.worldStepOf M S)
          (fun v' => M.initial S v')
        rw [hW0]
        exact Set.mem_singleton _
    | succ i ih =>
        show W (i + 1) ∈ (rho.events.take (i + 1)).foldlM (Record.worldStepOf M S)
          (fun v' => M.initial S v')
        rw [List.take_add, List.foldlM_append, Set.bind_def]
        exact Set.mem_biUnion ih (hW i)
  intro i
  refine ⟨hmem i, ?_⟩
  rw [Nat.add_sub_cancel_left]
  exact hW i

/-- For every outcome of `v₀`'s tick at a step `k < n` whose instant is a whole multiple of `S.E.Δ`,
    from the node state its wake stage leaves, with `o` in its list, some path of the run emits `o`
    from `v₀` at the time of that tick. -/
theorem emits_runAll_of_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    {n k t : Nat} (hk : k < n) {v₀ : V}
    {o : NamedObject V}
    (hl : x.lbl k = AtomicAction.tickAllAwake t)
    (haw : v₀ ∈ Sched.awake (t : Int) \ Sched.adv (t : Int))
    (hdvd : (t : Int) % S.E.Δ = 0)
    {out : M.N × List (NamedObject V)}
    (hout : M.tick (Setup.alwaysAwake S) v₀ (Record.wakeStage M Sched (t : Int) x[k] v₀) (t : Int) ⇢ out)
    (ho : o ∈ out.2) :
    ∃ W : Nat → V → M.N,
      Restated.Vocabulary.Execution.NamedRun.OnePath M (Setup.alwaysAwake S)
        (Restated.runAll M S Sched x v n) W ∧
      Restated.Vocabulary.Execution.NamedRun.emitsAlong M (Setup.alwaysAwake S)
        (Restated.runAll M S Sched x v n) W v₀ o (t : Int) := by
  have hcond : v₀ ∈ Sched.awake (t : Int) \ Sched.adv (t : Int) ∧ (t : Int) % S.E.Δ = 0 :=
    ⟨haw, hdvd⟩
  have hev : (Record.Event.tick v₀ (t : Int) : Record.Event V)
      ∈ Record.actionEventsOf M S Sched v₀ (x[k].time : Int) (x.lbl k) := by
    rw [hl]
    simp only [Record.actionEventsOf, List.mem_append, if_pos hcond, List.mem_singleton, or_true]
  obtain ⟨idx, hidx⟩ :=
    List.getElem?_of_mem (Restated.mem_runEvents_of_mem_actionEvents facts S Sched x n k hk v₀ _ hev)
  obtain ⟨k', hk', hmem', w, hw, hwv⟩ :=
    Restated.stateBefore_of_getElem?_runEvents facts S Sched x v n idx hidx
  obtain ⟨τ, hlbl', hτ, -⟩ := tickAllAwake_of_mem_actionEventsOf hmem'
  have hτt : τ = t := Nat.cast_injective hτ
  rw [hτt] at hlbl'
  have hkk : k' = k := Restated.tickAllAwake_step_unique facts S Sched x hlbl' hl
  subst hkk
  have hwv' : w v₀ = Record.wakeStage M Sched (t : Int) x[k'] v₀ := by
    rcases hwv with ⟨t', he', -⟩ | ⟨t', he', hw'⟩ | ⟨o', t', he', -⟩
    · cases he'
    · injection he' with h1 h2
      rw [← h2] at hw'
      exact hw'
    · cases he'
  have hw' : w ∈ ((Restated.runEvents M S Sched x n).take idx).foldlM
      (Record.worldStepOf M (Setup.alwaysAwake S))
        (fun v' => M.initial (Setup.alwaysAwake S) v') := hw
  obtain ⟨W, hW0, hW, hWi⟩ := path_of_mem_take M (Setup.alwaysAwake S)
    (Restated.runEvents M S Sched x n) (fun v' => M.initial (Setup.alwaysAwake S) v') idx w hw'
  have hdrop : ((Restated.runEvents M S Sched x n).drop idx).take 1
      = [(Record.Event.tick v₀ (t : Int) : Record.Event V)] := by
    have h1 : ((Restated.runEvents M S Sched x n).drop idx)[0]?
        = some (Record.Event.tick v₀ (t : Int) : Record.Event V) := by
      rw [List.getElem?_drop]; simpa using hidx
    cases hd : (Restated.runEvents M S Sched x n).drop idx with
    | nil => rw [hd] at h1; simp at h1
    | cons a l =>
        rw [hd] at h1
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h1
        rw [h1]
        rfl
  have hstep : Function.update w v₀ out.1 ∈
      (((Restated.runEvents M S Sched x n).drop idx).take 1).foldlM
        (Record.worldStepOf M (Setup.alwaysAwake S)) (W idx) := by
    rw [hdrop, hWi]
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
    exact Or.inl ⟨out, by rw [hwv']; exact hout, rfl⟩
  obtain ⟨W', hW', hW'le, hW'i⟩ := path_splice M (Setup.alwaysAwake S)
    (Restated.runEvents M S Sched x n) W hW idx _ hstep
  refine ⟨W', onePath_of_follows M (Setup.alwaysAwake S) (Restated.runAll M S Sched x v n) W'
    (by rw [hW'le 0 (Nat.zero_le idx), hW0]) hW', idx, hidx, out, ?_, ?_, ho⟩
  · rw [hW'le idx (Nat.le_refl idx), hWi, hwv']
    exact hout
  · rw [hW'i]
    simp only [Function.update_self]

end

/-! ## The path of the run that the execution follows -/

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For `j ≤ j'`, `u`'s own events of the first `j` steps are a prefix of its events of the first
    `j'` steps. -/
private theorem veventsOf_prefix (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (u : V) {j j' : Nat} (h : j ≤ j') :
    Record.veventsOf M S Sched x u j <+: Record.veventsOf M S Sched x u j' := by
  induction j', h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ j' h ih => exact ih.trans ⟨_, rfl⟩

/-- If step `i` contributes no event of `u`, `u`'s node state after it is its node state before it. -/
private theorem st_succ_of_actionEvents_nil (M : Record.Model V) (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (u : V) (i : Nat)
    (h : Record.actionEventsOf M S Sched u (x[i].time : Int) (x.lbl i) = []) :
    x[i + 1][u].st = x[i][u].st := by
  obtain ⟨w', hw', hw'u⟩ :=
    Record.fold_actionEventsOf M S Sched x facts.nd.wake_events_or_id u i (fun _ => x[i][u].st) rfl
  rw [h] at hw'
  have hw'' : w' = fun _ => x[i][u].st := hw'
  rw [← hw'u, hw'']

/-- For `j ≤ j'`, if `u`'s events of the first `j` steps and of the first `j'` steps agree, `u`
    holds the same node state after both. -/
private theorem st_eq_of_veventsOf_eq_of_le (M : Record.Model V) (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (u : V) {j j' : Nat}
    (hj : j ≤ j')
    (h : Record.veventsOf M S Sched x u j = Record.veventsOf M S Sched x u j') :
    x[j][u].st = x[j'][u].st := by
  induction j', hj using Nat.le_induction with
  | base => rfl
  | succ j' hj ih =>
      have hp := veventsOf_prefix M S Sched x u hj
      have hsucc : Record.veventsOf M S Sched x u (j' + 1)
          = Record.veventsOf M S Sched x u j' ++
              Record.actionEventsOf M S Sched u (x[j'].time : Int) (x.lbl j') := rfl
      have hlen : (Record.veventsOf M S Sched x u j).length
          = (Record.veventsOf M S Sched x u (j' + 1)).length := by rw [h]
      rw [hsucc, List.length_append] at hlen
      have hle := hp.length_le
      have hnil : Record.actionEventsOf M S Sched u (x[j'].time : Int) (x.lbl j') = [] :=
        List.eq_nil_of_length_eq_zero (by omega)
      have hj' : Record.veventsOf M S Sched x u j = Record.veventsOf M S Sched x u j' := by
        rw [h, hsucc, hnil, List.append_nil]
      rw [ih hj', st_succ_of_actionEvents_nil M facts S Sched x u j' hnil]

/-- If `u`'s events of the first `j` steps and of the first `j'` steps agree, `u` holds the same
    node state after both. -/
private theorem st_eq_of_veventsOf_eq (M : Record.Model V) (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (u : V) {j j' : Nat}
    (h : Record.veventsOf M S Sched x u j = Record.veventsOf M S Sched x u j') :
    x[j][u].st = x[j'][u].st := by
  rcases le_total j j' with hj | hj
  · exact st_eq_of_veventsOf_eq_of_le M facts S Sched x u hj h
  · exact (st_eq_of_veventsOf_eq_of_le M facts S Sched x u hj h.symm).symm

/-- The events of `u` among the first `idx` events of the run over the first `n` steps are `u`'s own
    events of the first `j` steps for some `j ≤ n`, or `u`'s events of the first `j` steps followed
    by its wake, for a step `j < n` at which `u` woke and ticked. -/
theorem exists_veventsOf_eq_filter_take (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (u : V) :
    ∀ (n idx : Nat), (∃ j ≤ n, Record.veventsOf M S Sched x u j =
        ((Restated.runEvents M S Sched x n).take idx).filter
          (fun e => decide (Record.Event.node e = u))) ∨
      ∃ j < n, ∃ t : Nat,
        Record.actionEventsOf M S Sched u (x[j].time : Int) (x.lbl j)
          = [Record.Event.wake u (t : Int), Record.Event.tick u (t : Int)] ∧
        Record.veventsOf M S Sched x u j ++ [Record.Event.wake u (t : Int)] =
          ((Restated.runEvents M S Sched x n).take idx).filter
            (fun e => decide (Record.Event.node e = u))
  | 0, idx => Or.inl ⟨0, le_rfl, by
      rw [show Restated.runEvents M S Sched x 0 = [] from rfl, List.take_nil, List.filter_nil]
      rfl⟩
  | n + 1, idx => by
      rw [show Restated.runEvents M S Sched x (n + 1)
            = Restated.runEvents M S Sched x n ++ Restated.stepEvents M S Sched x n from rfl]
      by_cases hidx : idx ≤ (Restated.runEvents M S Sched x n).length
      · rw [List.take_append_of_le_length hidx]
        rcases exists_veventsOf_eq_filter_take facts S Sched x u n idx with
          ⟨j, hj, h⟩ | ⟨j, hj, t, hA, h⟩
        · exact Or.inl ⟨j, Nat.le_succ_of_le hj, h⟩
        · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, t, hA, h⟩
      · rw [List.take_append, List.take_of_length_le (by omega), List.filter_append,
          Restated.filter_runEvents facts]
        have hpre := (List.take_prefix (idx - (Restated.runEvents M S Sched x n).length)
          (Restated.stepEvents M S Sched x n)).filter (fun e => decide (Record.Event.node e = u))
        rw [Restated.filter_stepEvents facts] at hpre
        have hvk : Record.veventsOf M S Sched x u (n + 1) = Record.veventsOf M S Sched x u n ++
            Record.actionEventsOf M S Sched u (x[n].time : Int) (x.lbl n) := rfl
        rcases actionEventsOf_cases S Sched u (x[n].time : Int) (x.lbl n) with
          h0 | ⟨e, h1⟩ | ⟨t, -, h2⟩
        · rw [h0, List.prefix_nil] at hpre
          exact Or.inl ⟨n, Nat.le_succ n, by rw [hpre, List.append_nil]⟩
        · rw [h1] at hpre
          rcases List.prefix_cons_iff.1 hpre with hnil | ⟨l, hl, hpl⟩
          · exact Or.inl ⟨n, Nat.le_succ n, by rw [hnil, List.append_nil]⟩
          · rw [List.prefix_nil] at hpl
            subst hpl
            refine Or.inl ⟨n + 1, le_rfl, ?_⟩
            rw [hl, hvk, h1]
        · rw [h2] at hpre
          rcases List.prefix_cons_iff.1 hpre with hnil | ⟨l, hl, hpl⟩
          · exact Or.inl ⟨n, Nat.le_succ n, by rw [hnil, List.append_nil]⟩
          · rcases List.prefix_cons_iff.1 hpl with hnil' | ⟨l', hl', hpl'⟩
            · subst hnil'
              exact Or.inr ⟨n, Nat.lt_succ_self n, t, h2, by rw [hl]⟩
            · rw [List.prefix_nil] at hpl'
              subst hpl'
              subst hl'
              refine Or.inl ⟨n + 1, le_rfl, ?_⟩
              rw [hl, hvk, h2]

/-- If `u`'s events of the first `j` steps are its events among the first `idx` events of the run,
    `runAllPath` before event `idx` holds `x[j][u].st` at `u`. -/
theorem runAllPath_eq (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    (n idx : Nat) (u : V) {j : Nat}
    (hj : Record.veventsOf M S Sched x u j =
      ((Restated.runEvents M S Sched x n).take idx).filter
        (fun e => decide (Record.Event.node e = u))) :
    Restated.runAllPath M S Sched x v n idx u = x[j][u].st := by
  have hex : ∃ j : Nat, Record.veventsOf M S Sched x u j =
      ((Restated.runEvents M S Sched x n).take idx).filter
        (fun e => decide (Record.Event.node e = u)) := ⟨j, hj⟩
  simp only [Restated.runAllPath, dif_pos hex]
  exact st_eq_of_veventsOf_eq M facts S Sched x u ((Classical.choose_spec hex).trans hj.symm)

/-- If at step `j` validator `u` woke and ticked at `t`, and `u`'s events among the first `idx`
    events of the run are its events of the first `j` steps followed by that wake, `runAllPath`
    before event `idx` holds `M.wake x[j][u].st` at `u`. -/
theorem runAllPath_eq_wake (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    (n idx : Nat) (u : V) {j t : Nat}
    (hA : Record.actionEventsOf M S Sched u (x[j].time : Int) (x.lbl j)
      = [Record.Event.wake u (t : Int), Record.Event.tick u (t : Int)])
    (hj : Record.veventsOf M S Sched x u j ++ [Record.Event.wake u (t : Int)] =
      ((Restated.runEvents M S Sched x n).take idx).filter
        (fun e => decide (Record.Event.node e = u))) :
    Restated.runAllPath M S Sched x v n idx u = M.wake x[j][u].st := by
  have hno : ¬ ∃ j' : Nat, Record.veventsOf M S Sched x u j' =
      ((Restated.runEvents M S Sched x n).take idx).filter
        (fun e => decide (Record.Event.node e = u)) := by
    rintro ⟨j', hj'⟩
    rw [← hj] at hj'
    have hlen := congrArg List.length hj'
    rw [List.length_append, List.length_singleton] at hlen
    rcases Nat.lt_or_ge j j' with h | h
    · have hp := (veventsOf_prefix M S Sched x u (show j + 1 ≤ j' from h)).length_le
      have h1 : (Record.veventsOf M S Sched x u (j + 1)).length
          = (Record.veventsOf M S Sched x u j).length + 2 := by
        show (Record.veventsOf M S Sched x u j ++
          Record.actionEventsOf M S Sched u (x[j].time : Int) (x.lbl j)).length = _
        rw [List.length_append, hA]
        rfl
      omega
    · have hp := (veventsOf_prefix M S Sched x u h).length_le
      omega
  have hex : ∃ j : Nat, ∃ t : DecoupledConsensusModel.Time,
      Record.veventsOf M S Sched x u j ++ [Record.Event.wake u t] =
        ((Restated.runEvents M S Sched x n).take idx).filter
          (fun e => decide (Record.Event.node e = u)) := ⟨j, (t : Int), hj⟩
  simp only [Restated.runAllPath, dif_neg hno, dif_pos hex]
  obtain ⟨t₀, h₀⟩ := Classical.choose_spec hex
  have heq := (List.append_inj' (h₀.trans hj.symm) rfl).1
  rw [st_eq_of_veventsOf_eq M facts S Sched x u heq]

/-- For `i ≤ n`, `runAllPath` before the events of the first `i` steps holds at `v₀` its node state
    after `i` steps. -/
theorem runAllPath_runEvents_length (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    {i n : Nat} (h : i ≤ n) (v₀ : V) :
    Restated.runAllPath M S Sched x v n (Restated.runEvents M S Sched x i).length v₀
      = x[i][v₀].st :=
  runAllPath_eq facts S Sched x v n _ v₀ (j := i)
    (by rw [Restated.take_runEvents facts S Sched x h, Restated.filter_runEvents facts])

/-- If the event `idx` of the run over the first `n` steps is `e`, it comes from a step `k < n`, and
    along `runAllPath` the validator of `e` holds, before and after `e`: `x[k]`'s node state and its
    wake stage when `e` is a wake; that wake stage and `x[k + 1]`'s node state when `e` is a tick;
    `x[k]`'s and `x[k + 1]`'s node states when `e` is a delivery. -/
theorem runAllPath_at_event (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    (n idx : Nat) {e : Record.Event V}
    (he : (Restated.runEvents M S Sched x n)[idx]? = some e) :
    ∃ k < n, e ∈ Record.actionEventsOf M S Sched (Record.Event.node e) (x[k].time : Int) (x.lbl k) ∧
      ((∃ t, e = Record.Event.wake (Record.Event.node e) t ∧
          Restated.runAllPath M S Sched x v n idx (Record.Event.node e)
            = x[k][Record.Event.node e].st ∧
          Restated.runAllPath M S Sched x v n (idx + 1) (Record.Event.node e)
            = Record.wakeStage M Sched t x[k] (Record.Event.node e)) ∨
       (∃ t, e = Record.Event.tick (Record.Event.node e) t ∧
          Restated.runAllPath M S Sched x v n idx (Record.Event.node e)
            = Record.wakeStage M Sched t x[k] (Record.Event.node e) ∧
          Restated.runAllPath M S Sched x v n (idx + 1) (Record.Event.node e)
            = x[k + 1][Record.Event.node e].st) ∨
       (∃ o t, e = Record.Event.deliver (Record.Event.node e) o t ∧
          Restated.runAllPath M S Sched x v n idx (Record.Event.node e)
            = x[k][Record.Event.node e].st ∧
          Restated.runAllPath M S Sched x v n (idx + 1) (Record.Event.node e)
            = x[k + 1][Record.Event.node e].st)) := by
  obtain ⟨k, hk, hmem, hfil⟩ := Restated.filter_take_runEvents facts S Sched x n idx he
  refine ⟨k, hk, hmem, ?_⟩
  have hsucc : ((Restated.runEvents M S Sched x n).take (idx + 1)).filter
        (fun e' => decide (Record.Event.node e' = Record.Event.node e))
      = ((Restated.runEvents M S Sched x n).take idx).filter
          (fun e' => decide (Record.Event.node e' = Record.Event.node e)) ++ [e] := by
    rw [List.take_add_one, he, Option.toList_some, List.filter_append]
    simp
  have hvk : Record.veventsOf M S Sched x (Record.Event.node e) (k + 1)
      = Record.veventsOf M S Sched x (Record.Event.node e) k ++
          Record.actionEventsOf M S Sched (Record.Event.node e) (x[k].time : Int) (x.lbl k) := rfl
  set u := Record.Event.node e with hu
  rcases hfil with ⟨hfil, post, hpost⟩ | ⟨t, hA, hte, hfil⟩
  · have hb : Restated.runAllPath M S Sched x v n idx u = x[k][u].st :=
      runAllPath_eq facts S Sched x v n idx u hfil.symm
    rcases actionEventsOf_cases S Sched u (x[k].time : Int) (x.lbl k) with
      hA | ⟨e₁, hA⟩ | ⟨t₁, -, hA⟩
    · rw [hA] at hpost; cases hpost
    · rw [hA, List.cons.injEq] at hpost
      obtain ⟨he₁, -⟩ := hpost
      have ha : Restated.runAllPath M S Sched x v n (idx + 1) u = x[k + 1][u].st :=
        runAllPath_eq facts S Sched x v n (idx + 1) u (by rw [hsucc, hfil, hvk, hA, he₁])
      rcases Record.mem_actionEventsOf_cases hmem with ⟨τ, hl, he' | he'⟩ | ⟨p, m, hl, hp, he'⟩
      · refine Or.inl ⟨_, he', hb, ?_⟩
        rw [ha, wakeStage_of_mem_wake (v := u) (t := (τ : Int)) x[k] (by rw [← he']; exact hmem)]
        obtain ⟨w', hw', hw'v⟩ := Record.fold_actionEventsOf M S Sched x
          facts.nd.wake_events_or_id u k (fun _ => x[k][u].st) rfl
        rw [hA, he₁, he'] at hw'
        simp only [List.foldlM_cons, List.foldlM_nil, bind_pure, Record.worldStepOf,
          Set.mem_singleton_iff] at hw'
        rw [← hw'v, hw', Function.update_self]
      · refine Or.inr (Or.inl ⟨_, he', ?_, ha⟩)
        rw [hb]
        have h1 : Record.actionEventsOf M S Sched u (x[k].time : Int) (AtomicAction.tickAllAwake τ)
            = Record.Event.tick u (τ : Int) :: [] := by rw [← hl, hA, he₁, he']
        exact (wakeStage_of_head_tick facts x[k] h1).symm
      · exact Or.inr (Or.inr ⟨_, _, he', hb, ha⟩)
    · rw [hA, List.cons.injEq] at hpost
      obtain ⟨he₁, -⟩ := hpost
      refine Or.inl ⟨_, he₁.symm, hb, ?_⟩
      rw [wakeStage_of_mem_wake x[k] (show Record.Event.wake u (t₁ : Int)
        ∈ Record.actionEventsOf M S Sched u (x[k].time : Int) (x.lbl k) by
          rw [hA]; exact List.mem_cons_self ..)]
      exact runAllPath_eq_wake facts S Sched x v n (idx + 1) u hA (by rw [hsucc, hfil, he₁])
  · have hb : Restated.runAllPath M S Sched x v n idx u = M.wake x[k][u].st :=
      runAllPath_eq_wake facts S Sched x v n idx u hA hfil.symm
    have ha : Restated.runAllPath M S Sched x v n (idx + 1) u = x[k + 1][u].st :=
      runAllPath_eq facts S Sched x v n (idx + 1) u (by rw [hsucc, hfil, hvk, hA, hte]; simp)
    refine Or.inr (Or.inl ⟨_, hte, ?_, ha⟩)
    rw [hb, wakeStage_of_mem_wake x[k] (show Record.Event.wake u (t : Int)
      ∈ Record.actionEventsOf M S Sched u (x[k].time : Int) (x.lbl k) by
        rw [hA]; exact List.mem_cons_self ..)]

/-- Under monotone corruption, a validator awake and not adversarial at `τ` is not adversarial at
    any time up to `τ`. -/
theorem honest_upTo_of_mono {Sched : Schedule V} (hmono : Sched.MonotoneCorruption) {τ : Int}
    {v : V}
    -- `v` is awake and not held by the adversary at `τ`.
    (hv : v ∈ Sched.awake τ \ Sched.adv τ) : ∀ t' ≤ τ, v ∉ Sched.adv t' :=
  fun t' ht' h => (Finset.mem_sdiff.1 hv).2 (hmono t' τ ht' h)

/-- A tick event of `u` at `t` among the events a step labelled `a` gives `u` means `a` is
    `tickAllAwake τ` with `t = τ`, `u` is awake and not adversarial at `τ`, and `τ` is a whole
    multiple of `S.E.Δ`. -/
theorem tick_mem_actionEventsOf {S : Setup V} {Sched : Schedule V} {u : V} {now : Int}
    {a : AtomicAction V (NamedObject V) Empty} {t : Int}
    (h : Record.Event.tick u t ∈ Record.actionEventsOf M S Sched u now a) :
    ∃ τ : Nat, a = AtomicAction.tickAllAwake τ ∧ t = (τ : Int) ∧
      u ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) ∧ (τ : Int) % S.E.Δ = 0 := by
  cases a with
  | tickAllAwake τ =>
      refine ⟨τ, rfl, ?_⟩
      simp only [Record.actionEventsOf, List.mem_append] at h
      rcases h with h | h
      · split at h
        · simp at h
        · simp at h
      · split at h
        · rename_i hc
          simp only [List.mem_singleton, Record.Event.tick.injEq] at h
          exact ⟨h.2, hc⟩
        · simp at h
  | deliver p m =>
      simp only [Record.actionEventsOf] at h
      split at h <;> simp at h
  | custom _ ev => exact ev.elim
  | adversarial p m => simp [Record.actionEventsOf] at h
  | forward p m => simp [Record.actionEventsOf] at h

/-- Under monotone corruption, if every tick at a tick step of a validator honest up to its time has
    an outcome from the node state it reads, then every tick event of the run over the first `n`
    steps has an outcome from the node state `runAllPath` holds before it. -/
theorem tick_outcome_runAllPath (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (n : Nat)
    (hmono : Sched.MonotoneCorruption)
    -- Every tick at a tick step at a whole multiple of `S.E.Δ`, of a validator awake there and
    -- never adversarial up to it, has an outcome from the node state that tick reads.
    (hsts : ∀ (k τ : Nat) (u : V), x.lbl k = AtomicAction.tickAllAwake τ →
      (τ : Int) % S.E.Δ = 0 → u ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) →
      (∀ t' ≤ (τ : Int), u ∉ Sched.adv t') →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τ : Int) x[k] u) (τ : Int) ⇢ out) :
    ∀ (i : Nat) (u : V) (t : Int),
      (Restated.runAll M S Sched x v n).events[i]? = some (Record.Event.tick u t) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Restated.runAllPath M S Sched x v n i u) t ⇢ out := by
  intro i u t he
  obtain ⟨k, -, hmem, hcases⟩ := Restated.runAllPath_at_event facts S Sched x v n i he
  have hnode : Record.Event.node (Record.Event.tick u t : Record.Event V) = u := rfl
  simp only [hnode] at hmem hcases
  obtain ⟨τ, hl, hτ, hv, hΔ⟩ := tick_mem_actionEventsOf hmem
  rcases hcases with ⟨t', he', -, -⟩ | ⟨t', he', hb, -⟩ | ⟨o, t', he', -, -⟩
  · cases he'
  · have htt : t = t' := (Record.Event.tick.inj he').2
    subst htt
    rw [hb, hτ]
    exact hsts k τ u hl hΔ hv (honest_upTo_of_mono hmono hv)
  · cases he'

/-- If no two blocks in play have two ancestors with one root, an honest proposer never already
    holds a block carrying the root it is about to give its own proposal, corruption only grows,
    step `m` is the tick at `t`, `t` is a whole multiple of `S.E.Δ` and `q` is awake and not
    adversarial at `t`, then `q`'s tick at `t` has an outcome from the node state it reads. -/
theorem tick_outcome_of_tickStepAt (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    -- No two blocks in play (sent, or held by a validator honest through the step) have two
    -- ancestors with one root.
    (hroot : ∀ B C : NamedBlock V,
      (∃ B' : NamedBlock V,
        ((∃ (i : Nat) (sm : SignedMsg V (NamedObject V)),
            sm ∈ x[i].sent ∧ sm.msg = .block B') ∨
          (∃ (i : Nat) (v : V), (∀ t' ≤ (x[i].time : Int), v ∉ Sched.adv t') ∧
            B' ∈ x[i][v].st.st.bodies)) ∧
        NamedBlock.Preceq B B') →
      (∃ C' : NamedBlock V,
        ((∃ (i : Nat) (sm : SignedMsg V (NamedObject V)),
            sm ∈ x[i].sent ∧ sm.msg = .block C') ∨
          (∃ (i : Nat) (v : V), (∀ t' ≤ (x[i].time : Int), v ∉ Sched.adv t') ∧
            C' ∈ x[i][v].st.st.bodies)) ∧
        NamedBlock.Preceq C C') →
      ∀ A D : NamedBlock V,
        (NamedBlock.Preceq A B ∨ NamedBlock.Preceq A C) →
        (NamedBlock.Preceq D B ∨ NamedBlock.Preceq D C) → A.root = D.root → A = D)
    -- An honest proposer never already holds a block carrying the root it is about to give its own
    -- proposal.
    (hnew : ∀ (k τ : Nat) (s : Slot), x.lbl k = AtomicAction.tickAllAwake τ →
      (τ : Int) = M.proposal_time S.E s →
      (∀ t' ≤ (τ : Int), S.E.proposer s ∉ Sched.adv t') →
      ∀ B ∈ x[k][S.E.proposer s].st.st.bodies, B.root ≠ (S.node (S.E.proposer s)).new_root s)
    (hmono : Sched.MonotoneCorruption) {m : Nat} {t : Int} {q : V}
    (hm : Restated.tickStepAt M x m t)
    (hΔ : t % S.E.Δ = 0)
    -- `q` is awake and not held by the adversary at `t`.
    (hq : q ∈ Sched.awake t \ Sched.adv t) :
    ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched t x[m] q) t ⇢ out := by
  obtain ⟨τ, hl, rfl⟩ := hm
  exact facts.ndRun.tick_outcome_sts S Sched x hroot hnew m τ q hl hΔ hq (honest_upTo_of_mono hmono hq)

/-- If `u`'s events among the first `idx` and among the first `idx'` events of the run are the same,
    `runAllPath` holds the same node state at `u` before both. -/
private theorem runAllPath_congr (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (n : Nat) {idx idx' : Nat} (u : V)
    (h : ((Restated.runEvents M S Sched x n).take idx).filter
        (fun e => decide (Record.Event.node e = u))
      = ((Restated.runEvents M S Sched x n).take idx').filter
        (fun e => decide (Record.Event.node e = u))) :
    Restated.runAllPath M S Sched x v n idx u = Restated.runAllPath M S Sched x v n idx' u := by
  simp only [Restated.runAllPath]
  rw [h]

/-- If step `k` is the tick step at `τ`, `u` is awake and not adversarial there, `τ` is a whole
    multiple of `S.E.Δ`, and `W` holds at `u` its wake stage at `τ`, then the tick event of `u` at
    `τ` can lead from `W` to a world holding `x[k + 1][u].st` at `u`. -/
private theorem tick_step_world (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {k τ : Nat} {u : V}
    (hl : x.lbl k = AtomicAction.tickAllAwake τ)
    (hu : u ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int)) (hdvd : (τ : Int) % S.E.Δ = 0)
    (W : V → M.N) (hW : W u = Record.wakeStage M Sched (τ : Int) x[k] u) :
    ∃ w' ∈ Record.worldStepOf M (Setup.alwaysAwake S) W (Record.Event.tick u (τ : Int)),
      w' u = x[k + 1][u].st := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  obtain ⟨-, w, tk, hwake, htick, hc⟩ := hs
  have hx1 : x[k + 1][u].st = (tk u).state := by
    have h2 : x[k + 1][u] = (tickAllAwakeUpdate Sched τ x[k] w tk)[u] := by rw [hc]
    rw [h2, tickAllAwakeUpdate_getElem_awake (Finset.mem_sdiff.1 hu).1 (Finset.mem_sdiff.1 hu).2]
  have hwst := Record.wakeStage_of_TickAllAwakeWake M S Sched (hwake u)
  have htk := Record.protocolOf_step_tick M S (htick u hu)
  rw [hwst, ← hW] at htk
  rcases htk with ⟨-, out, hout, hst⟩ | ⟨hno, hst⟩
  · exact ⟨Function.update W u out.1, Or.inl ⟨out, hout, rfl⟩,
      by rw [Function.update_self, hx1, hst]⟩
  · refine ⟨W, Or.inr ⟨?_, rfl⟩, by rw [hx1, hst]⟩
    rcases hno with hnd | hno
    · exact absurd hdvd hnd
    · exact hno

/-- If step `k` delivers `m` to `u` and `W` holds `x[k][u].st` at `u`, then the delivery event of
    `m`'s payload to `u` can lead from `W` to a world holding `x[k + 1][u].st` at `u`. -/
private theorem deliver_step_world (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {k : Nat} {u : V}
    {m : SignedMsg V (NamedObject V)} (hl : x.lbl k = AtomicAction.deliver u m)
    (t : DecoupledConsensusModel.Time) (W : V → M.N) (hW : W u = x[k][u].st) :
    ∃ w' ∈ Record.worldStepOf M (Setup.alwaysAwake S) W (Record.Event.deliver u m.msg t),
      w' u = x[k + 1][u].st := by
  rcases Record.st_succ_of_deliver M S Sched x hl with h | ⟨hno, h⟩
  · exact ⟨Function.update W u x[k + 1][u].st, Or.inl ⟨_, by rw [hW]; exact h, rfl⟩,
      Function.update_self _ _ _⟩
  · exact ⟨W, Or.inr ⟨by rw [hW]; exact hno, rfl⟩, by rw [h, hW]⟩

/-- `runAllPath` is a path of the run over the first `n` steps: each of its worlds is one the run
    can reach before its event, and each event leads from one to the next. -/
theorem OnePath_runAllPath (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    (n : Nat) :
    Restated.Vocabulary.Execution.NamedRun.OnePath M (Setup.alwaysAwake S)
      (Restated.runAll M S Sched x v n) (Restated.runAllPath M S Sched x v n) := by
  refine onePath_of_follows M (Setup.alwaysAwake S) _ _ ?_ ?_
  · funext u
    rw [runAllPath_eq facts S Sched x v n 0 u (j := 0) (by simp; rfl)]
    exact Record.st_zero M S Sched x u
  · intro j
    show Restated.runAllPath M S Sched x v n (j + 1) ∈
      (((Restated.runEvents M S Sched x n).drop j).take 1).foldlM
        (Record.worldStepOf M (Setup.alwaysAwake S)) (Restated.runAllPath M S Sched x v n j)
    cases he : (Restated.runEvents M S Sched x n)[j]? with
    | none =>
        have hlen : (Restated.runEvents M S Sched x n).length ≤ j := List.getElem?_eq_none_iff.1 he
        rw [List.drop_of_length_le hlen, List.take_nil, List.foldlM_nil]
        show _ = _
        funext u
        exact runAllPath_congr S Sched x v n u
          (by rw [List.take_of_length_le (by omega), List.take_of_length_le hlen])
    | some e =>
        have hd : ((Restated.runEvents M S Sched x n).drop j).take 1 = [e] := by
          have h1 : ((Restated.runEvents M S Sched x n).drop j)[0]? = some e := by
            rw [List.getElem?_drop]; simpa using he
          cases hdr : (Restated.runEvents M S Sched x n).drop j with
          | nil => rw [hdr] at h1; simp at h1
          | cons a l =>
              rw [hdr] at h1
              simp only [List.getElem?_cons_zero, Option.some.injEq] at h1
              rw [h1]
              rfl
        rw [hd]
        simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
        have hfin : ∀ w' ∈ Record.worldStepOf M (Setup.alwaysAwake S)
            (Restated.runAllPath M S Sched x v n j) e,
            w' (Record.Event.node e) = Restated.runAllPath M S Sched x v n (j + 1) (Record.Event.node e) →
            Restated.runAllPath M S Sched x v n (j + 1) ∈ Record.worldStepOf M (Setup.alwaysAwake S)
              (Restated.runAllPath M S Sched x v n j) e := by
          intro w' hw' hw'v
          have hW : Restated.runAllPath M S Sched x v n (j + 1) = w' := by
            funext u
            by_cases hu : Record.Event.node e = u
            · subst hu
              exact hw'v.symm
            · rw [worldStepOf_at_other _ hu hw']
              exact runAllPath_congr S Sched x v n u
                (by rw [List.take_add_one, he, Option.toList_some, List.filter_append]; simp [hu])
          rw [hW]
          exact hw'
        obtain ⟨k, hk, hmem, hcase⟩ := runAllPath_at_event facts S Sched x v n j he
        generalize hu : Record.Event.node e = u at hcase hmem hfin
        rcases hcase with ⟨t, rfl, hb, ha⟩ | ⟨t, rfl, hb, ha⟩ | ⟨o, t, rfl, hb, ha⟩
        · refine hfin (Function.update (Restated.runAllPath M S Sched x v n j) u
            (M.wake (Restated.runAllPath M S Sched x v n j u))) (Set.mem_singleton _) ?_
          rw [Function.update_self, ha, hb, wakeStage_of_mem_wake x[k] hmem]
        · obtain ⟨τ, hl, hτ, hu', hdvd⟩ := tickAllAwake_of_mem_actionEventsOf hmem
          subst hτ
          obtain ⟨w', hw', hw'v⟩ := tick_step_world S Sched x hl hu' hdvd _ hb
          exact hfin w' hw' (hw'v.trans ha.symm)
        · obtain ⟨m, hl, hmsg, -⟩ := deliver_of_mem_actionEventsOf hmem
          subst hmsg
          obtain ⟨w', hw', hw'v⟩ := deliver_step_world S Sched x hl t _ hb
          exact hfin w' hw' (hw'v.trans ha.symm)

/-- If `out` is an outcome of `v₀`'s tick at a step `k < n` whose instant is a whole multiple of
    `S.E.Δ`, from the node state its wake stage leaves, and its node state is `v₀`'s node state
    after step `k`, then every object in `out`'s list is emitted by `v₀` at `t` along `runAllPath`. -/
theorem emits_runAllPath_of_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    {n k t : Nat} (hk : k < n) {v₀ : V}
    {o : NamedObject V}
    (hl : x.lbl k = AtomicAction.tickAllAwake t)
    (haw : v₀ ∈ Sched.awake (t : Int) \ Sched.adv (t : Int))
    (hdvd : (t : Int) % S.E.Δ = 0)
    {out : M.N × List (NamedObject V)}
    (hout : M.tick (Setup.alwaysAwake S) v₀ (Record.wakeStage M Sched (t : Int) x[k] v₀) (t : Int) ⇢ out)
    (hst : x[k + 1][v₀].st = out.1) (ho : o ∈ out.2) :
    Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S)
      (Restated.runAll M S Sched x v n) (Restated.runAllPath M S Sched x v n) v₀ o (t : Int) := by
  have hcond : v₀ ∈ Sched.awake (t : Int) \ Sched.adv (t : Int) ∧ (t : Int) % S.E.Δ = 0 :=
    ⟨haw, hdvd⟩
  have hev : (Record.Event.tick v₀ (t : Int) : Record.Event V)
      ∈ Record.actionEventsOf M S Sched v₀ (x[k].time : Int) (x.lbl k) := by
    rw [hl]
    simp only [Record.actionEventsOf, List.mem_append, if_pos hcond, List.mem_singleton, or_true]
  obtain ⟨idx, hidx⟩ :=
    List.getElem?_of_mem (Restated.mem_runEvents_of_mem_actionEvents facts S Sched x n k hk v₀ _ hev)
  obtain ⟨k', hk', hmem', hcase⟩ := runAllPath_at_event facts S Sched x v n idx hidx
  obtain ⟨τ, hlbl', hτ, -⟩ := tickAllAwake_of_mem_actionEventsOf hmem'
  have hτt : τ = t := Nat.cast_injective hτ
  rw [hτt] at hlbl'
  have hkk : k' = k := Restated.tickAllAwake_step_unique facts S Sched x hlbl' hl
  subst hkk
  rcases hcase with ⟨t', he', -⟩ | ⟨t', he', hb, ha⟩ | ⟨o', t', he', -⟩
  · cases he'
  · injection he' with h1 h2
    subst h2
    have hb' : Restated.runAllPath M S Sched x v n idx v₀
        = Record.wakeStage M Sched (t : Int) x[k'] v₀ := hb
    have ha' : Restated.runAllPath M S Sched x v n (idx + 1) v₀ = x[k' + 1][v₀].st := ha
    exact ⟨idx, hidx, out, by rw [hb']; exact hout, by rw [ha']; exact hst, ho⟩
  · cases he'

/-- If `⟨v, o⟩` is in the sent log `x[k + 1].sent` after the tick step `k` and not in `x[k].sent`,
    then `v` reacts at `t`, `t` is a whole multiple of `S.E.Δ`, and some outcome of `v`'s tick at
    `t`, from the node state its wake stage leaves, has `v`'s node state after the step as its node
    state and `o` in its list. -/
theorem tick_outcome_of_mem_sent_succ (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {k t : Nat} {v : V}
    {o : NamedObject V} (hl : x.lbl k = AtomicAction.tickAllAwake t)
    (hnew : (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent)
    (hold : (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∉ x[k].sent) :
    v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int) ∧ (t : Int) % S.E.Δ = 0 ∧
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (t : Int) x[k] v) (t : Int) ⇢ out ∧
          x[k + 1][v].st = out.1 ∧ o ∈ out.2 := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  obtain ⟨-, w, tk, hwake, htick, hc⟩ := hs
  have hsent : x[k + 1].sent = x[k].sent
      + (Sched.awake (t : Int) \ Sched.adv (t : Int)).sum
          (fun q => ((w q).send + (tk q).send).map (SignedMsg.mk q)) := by
    rw [hc]; rfl
  rw [hsent, Multiset.mem_add] at hnew
  rcases hnew with h | h
  · exact absurd h hold
  obtain ⟨q, hq, hmem⟩ := Multiset.mem_sum.1 h
  obtain ⟨o', ho', heq⟩ := Multiset.mem_map.1 hmem
  have hqv : q = v := congrArg SignedMsg.sender heq
  have hoo : o' = o := congrArg SignedMsg.msg heq
  subst hqv; subst hoo
  have hwst : (w q).state = Record.wakeStage M Sched (t : Int) x[k] q ∧ (w q).send = 0 := by
    refine ⟨Record.wakeStage_of_TickAllAwakeWake M S Sched (hwake q), ?_⟩
    have hww := hwake q
    unfold TickAllAwakeWake at hww
    by_cases he : q ∈ entrants Sched t
    · rw [if_pos he] at hww
      rw [Record.protocolOf_step_wake M S hww]
    · rw [if_neg he] at hww
      rw [hww]
  rw [hwst.2, zero_add] at ho'
  have hx1 : x[k + 1][q].st = (tk q).state := by
    have h2 : x[k + 1][q] = (tickAllAwakeUpdate Sched t x[k] w tk)[q] := by rw [hc]
    rw [h2, tickAllAwakeUpdate_getElem_awake (Finset.mem_sdiff.1 hq).1 (Finset.mem_sdiff.1 hq).2]
  have htk : tk q ∈ Record.reactionsOf M S q ((w q).state) (t : Int) .tick ∨
      (Record.reactionsOf M S q ((w q).state) (t : Int) .tick = ∅ ∧
        tk q = { state := (w q).state, send := 0 }) := htick q hq
  rcases htk with htk | ⟨-, htk⟩
  · by_cases hp : (t : Int) % S.E.Δ = 0
    · simp only [Record.reactionsOf, if_pos hp, Set.mem_setOf_eq] at htk
      obtain ⟨out, hout, htkv⟩ := htk
      rw [htkv] at ho' hx1
      rw [hwst.1] at hout
      exact ⟨hq, hp, out, hout, hx1, Multiset.mem_coe.1 ho'⟩
    · simp only [Record.reactionsOf, if_neg hp, Set.mem_singleton_iff] at htk
      rw [htk] at ho'
      exact absurd ho' (by simp)
  · rw [htk] at ho'
    exact absurd ho' (by simp)

/-- If `out` is an outcome of `v`'s tick at the tick step `k`, at a whole multiple of `S.E.Δ`, from
    the node state its wake stage leaves, its node state is `v`'s node state after the step, and two
    outcomes of that tick with one node state send the same objects (`hsend`), then every object of
    `out`'s list, signed by `v`, is in the sent log `x[k + 1].sent`. -/
theorem mem_sent_of_tick_of_state (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {k t : Nat} {v : V} {o : NamedObject V}
    (hl : x.lbl k = AtomicAction.tickAllAwake t)
    (haw : v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int))
    (hdvd : (t : Int) % S.E.Δ = 0)
    (hsend : ∀ out out' : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (t : Int) x[k] v) (t : Int) ⇢ out →
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (t : Int) x[k] v) (t : Int) ⇢ out' →
      out.1 = out'.1 → out.2 = out'.2)
    {out : M.N × List (NamedObject V)}
    (hout : M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (t : Int) x[k] v) (t : Int) ⇢ out)
    (hst : x[k + 1][v].st = out.1) (ho : o ∈ out.2) :
    (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  obtain ⟨-, w, tk, hwake, htick, hc⟩ := hs
  obtain ⟨out', hout', htkv⟩ := tick_outcome_of_step S Sched hwake htick haw hdvd ⟨out, hout⟩
  have hx1 : x[k + 1][v].st = (tk v).state := by
    have h2 : x[k + 1][v] = (tickAllAwakeUpdate Sched t x[k] w tk)[v] := by rw [hc]
    rw [h2, tickAllAwakeUpdate_getElem_awake (Finset.mem_sdiff.1 haw).1 (Finset.mem_sdiff.1 haw).2]
  rw [htkv] at hx1
  have h2 : out'.2 = out.2 := hsend out' out hout' hout (hx1.symm.trans hst)
  have hsent : x[k + 1].sent = x[k].sent
      + (Sched.awake (t : Int) \ Sched.adv (t : Int)).sum
          (fun q => ((w q).send + (tk q).send).map (SignedMsg.mk q)) := by
    rw [hc]; rfl
  rw [hsent]
  refine Multiset.mem_add.2 (Or.inr (Multiset.mem_sum.2 ⟨v, haw, ?_⟩))
  refine Multiset.mem_map.2 ⟨o, Multiset.mem_add.2 (Or.inr ?_), rfl⟩
  rw [htkv]
  exact Multiset.mem_coe.2 (h2 ▸ ho)

end

end DecoupledConsensusModel.Sts.Restated
