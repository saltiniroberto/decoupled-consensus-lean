import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.RunAll
import Model.Conditions.RunAll
import Model.Record.Wiring

/-!
# The run's events are sorted

What the events of one step are, and that the events of the run built from an execution are in
non-decreasing order of key. Stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The events of step `k` are wakes and ticks at `x[k].time + 1` from a `tickAllAwake` step, or
    deliveries at `x[k].time` from a delivery step. -/
theorem time_phase_of_mem_stepEvents (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (k : Nat) {e : Record.Event V}
    (he : e ∈ Restated.stepEvents M S Sched x k) :
    ((∃ t : Nat, x.lbl k = AtomicAction.tickAllAwake t) ∧
        Record.Event.phase e = 0 ∧ Record.Event.time e = ((x[k].time + 1 : Nat) : Int)) ∨
      ((∃ (v : V) (m : SignedMsg V (NamedObject V)), x.lbl k = AtomicAction.deliver v m) ∧
        Record.Event.phase e = 1 ∧ Record.Event.time e = (x[k].time : Int)) := by
  obtain ⟨v₀, -, hmem⟩ := List.mem_flatMap.1 he
  cases e with
  | wake v₁ t' =>
      obtain ⟨τ, hlbl, hτ, -, -, -⟩ := Restated.wake_of_mem_actionEventsOf hmem
      have ht := (Restated.tickAllAwake_time facts S Sched x hlbl).1
      refine Or.inl ⟨⟨τ, hlbl⟩, rfl, ?_⟩
      show t' = ((x[k].time + 1 : Nat) : Int)
      rw [← hτ, ht]
  | tick v₁ t' =>
      obtain ⟨τ, hlbl, hτ, -⟩ := Restated.tickAllAwake_of_mem_actionEventsOf hmem
      have ht := (Restated.tickAllAwake_time facts S Sched x hlbl).1
      refine Or.inl ⟨⟨τ, hlbl⟩, rfl, ?_⟩
      show t' = ((x[k].time + 1 : Nat) : Int)
      rw [← hτ, ht]
  | deliver v₁ o t' =>
      obtain ⟨m, hlbl, -, ht⟩ := Restated.deliver_of_mem_actionEventsOf hmem
      exact Or.inr ⟨⟨v₁, m, hlbl⟩, rfl, ht⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- An event of step `k` has key at most the key of any event of a step `k'` with `k ≤ k'`. -/
theorem key_le_of_mem_stepEvents (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {k k' : Nat} (hkk : k ≤ k') {e f : Record.Event V}
    (he : e ∈ Restated.stepEvents M S Sched x k) (hf : f ∈ Restated.stepEvents M S Sched x k') :
    Record.Event.key e ≤ Record.Event.key f := by
  show toLex (Record.Event.time e, Record.Event.phase e)
    ≤ toLex (Record.Event.time f, Record.Event.phase f)
  refine Prod.Lex.toLex_le_toLex.2 ?_
  have hcast : ∀ {a b : Nat}, a < b → (a : Int) < (b : Int) := fun h => by exact_mod_cast h
  rcases Nat.eq_or_lt_of_le hkk with hk | hk
  · subst hk
    rcases Restated.time_phase_of_mem_stepEvents facts S Sched x k he with
        ⟨⟨t, hl⟩, hpe, hte⟩ | ⟨⟨v, m, hl⟩, hpe, hte⟩ <;>
      rcases Restated.time_phase_of_mem_stepEvents facts S Sched x k hf with
        ⟨⟨t', hl'⟩, hpf, htf⟩ | ⟨⟨v', m', hl'⟩, hpf, htf⟩
    · exact Or.inr ⟨by rw [hte, htf], by rw [hpe, hpf]⟩
    · rw [hl] at hl'; exact absurd hl' (by simp)
    · rw [hl] at hl'; exact absurd hl' (by simp)
    · exact Or.inr ⟨by rw [hte, htf], by rw [hpe, hpf]⟩
  · have h1 : x[k + 1].time ≤ x[k'].time := Restated.time_mono facts S Sched x hk
    have h2 : x[k].time ≤ x[k + 1].time := Restated.time_mono facts S Sched x (Nat.le_succ k)
    have h0 : x[k].time ≤ x[k'].time := Nat.le_trans h2 h1
    rcases Restated.time_phase_of_mem_stepEvents facts S Sched x k he with
        ⟨⟨t, hl⟩, hpe, hte⟩ | ⟨-, hpe, hte⟩
    · obtain ⟨ht1, ht2⟩ := Restated.tickAllAwake_time facts S Sched x hl
      have hk1 : x[k].time + 1 ≤ x[k'].time := by rw [ht1, ← ht2]; exact h1
      rcases Restated.time_phase_of_mem_stepEvents facts S Sched x k' hf with
          ⟨-, hpf, htf⟩ | ⟨-, hpf, htf⟩
      · exact Or.inl (by rw [hte, htf]; exact hcast (Nat.lt_succ_of_le hk1))
      · rcases Nat.lt_or_eq_of_le hk1 with hlt | heq
        · exact Or.inl (by rw [hte, htf]; exact hcast hlt)
        · exact Or.inr ⟨by rw [hte, htf, heq], by rw [hpe]; exact Nat.zero_le _⟩
    · rcases Restated.time_phase_of_mem_stepEvents facts S Sched x k' hf with
          ⟨-, hpf, htf⟩ | ⟨-, hpf, htf⟩
      · exact Or.inl (by rw [hte, htf]; exact hcast (Nat.lt_succ_of_le h0))
      · rcases Nat.lt_or_eq_of_le h0 with hlt | heq
        · exact Or.inl (by rw [hte, htf]; exact hcast hlt)
        · exact Or.inr ⟨by rw [hte, htf, heq], by rw [hpe, hpf]⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Within the events of step `k`, keys never decrease. -/
theorem pairwise_key_stepEvents (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (k : Nat) :
    (Restated.stepEvents M S Sched x k).Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f) :=
  List.pairwise_iff_forall_sublist.2 (fun {e f} hs => by
    have hmem := hs.subset
    exact Restated.key_le_of_mem_stepEvents facts S Sched x (le_refl k)
      (hmem (List.mem_cons_self ..)) (hmem (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every `n`, the events of the first `n` steps, over every validator, are in non-decreasing
    order of key. -/
theorem sorted_runEvents (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) :
    ∀ n : Nat, (Restated.runEvents M S Sched x n).Pairwise (fun e f => e.key ≤ f.key)
  | 0 => List.Pairwise.nil
  | n + 1 => by
      rw [show Restated.runEvents M S Sched x (n + 1)
            = Restated.runEvents M S Sched x n ++ Restated.stepEvents M S Sched x n from rfl]
      refine List.pairwise_append.2 ⟨sorted_runEvents facts S Sched x n,
        Restated.pairwise_key_stepEvents facts S Sched x n, ?_⟩
      intro e he f hf
      obtain ⟨k, hk, hmem⟩ := Restated.exists_step_of_mem_runEvents facts S Sched x n he
      exact Restated.key_le_of_mem_stepEvents facts S Sched x (Nat.le_of_lt hk)
        (Restated.mem_stepEvents_of_mem_actionEvents facts S Sched x k hmem) hf

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Whatever honest set `H` is declared, the events of `runAll` with honest set `H` are in
    non-decreasing order of key. -/
theorem sorted_runAll_withHonest_events (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (H : Finset V) (n : Nat) :
    ({ Restated.runAll M S Sched x v n with honest := H } : Record.Run V).events.Pairwise
      (fun e f => Record.Event.key e ≤ Record.Event.key f) :=
  Restated.sorted_runEvents facts S Sched x n

end

end DecoupledConsensusModel.Sts.Restated
