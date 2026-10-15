import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.RunAll
import Model.Conditions.RunAll
import Model.Conditions.Sts_Interface
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Record.Wiring

/-!
# Blocks in play of the run built from an execution

A block the run built from an execution puts in play is a block the execution puts in play. Stated
over a model `M : Record.Model V`.
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

/-- Along the path `x` follows, every ancestor of a block delivered in the run of the first `n`
    steps, or held by a member of `H` at some index of that path, is an ancestor of a block in some
    sent log `x[k].sent` or held by a validator honest through some step, provided no member of `H`
    is in the adversary set at any time up to `x[n].time`. -/
theorem blockInLog_of_blockInRun_runAll_withHonest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    (H : Finset V) (n : Nat)
    (hH : ∀ v₀ ∈ H, Restated.HonestThrough M Sched x n v₀) {A : NamedBlock V}
    (hA : Restated.Vocabulary.Execution.NamedRun.blockInRun M (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n) A) :
    Restated.blockInLog M S Sched x A := by
  obtain ⟨B, hdir, hpre⟩ := hA
  refine ⟨B, ?_, hpre⟩
  rcases hdir with hobj | ⟨v₀, hv₀, i, hbodies⟩
  · -- the block is a delivery payload of the run, so a message of the sent log
    obtain ⟨e, hemem, heobj⟩ := List.mem_filterMap.1 hobj
    cases e with
    | wake v₁ t₁ => exact absurd heobj (by simp [Record.Event.object?])
    | tick v₁ t₁ => exact absurd heobj (by simp [Record.Event.object?])
    | deliver v₁ o₁ t₁ =>
        obtain ⟨k, -, hmem⟩ := Restated.exists_step_of_mem_runEvents facts S Sched x n hemem
        have hoo : o₁ = NamedObject.block B := by
          have hobj' : Record.Event.object? (Record.Event.deliver v₁ o₁ t₁) = some o₁ := rfl
          rw [hobj'] at heobj
          exact Option.some.inj heobj
        obtain ⟨m, hlbl, hmsg, -⟩ := Restated.deliver_of_mem_actionEventsOf hmem
        have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
        rw [hlbl] at hs
        exact Or.inl ⟨k, m, hs.1.1, by rw [hmsg, hoo]⟩
  · -- the block is in a member's store at some index of the path `x` follows, which is the store at a step `m ≤ n`
    have hstore : ∃ m ≤ n, (Restated.runAllPath M S Sched x v n i v₀).st = x[m][v₀].st.st := by
      rcases Restated.exists_veventsOf_eq_filter_take facts S Sched x v₀ n i with
        ⟨m, hm, hev⟩ | ⟨m, hm, t, hA, hev⟩
      · exact ⟨m, hm, by rw [Restated.runAllPath_eq facts S Sched x v n i v₀ hev]⟩
      · refine ⟨m, Nat.le_of_lt hm, ?_⟩
        rw [Restated.runAllPath_eq_wake facts S Sched x v n i v₀ hA hev]
        exact (facts.nd.wake_st_record _).1
    obtain ⟨m, hm, hst⟩ := hstore
    refine Or.inr ⟨m, v₀, ?_, ?_⟩
    · intro t' ht'
      have htime : (x[m].time : Int) ≤ (x[n].time : Int) := by
        exact_mod_cast Restated.time_mono facts S Sched x hm
      exact hH v₀ hv₀ t' (le_trans ht' htime)
    · show B ∈ (x[m][v₀].st).st.bodies
      rw [← hst]
      exact hbodies

end

end DecoupledConsensusModel.Sts.Restated
