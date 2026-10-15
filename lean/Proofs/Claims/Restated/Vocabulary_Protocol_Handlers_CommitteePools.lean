import Proofs.Vocabulary.Protocol.Handlers.CommitteePools
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Internal_Definitions_NamedExecutionQueries
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Event
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_FinalityGadget_Crossing
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Protocol_Handlers_CommitteePools
import Model.Record.Wiring

/-!
# Committee-typed Goldfish pools

Every validator's Goldfish pools hold only votes of the slot's committee, in the initial world and
after every event of a run, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.CommitteePools

/-- The initial world satisfies `NamedWorldInitPoolsQuery`: every validator's Goldfish pools are
    committee-typed. -/
theorem Vocabulary.Protocol.CommitteePools.world_init (facts : Record.Facts M) (S : Execution.Setup V) :
    Restated.Vocabulary.Execution.NamedWorldInitPoolsQuery M S := by
  intro v
  show Restated.Vocabulary.Execution.CorePools M S (M.initial S v).st.core
  rw [facts.nd.initial_st S v, facts.hd.initial_core]
  exact facts.sto.committeePools_init S.E

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.CommitteePools

/-- One world event keeps every validator's Goldfish pools committee-typed
    (`NamedWorldStepPoolsQuery`). -/
theorem Vocabulary.Protocol.CommitteePools.world_step (facts : Record.Facts M) (S : Execution.Setup V) :
    Restated.Vocabulary.Execution.NamedWorldStepPoolsQuery M S := by
  intro w e w' hw' h x
  cases e with
  | wake v t =>
      simp only [Record.worldStepOf, Set.mem_singleton_iff] at hw'
      subst hw'
      by_cases hx : x = v
      · subst hx
        simp only [Function.update_apply, if_pos]
        rw [(facts.nd.wake_st_record (w x)).1]
        exact h x
      · simp only [Function.update_apply, if_neg hx]
        exact h x
  | tick v t =>
      simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
      rcases hw' with ⟨out, hout, rfl⟩ | ⟨_, rfl⟩
      · by_cases hx : x = v
        · subst hx
          simp only [Function.update_apply, if_pos]
          exact facts.hd.committeePools_on_tick_emit S x (w x) t out hout (h x)
        · simp only [Function.update_apply, if_neg hx]
          exact h x
      · exact h x
  | deliver v o t =>
      simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
      rcases hw' with ⟨n', hn', rfl⟩ | ⟨_, rfl⟩
      · by_cases hx : x = v
        · subst hx
          simp only [Function.update_apply, if_pos]
          exact facts.nd.committeePools_process S (w x) o n' hn' (h x)
        · simp only [Function.update_apply, if_neg hx]
          exact h x
      · exact h x

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.CommitteePools

/-- If every validator's core store in `w` has committee-typed Goldfish pools, then so does every
    validator's core store in every world the events of `l` can lead to from `w`. -/
theorem Vocabulary.Protocol.CommitteePools.foldl_world_step (facts : Record.Facts M) (S : Execution.Setup V)
    (l : List (Record.Event V)) {w : (V → M.N)}
    (h : Restated.Vocabulary.Protocol.CommitteePools.WorldCommitteePools M S w) :
    ∀ w' ∈ l.foldlM (Restated.Vocabulary.Execution.World.step M S) w,
      Restated.Vocabulary.Protocol.CommitteePools.WorldCommitteePools M S w' := by
  induction l generalizing w with
  | nil =>
      intro w' hw'
      obtain rfl := hw'
      exact h
  | cons e l ih =>
      intro w' hw'
      rw [List.foldlM_cons, Set.bind_def] at hw'
      obtain ⟨w₁, hw₁, hw'⟩ := Set.mem_iUnion₂.mp hw'
      exact ih (Restated.Vocabulary.Protocol.CommitteePools.world_step facts S w e w₁ hw₁ h) w' hw'

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.CommitteePools

/-- The run `rho` satisfies `NamedRunPoolsQuery`: the worlds it reads have committee-typed Goldfish
    pools. -/
theorem Vocabulary.Protocol.CommitteePools.run_pools (facts : Record.Facts M) (S : Execution.Setup V) (rho : Record.Run V) :
    Restated.Vocabulary.Execution.NamedRunPoolsQuery M S rho :=
  ⟨fun i w hw v => Restated.Vocabulary.Protocol.CommitteePools.foldl_world_step facts S (rho.events.take i)
      (Restated.Vocabulary.Protocol.CommitteePools.world_init facts S) w hw v,
    fun t w hw v => Restated.Vocabulary.Protocol.CommitteePools.foldl_world_step facts S
      (rho.events.filter (fun e => decide (e.time ≤ t)))
      (Restated.Vocabulary.Protocol.CommitteePools.world_init facts S) w hw v,
    fun t w hw v => Restated.Vocabulary.Protocol.CommitteePools.foldl_world_step facts S
      (rho.events.filter (fun e => decide (e.time < t)))
      (Restated.Vocabulary.Protocol.CommitteePools.world_init facts S) w hw v,
    fun w hw v => Restated.Vocabulary.Protocol.CommitteePools.foldl_world_step facts S rho.events
      (Restated.Vocabulary.Protocol.CommitteePools.world_init facts S) w hw v⟩

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.CommitteePools

/-- In every world before the `i`-th event of `rho`, `v`'s core store has committee-typed Goldfish
    pools. -/
theorem Vocabulary.Protocol.CommitteePools.stateBefore (facts : Record.Facts M) (S : Execution.Setup V)
    (rho : Record.Run V) (v : V) (i : Nat) : ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    Restated.Vocabulary.Execution.CorePools M S (w₁ v).st.core :=
  fun w₁ hw₁ => (Restated.Vocabulary.Protocol.CommitteePools.run_pools facts S rho).1 i w₁ hw₁ v

end

end DecoupledConsensusModel.Sts.Restated
