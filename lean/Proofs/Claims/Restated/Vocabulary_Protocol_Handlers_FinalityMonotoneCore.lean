import Proofs.Vocabulary.Protocol.Handlers.FinalityMonotoneCore
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Event
import Model.Record.Wiring

/-!
# The finalized block only moves forward

The finalized block of a validator's store moves to a descendant, or stays, at every event of a run,
stated over a model `M : Record.Model V`.
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
open Protocol (HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

/-- In every world one event `e` can lead to from `w`, `v`'s finalized block is a descendant of, or
    is, its finalized block in `w`. -/
theorem Vocabulary.Protocol.step_F_mono (facts : Record.Facts M)
    (S : Setup V) (w : (V → M.N)) (e : Record.Event V) (v : V) : ∀ w₁ ∈ Restated.Vocabulary.Execution.World.step M S w e, 
    Block.Preceq (w v).st.core.F (w₁ v).st.core.F := by
  intro w₁ hw₁
  cases e with
  | wake u t =>
      simp only [Restated.Vocabulary.Execution.World.step, Record.worldStepOf,
        Set.mem_singleton_iff] at hw₁
      subst hw₁
      by_cases hu : u = v
      · subst u
        rw [Function.update_self, (facts.nd.wake_st_record (w v)).1]
        exact Proofs.ModelProperties.Preceq_self _
      · rw [Function.update_of_ne (Ne.symm hu)]
        exact Proofs.ModelProperties.Preceq_self _
  | tick u t =>
      simp only [Restated.Vocabulary.Execution.World.step, Record.worldStepOf, Set.mem_setOf_eq] at hw₁
      rcases hw₁ with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
      · by_cases hu : u = v
        · subst u
          rw [Function.update_self]
          exact facts.nd.node_tick_F S v (w v) t out hout
        · rw [Function.update_of_ne (Ne.symm hu)]
          exact Proofs.ModelProperties.Preceq_self _
      · exact Proofs.ModelProperties.Preceq_self _
  | deliver u o t =>
      simp only [Restated.Vocabulary.Execution.World.step, Record.worldStepOf, Set.mem_setOf_eq] at hw₁
      rcases hw₁ with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
      · by_cases hu : u = v
        · subst u
          rw [Function.update_self]
          exact facts.nd.node_process_F S (w v) o n' hn'
        · rw [Function.update_of_ne (Ne.symm hu)]
          exact Proofs.ModelProperties.Preceq_self _
      · exact Proofs.ModelProperties.Preceq_self _

/-- For every world `w₁` before the `m`-th event of `rho`, and every world `w₂` that the events `m`
    to `n - 1` of `rho` can lead to from `w₁`, the finalized block of `v`'s store in `w₁` is an
    ancestor of, or is, the finalized block of `v`'s store in `w₂`. -/
theorem Vocabulary.Protocol.stateBefore_F_mono (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) {m n : Nat} (hmn : m ≤ n) :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho m,
    ∀ w₂ ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) w₁,
    Block.Preceq (w₁ v).st.core.F (w₂ v).st.core.F := by
  intro w₁ _
  suffices h : ∀ (l : List (Record.Event V)) (w : V → M.N),
      ∀ w₂ ∈ l.foldlM (Record.worldStepOf M S) w,
        Block.Preceq (w v).st.core.F (w₂ v).st.core.F from h _ w₁
  intro l
  induction l with
  | nil =>
      intro w w₂ hw₂
      rw [Set.mem_singleton_iff.mp hw₂]
      exact Proofs.ModelProperties.Preceq_self _
  | cons e l ih =>
      intro w w₂ hw₂
      rw [List.foldlM_cons, Set.bind_def] at hw₂
      obtain ⟨w', hw', hw₂'⟩ := Set.mem_iUnion₂.mp hw₂
      exact Proofs.ModelProperties.Preceq_trans
        (Restated.Vocabulary.Protocol.step_F_mono facts S w e v w' hw') (ih w' w₂ hw₂')

end

end DecoupledConsensusModel.Sts.Restated
