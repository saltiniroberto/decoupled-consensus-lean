import Proofs.Vocabulary.Protocol.Handlers.HMaxMonotone
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Internal_Definitions_NamedExecutionQueries
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Event
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Record.Wiring

/-!
# The height maximum never decreases

The height maximum `h_max` of a validator's store never decreases along a run, stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open Execution

private theorem step_h_max_mono' (facts : Record.Facts M) (S : Setup V) (w : V → M.N)
    (e : Record.Event V) (v : V) :
    ∀ w' ∈ Record.worldStepOf M S w e, (w v).st.core.h_max ≤ (w' v).st.core.h_max := by
  intro w' hw'
  cases e with
  | wake u t =>
    have hw'' : w' = Function.update w u (M.wake (w u)) := hw'
    subst hw''
    by_cases hu : u = v
    · subst u
      rw [Function.update_self, (facts.nd.wake_st_record _).1]
    · rw [Function.update_of_ne (Ne.symm hu)]
  | tick u t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
    rcases hw' with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
    · by_cases hu : u = v
      · subst u
        rw [Function.update_self]
        exact facts.nd.tick_h_max_mono S v (w v) t out hout
      · rw [Function.update_of_ne (Ne.symm hu)]
    · exact le_rfl
  | deliver u o t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
    rcases hw' with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
    · by_cases hu : u = v
      · subst u
        rw [Function.update_self]
        exact facts.nd.process_h_max_mono S (w v) o n' hn'
      · rw [Function.update_of_ne (Ne.symm hu)]
    · exact le_rfl

private theorem foldlM_h_max_mono' (facts : Record.Facts M) (S : Setup V) (v : V) :
    ∀ (l : List (Record.Event V)) (w : V → M.N),
      ∀ w₂ ∈ l.foldlM (Record.worldStepOf M S) w, (w v).st.core.h_max ≤ (w₂ v).st.core.h_max := by
  intro l
  induction l with
  | nil =>
    intro w w₂ hw₂
    obtain rfl := Set.mem_singleton_iff.mp hw₂
    exact le_rfl
  | cons e l ih =>
    intro w w₂ hw₂
    rw [List.foldlM_cons, Set.bind_def] at hw₂
    obtain ⟨w', hw', hw₂'⟩ := Set.mem_iUnion₂.mp hw₂
    exact (step_h_max_mono' facts S w e v w' hw').trans (ih w' w₂ hw₂')

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (ChainState)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

/-- For `n ≤ m`, every world `w₁` before the `n`-th event of `rho` and every world `w₂` the events
    `n` to `m - 1` can lead to from `w₁`, the height maximum of `v`'s store in `w₁` is at most the
    one in `w₂`. -/
theorem Vocabulary.Proofs.HealingSurface.stateBefore_hMax_mono (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) {n m : Nat} (hnm : n ≤ m) :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho n,
    ∀ w₂ ∈ ((rho.events.drop n).take (m - n)).foldlM (Record.worldStepOf M S) w₁,
    (w₁ v).st.core.h_max ≤ (w₂ v).st.core.h_max :=
  fun w₁ _ w₂ hw₂ => foldlM_h_max_mono' facts S v _ w₁ w₂ hw₂

end

end DecoupledConsensusModel.Sts.Restated
