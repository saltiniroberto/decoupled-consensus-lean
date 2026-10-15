import Proofs.Vocabulary.Protocol.ValidatorClient.Schedule
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Event
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Node
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Record.Wiring

/-!
# Attestation sets along a run

The attestation set a validator holds for a round only grows along a run, stated over a model
`M : Record.Model V` and its facts `facts : Record.Facts M`.
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
open DecoupledConsensusModel.Proofs.HealingLemmas
open Protocol (HealConfig)
open Internal
open Execution

/-- For every world `w₁` before the `i`-th event of `ρ`, every `j ≥ i`, and every world `w₂` the
    events `i` to `j - 1` of `ρ` can lead to from `w₁`, every round-`r` attestation in `v`'s
    attestation set in `w₁` is in `v`'s attestation set in `w₂`. -/
theorem Vocabulary.Proofs.HealingLemmas.stateBefore_sg_pool_subset (facts : Record.Facts M)
    (S : Setup V) (ρ : Record.Run V) (v : V) (r : Round)
    {i : Nat} : ∀ w₁ ∈ Record.stateBeforeOf M S ρ i,
    ∀ j : Nat, i ≤ j →
      ∀ w₂ ∈ ((ρ.events.drop i).take (j - i)).foldlM (Record.worldStepOf M S) w₁,
      (w₁ v).st.sg_pool r ⊆ (w₂ v).st.sg_pool r := by
  intro w₁ _ j _
  suffices h : ∀ (l : List (Record.Event V)) (w : V → M.N),
      ∀ w₂ ∈ l.foldlM (Record.worldStepOf M S) w, (w v).st.sg_pool r ⊆ (w₂ v).st.sg_pool r from
    h _ w₁
  intro l
  induction l with
  | nil =>
      intro w w₂ hw₂
      rw [Set.mem_singleton_iff.mp hw₂]
  | cons e l ih =>
      intro w w₂ hw₂
      rw [List.foldlM_cons, Set.bind_def] at hw₂
      obtain ⟨w', hw', hw₂'⟩ := Set.mem_iUnion₂.mp hw₂
      refine Finset.Subset.trans ?_ (ih w' w₂ hw₂')
      cases e with
      | wake u t =>
          simp only [Record.worldStepOf, Set.mem_singleton_iff] at hw'
          subst hw'
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
              exact facts.nd.sg_pool_subset_on_tick_emit S v (w v) t r out hout
            · rw [Function.update_of_ne (Ne.symm hu)]
          · exact Finset.Subset.refl _
      | deliver u o t =>
          simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
          rcases hw' with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
          · by_cases hu : u = v
            · subst u
              rw [Function.update_self]
              exact facts.nd.sg_pool_subset_process S (w v) o r n' hn'
            · rw [Function.update_of_ne (Ne.symm hu)]
          · exact Finset.Subset.refl _

end

end DecoupledConsensusModel.Sts.Restated
