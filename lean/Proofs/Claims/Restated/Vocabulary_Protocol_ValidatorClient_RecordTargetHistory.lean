import Proofs.Vocabulary.Protocol.ValidatorClient.RecordTargetHistory
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_Bridge
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Event
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Node
import Model.Record.Wiring

/-!
# The signing record across events

A helper about how the events of a run act on a validator's signing record, stated over a model
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
open Internal
open Execution

/-- An event that is not a tick of `v` leaves `v`'s signing record unchanged, in every world it can
    lead to. -/
private theorem rt_step_record (facts : Record.Facts M) (S : Setup V) (w w₂ : V → M.N)
    (e : Record.Event V) (v : V) (hw₂ : w₂ ∈ Record.worldStepOf M S w e)
    (hne : ∀ t : Time, e ≠ .tick v t) : (w₂ v).record = (w v).record := by
  cases e with
  | wake u t =>
    obtain rfl : w₂ = Function.update w u (M.wake (w u)) := hw₂
    by_cases hu : u = v
    · subst u
      rw [Function.update_self, (facts.nd.wake_st_record (w v)).2]
    · rw [Function.update_of_ne (Ne.symm hu)]
  | tick u t =>
    have hu : u ≠ v := fun h => hne t (by rw [h])
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw₂
    rcases hw₂ with ⟨out, -, rfl⟩ | ⟨-, rfl⟩
    · rw [Function.update_of_ne (Ne.symm hu)]
    · rfl
  | deliver u o t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw₂
    rcases hw₂ with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
    · by_cases hu : u = v
      · subst u
        rw [Function.update_self, facts.nd.process_record S (w v) o n' hn']
      · rw [Function.update_of_ne (Ne.symm hu)]
    · rfl

end

end DecoupledConsensusModel.Sts.Restated
