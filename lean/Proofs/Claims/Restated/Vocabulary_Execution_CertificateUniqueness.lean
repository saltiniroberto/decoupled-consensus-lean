import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.RunVocabulary
import Model.Record.Wiring

/-!
# Every delivered object is processed

A theorem over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: along every path
`W` of a run, every object the run delivers is processed by some validator.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution

/-- For every path `W` of `rho`, every object among those `rho` delivers is processed, along `W`, by
    some validator `u` at some time `t`. -/
theorem Vocabulary.Proofs.HealingSurface.exists_processes_of_mem_objects (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) {o : Object V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (h : o ∈ Restated.objects rho) :
    ∃ (u : V) (t : Time), Restated.Vocabulary.Execution.NamedRun.processes M S rho W u o t := by
  obtain ⟨e, hmem, he⟩ := List.mem_filterMap.mp h
  cases e with
  | wake u t =>
      have hnone : (none : Option (Object V)) = some o := he
      exact absurd hnone (by simp)
  | tick u t =>
      have hnone : (none : Option (Object V)) = some o := he
      exact absurd hnone (by simp)
  | deliver u p t =>
      have heq : p = o := Option.some.inj he
      subst heq
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hmem
      exact ⟨u, t, Or.inr ⟨i, hi⟩⟩

end

end DecoupledConsensusModel.Sts.Restated
