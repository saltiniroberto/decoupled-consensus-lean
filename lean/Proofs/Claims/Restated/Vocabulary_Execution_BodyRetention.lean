import Proofs.Vocabulary.Execution.BodyRetention
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Model.Record.Wiring

/-!
# Held bodies are kept

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: no event removes
a named block a validator holds among its bodies, for one event and across event-index prefixes.
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
open DecoupledConsensusModel.Proofs.NamedBodyRetention
open Execution

/-- For every world `w'` that the event `e` can lead to from the world `w`, every named block `v`
    holds in `w` it also holds in `w'`. -/
theorem Vocabulary.Proofs.NamedBodyRetention.step_bodies_subset (facts : Record.Facts M) (S : Setup V) (w : (V → M.N))
    (e : Record.Event V) (v : V) :
    ∀ w' ∈ Record.worldStepOf M S w e, (w v).st.bodies ⊆ (w' v).st.bodies :=
  facts.nd.step_bodies_subset S w e v

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedBodyRetention
open Execution

/-- For `i ≤ j`, for every world `w₁` that can hold before the `i`-th event of `rho`, and every
    world `w₂` that the events `i` to `j - 1` of `rho` can lead to from `w₁`, every named block `v`
    holds in `w₁` it also holds in `w₂`. -/
theorem Vocabulary.Proofs.NamedBodyRetention.stateBefore_bodies_mono (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (v : V)
    {i j : Nat} (hij : i ≤ j) :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    ∀ w₂ ∈ ((rho.events.drop i).take (j - i)).foldlM (Record.worldStepOf M S) w₁,
    (w₁ v).st.bodies ⊆ (w₂ v).st.bodies := by
  intro w₁ _
  suffices h : ∀ (l : List (Record.Event V)) (w : V → M.N),
      ∀ w₂ ∈ l.foldlM (Record.worldStepOf M S) w, (w v).st.bodies ⊆ (w₂ v).st.bodies from h _ w₁
  intro l
  induction l with
  | nil =>
      intro w w₂ hw₂
      rw [Set.mem_singleton_iff.mp hw₂]
  | cons e l ih =>
      intro w w₂ hw₂
      rw [List.foldlM_cons, Set.bind_def] at hw₂
      obtain ⟨w', hw', hw₂'⟩ := Set.mem_iUnion₂.mp hw₂
      exact (Restated.Vocabulary.Proofs.NamedBodyRetention.step_bodies_subset facts S w e v w' hw').trans
        (ih w' w₂ hw₂')

end

end DecoupledConsensusModel.Sts.Restated
