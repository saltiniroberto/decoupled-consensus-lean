import Proofs.Vocabulary.Protocol.Handlers.Proposer
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Vocabulary.Protocol.Handlers.Invariants
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Model.Conditions.Vocabulary_Protocol_Handlers_Proposer
import Model.Record.Wiring

/-!
# Every stored block names its slot's proposer

In every world of a run, every block of a validator's tree satisfies `ProposerOk`, stated over a
model `M : Record.Model V`.
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
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (Record)
open Internal
open Execution

private theorem step_proposerOk' (facts : Record.Facts M) (S : Setup V) (w : V → M.N)
    (e : Record.Event V) (h : ∀ u, Restated.Vocabulary.Proofs.HealingSurface.ProposerOk M S.E (w u).st.core) :
    ∀ w' ∈ Record.worldStepOf M S w e, ∀ u,
      Restated.Vocabulary.Proofs.HealingSurface.ProposerOk M S.E (w' u).st.core := by
  intro w' hw' u
  cases e with
  | wake x t =>
    simp only [Record.worldStepOf, Set.mem_singleton_iff] at hw'
    subst hw'
    by_cases hu : u = x
    · subst u
      rw [Function.update_self, (facts.nd.wake_st_record (w x)).1]
      exact h x
    · rw [Function.update_of_ne hu]
      exact h u
  | tick x t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
    rcases hw' with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
    · by_cases hu : u = x
      · subst u
        rw [Function.update_self]
        exact facts.nd.tick_proposerOk S x (w x) t out hout (h x)
      · rw [Function.update_of_ne hu]
        exact h u
    · exact h u
  | deliver x o t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
    rcases hw' with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
    · by_cases hu : u = x
      · subst u
        rw [Function.update_self]
        exact facts.nd.process_proposerOk S (w x) o n' hn' (h x)
      · rw [Function.update_of_ne hu]
        exact h u
    · exact h u

private theorem fold_proposerOk' (facts : Record.Facts M) (S : Setup V) :
    ∀ (l : List (Record.Event V)) (w : V → M.N),
      (∀ u, Restated.Vocabulary.Proofs.HealingSurface.ProposerOk M S.E (w u).st.core) →
      ∀ w₂ ∈ l.foldlM (Record.worldStepOf M S) w, ∀ u,
        Restated.Vocabulary.Proofs.HealingSurface.ProposerOk M S.E (w₂ u).st.core := by
  intro l
  induction l with
  | nil =>
    intro w h w₂ hw₂
    obtain rfl := Set.mem_singleton_iff.mp hw₂
    exact h
  | cons e l ih =>
    intro w h w₂ hw₂
    rw [List.foldlM_cons, Set.bind_def] at hw₂
    obtain ⟨w', hw', hw₂'⟩ := Set.mem_iUnion₂.mp hw₂
    exact ih w' (step_proposerOk' facts S w e h w' hw') w₂ hw₂'

/-- For every `n`, in every world before the `n`-th event of `ρ`, every block of the tree of `v`'s
    core store is the genesis block or was proposed by its slot's proposer. -/
theorem Vocabulary.Proofs.HealingSurface.proposerOk_stateBefore (facts : Record.Facts M) (S : Setup V) (ρ : Record.Run V) (v : V) :
    ∀ n : Nat, ∀ w ∈ Record.stateBeforeOf M S ρ n,
      Restated.Vocabulary.Proofs.HealingSurface.ProposerOk M S.E (w v).st.core := by
  intro n w hw
  refine fold_proposerOk' facts S (ρ.events.take n) (fun u => M.initial S u) (fun u => ?_) w hw v
  intro B hB
  left
  change B ∈ (M.initial S u : M.N).st.core.T at hB
  rw [facts.nd.initial_st, facts.hd.initial_core_T] at hB
  exact Finset.mem_singleton.mp hB

end

end DecoupledConsensusModel.Sts.Restated
