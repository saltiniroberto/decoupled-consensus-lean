import Proofs.Vocabulary.Protocol.Handlers.HMaxCore
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Vocabulary.Protocol.ChainState.Chain
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Vocabulary.Protocol.ChainState.DerivationGeometry
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_HMaxMonotone
import Proofs.Vocabulary.Protocol.Handlers.Invariants2
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Event
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Protocol_Handlers_HMaxCore
import Model.Record.Wiring

/-!
# Tree heights and the height maximum

The bound of tree heights by `h_max` carries across handlers that keep the tree, and one event
raises `h_max` by at most one, stated over a model `M : Record.Model V`.
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
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

/-- If `st'` has the same tree, chain states and `h_max` as `st`, and every block of `st`'s tree has
    height at most `st.h_max`, the same holds for `st'`. -/
theorem Vocabulary.Proofs.HealingSurface.treeHeightsLeHMax_of_eq (facts : Record.Facts M) {st st' : M.S}
    (hT : st'.T = st.T) (hSigma : st'.σ = st.σ)
    (hMax : st'.h_max = st.h_max) (h : Restated.Vocabulary.Proofs.HealingSurface.TreeHeightsLeHMax M st) :
    Restated.Vocabulary.Proofs.HealingSurface.TreeHeightsLeHMax M st' := by
  intro B hB
  rw [hT] at hB
  rw [hSigma, hMax]
  exact h B hB

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

/-- If every block of `v`'s tree in `w` has a chain-state height at most `v`'s `h_max`, then in
    every world one event can lead to from `w`, `v`'s `h_max` is at most its `h_max` in `w` plus
    one. -/
theorem Vocabulary.Proofs.HealingSurface.worldStep_h_max_le_succ (facts : Record.Facts M)
    (S : Setup V) (w : (V → M.N)) (e : Record.Event V) (v : V)
    (hbound : Restated.Vocabulary.Proofs.HealingSurface.TreeHeightsLeHMax M (w v).st.core) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.World.step M S w e,
    (w₁ v).st.core.h_max ≤ (w v).st.core.h_max + 1 := by
  intro w₁ hw₁
  cases e with
  | wake u t =>
      obtain rfl : w₁ = Function.update w u (M.wake (w u)) := hw₁
      by_cases hu : v = u
      · subst hu
        rw [Function.update_self, (facts.nd.wake_st_record (w v)).1]
        exact Nat.le_succ _
      · rw [Function.update_of_ne hu]
        exact Nat.le_succ _
  | tick u t =>
      simp only [Restated.Vocabulary.Execution.World.step, Record.worldStepOf, Set.mem_setOf_eq] at hw₁
      rcases hw₁ with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
      · by_cases hu : v = u
        · subst hu
          rw [Function.update_self]
          exact facts.nd.node_tick_h_max_le_succ S v (w v) t hbound out hout
        · rw [Function.update_of_ne hu]
          exact Nat.le_succ _
      · exact Nat.le_succ _
  | deliver u o t =>
      simp only [Restated.Vocabulary.Execution.World.step, Record.worldStepOf, Set.mem_setOf_eq] at hw₁
      rcases hw₁ with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
      · by_cases hu : v = u
        · subst hu
          rw [Function.update_self]
          exact facts.nd.node_process_h_max_le_succ S (w v) o hbound n' hn'
        · rw [Function.update_of_ne hu]
          exact Nat.le_succ _
      · exact Nat.le_succ _

end

end DecoupledConsensusModel.Sts.Restated
