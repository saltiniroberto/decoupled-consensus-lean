import Proofs.Vocabulary.Protocol.Handlers.StoreRoots
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Record.Wiring

/-!
# The FG root is in the tree

The FG root of a store whose roots are in its tree is in the tree, and setting the clock keeps the
store-roots invariant, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedStoreRoots
open DecoupledConsensusModel Protocol

/-- If `st` satisfies `RootsInTree`, the FG root of `st`'s core store is in its tree. -/
theorem Vocabulary.Proofs.NamedStoreRoots.fg_root_mem (facts : Record.Facts M) (st : M.NS) (h : Restated.Vocabulary.Proofs.NamedStoreRoots.RootsInTree M st) :
    M.get_fg_root (M.toHealing st.core).toFG ∈ st.core.T := by
  by_cases hj : st.core.h_max = st.core.h_j + 1
  · rw [facts.fc.get_fg_root_toHealing_of_eq st.core hj]
    exact h.2
  · rw [facts.fc.get_fg_root_toHealing_of_ne st.core hj]
    exact h.1

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedStoreRoots
open DecoupledConsensusModel Protocol

/-- If `st` satisfies `Invariant`, so does `st` with its clock set to `t`. -/
theorem Vocabulary.Proofs.NamedStoreRoots.invariant_clock (facts : Record.Facts M) (E : Env V) (cfg : HeightConfig) (st : M.NS)
    (t : Time) (h : Restated.Vocabulary.Proofs.NamedStoreRoots.Invariant M E cfg st) :
    Restated.Vocabulary.Proofs.NamedStoreRoots.Invariant M E cfg (M.ns_setClock E st t) :=
  by
  obtain ⟨⟨hT, hU, hP, hS, hD⟩, hF, hJ⟩ := h
  have hb := facts.hd.Sts_setClock_bodies E st t
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · show (M.ns_setClock E st t).core.T = (M.ns_setClock E st t).bodies.image NamedBlock.erase
    rw [facts.hd.Sts_setClock_core_T, hb]
    exact hT
  · show ∀ A ∈ (M.ns_setClock E st t).bodies, ∀ B ∈ (M.ns_setClock E st t).bodies,
      A.erase = B.erase → A = B
    rw [hb]
    exact hU
  · show NamedBlock.genesis ∈ (M.ns_setClock E st t).bodies ∧
      ∀ B ∈ (M.ns_setClock E st t).bodies, B.parent ∈ (M.ns_setClock E st t).bodies
    rw [hb]
    exact hP
  · intro r
    rw [facts.hd.setClock_core_sg_votes E st t, facts.hd.setClock_sg_rows E st t]
    exact hS r
  · intro B hB
    rw [hb] at hB
    rw [facts.hd.Sts_setClock_core_σ]
    exact hD B hB
  · show (M.ns_setClock E st t).core.F ∈ (M.ns_setClock E st t).core.T
    rw [facts.hd.setClock_core_F, facts.hd.Sts_setClock_core_T]
    exact hF
  · show (M.ns_setClock E st t).core.J ∈ (M.ns_setClock E st t).core.T
    rw [facts.hd.setClock_core_J, facts.hd.Sts_setClock_core_T]
    exact hJ

end

end DecoupledConsensusModel.Sts.Restated
