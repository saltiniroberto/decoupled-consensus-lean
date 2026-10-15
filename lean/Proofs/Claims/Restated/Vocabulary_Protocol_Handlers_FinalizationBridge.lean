import Proofs.Vocabulary.Protocol.Handlers.FinalizationBridge
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Model.Conditions.Vocabulary_Model_Execution_Run
import Proofs.Vocabulary.Protocol.ChainState.Chain
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# A body for the finalized block

Every store holds a body whose derived finalized block is the store's own, and root collision
freedom gives root injectivity on ancestors, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedFinalizationBridge
open Execution Protocol

/-- In every world `w₁` before the `i`-th event of `rho`, `v`'s store holds a body `D` whose derived
    finalized block is the store's finalized block, with derived height `h_F` less than the store's
    `h_max`. -/
theorem Vocabulary.Proofs.NamedFinalizationBridge.finalization_carrier_stateBefore (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V) : ∀ w₁ ∈ Record.stateBeforeOf M S rho i, 
    ∃ D : NamedBlock V, D ∈ (w₁ v).st.bodies ∧
      (M.derive_named S.E S.cfg D).F = (w₁ v).st.core.F ∧
      (M.derive_named S.E S.cfg D).h_F < (w₁ v).st.core.h_max :=
  facts.hdRun.finalization_carrier_stateBefore S rho i v
end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedFinalizationBridge
open Execution Protocol

/-- In every world `w₁` before time `t`, `v`'s store holds a body `D` whose derived finalized block
    is the store's finalized block, with derived height `h_F` less than the store's `h_max`. -/
theorem Vocabulary.Proofs.NamedFinalizationBridge.finalization_carrier_stateBeforeTime (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) : ∀ w₁ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t, 
    ∃ D : NamedBlock V, D ∈ (w₁ v).st.bodies ∧
      (M.derive_named S.E S.cfg D).F = (w₁ v).st.core.F ∧
      (M.derive_named S.E S.cfg D).h_F < (w₁ v).st.core.h_max :=
  facts.hdRun.finalization_carrier_stateBeforeTime S rho t v
end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedFinalizationBridge
open Execution Protocol

/-- For every path `W` of `rho`, if the run blocks read along `W` are free of root collisions and
    `A` and `B` are run blocks read along `W`, then their erasures are root-injective on their
    ancestors. -/
theorem Vocabulary.Proofs.NamedFinalizationBridge.rootInjectiveOnAncestors_of_collisionFree (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hroot : Restated.Vocabulary.Execution.NamedRootCollisionFree M S rho W)
    (A B : NamedBlock V) (hA : Restated.Vocabulary.Execution.NamedRun.blockInRun M S rho W A)
    (hB : Restated.Vocabulary.Execution.NamedRun.blockInRun M S rho W B) :
    Execution.RootInjectiveOnAncestors A.erase B.erase := by
  refine Proofs.ModelProperties.RootInjectiveOnAncestors.of_four ?_ ?_ ?_ ?_ <;>
    intro X Y hXZ hYW hroots
  · obtain ⟨X', hX'anc, hX'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift A hXZ
    obtain ⟨Y', hY'anc, hY'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift A hYW
    have hXr : X'.root = X.root := by
      rw [← Proofs.NamedWire.erase_root X', hX'erase]
    have hYr : Y'.root = Y.root := by
      rw [← Proofs.NamedWire.erase_root Y', hY'erase]
    have hEq := hroot.root_injective A B hA hB X' Y'
      (Or.inl hX'anc) (Or.inl hY'anc) (hXr.trans (hroots.trans hYr.symm))
    rw [← hX'erase, ← hY'erase, hEq]
  · obtain ⟨X', hX'anc, hX'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift A hXZ
    obtain ⟨Y', hY'anc, hY'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hYW
    have hXr : X'.root = X.root := by
      rw [← Proofs.NamedWire.erase_root X', hX'erase]
    have hYr : Y'.root = Y.root := by
      rw [← Proofs.NamedWire.erase_root Y', hY'erase]
    have hEq := hroot.root_injective A B hA hB X' Y'
      (Or.inl hX'anc) (Or.inr hY'anc) (hXr.trans (hroots.trans hYr.symm))
    rw [← hX'erase, ← hY'erase, hEq]
  · obtain ⟨X', hX'anc, hX'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hXZ
    obtain ⟨Y', hY'anc, hY'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift A hYW
    have hXr : X'.root = X.root := by
      rw [← Proofs.NamedWire.erase_root X', hX'erase]
    have hYr : Y'.root = Y.root := by
      rw [← Proofs.NamedWire.erase_root Y', hY'erase]
    have hEq := hroot.root_injective A B hA hB X' Y'
      (Or.inr hX'anc) (Or.inl hY'anc) (hXr.trans (hroots.trans hYr.symm))
    rw [← hX'erase, ← hY'erase, hEq]
  · obtain ⟨X', hX'anc, hX'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hXZ
    obtain ⟨Y', hY'anc, hY'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hYW
    have hXr : X'.root = X.root := by
      rw [← Proofs.NamedWire.erase_root X', hX'erase]
    have hYr : Y'.root = Y.root := by
      rw [← Proofs.NamedWire.erase_root Y', hY'erase]
    have hEq := hroot.root_injective A B hA hB X' Y'
      (Or.inr hX'anc) (Or.inr hY'anc) (hXr.trans (hroots.trans hYr.symm))
    rw [← hX'erase, ← hY'erase, hEq]

end

end DecoupledConsensusModel.Sts.Restated
