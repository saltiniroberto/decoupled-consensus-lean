import Proofs.Vocabulary.Protocol.Evidence.ProvenanceBridge
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_FinalizationBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_JustificationCarrier
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Model.Record.Wiring

/-!
# Finalized and justified blocks are recomputed on retained bodies

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: in every world
before a time or an event of a run, a validator's finalized and justified blocks are recomputed on a
named body its store holds, and its store has named provenance.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Bridges
open Internal Execution Protocol

/-- In every world `w₁` before time `t` of `rho`, `v`'s store holds a named body `D` whose derived
    finalized block is the store's finalized block, with a derived finalized height less than the
    store's maximum height. -/
theorem Vocabulary.Proofs.Bridges.storeFinalizationOnChain_stateBeforeTime (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (t : Time) (v : V) : ∀ w₁ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t, 
    ∃ D : NamedBlock V, D ∈ (w₁ v).st.bodies ∧
      (M.derive_named S.E S.cfg D).F = (w₁ v).st.core.F ∧
      (M.derive_named S.E S.cfg D).h_F < (w₁ v).st.core.h_max :=
  Restated.Vocabulary.Proofs.NamedFinalizationBridge.finalization_carrier_stateBeforeTime facts S rho t v

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Bridges
open Internal Execution Protocol

/-- In every world `w₁` before the `i`-th event of `rho`, `v`'s store holds a named body `D` whose
    derived finalized block is the store's finalized block, with a derived finalized height less
    than the store's maximum height. -/
theorem Vocabulary.Proofs.Bridges.storeFinalizationOnChain_stateBefore (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (i : Nat) (v : V) : ∀ w₁ ∈ Record.stateBeforeOf M S rho i, 
    ∃ D : NamedBlock V, D ∈ (w₁ v).st.bodies ∧
      (M.derive_named S.E S.cfg D).F = (w₁ v).st.core.F ∧
      (M.derive_named S.E S.cfg D).h_F < (w₁ v).st.core.h_max :=
  Restated.Vocabulary.Proofs.NamedFinalizationBridge.finalization_carrier_stateBefore facts S rho i v

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Bridges
open Internal Execution Protocol

/-- In every world before time `t` of `rho`, `v`'s store satisfies
    `Restated.Vocabulary.Proofs.Bridges.NamedStoreJustificationOnChain`: its justified block is
    recomputed on a body the store retains. -/
theorem Vocabulary.Proofs.Bridges.storeJustificationOnChain_stateBeforeTime (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (t : Time) (v : V) : ∀ w₁ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t, 
    Restated.Vocabulary.Proofs.Bridges.NamedStoreJustificationOnChain M S (w₁ v).st :=
  Restated.Vocabulary.Proofs.NamedJustificationCarrier.justification_carrier_stateBeforeTime facts S rho t v

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Bridges
open Internal Execution Protocol

/-- In every world before the `i`-th event of `rho`, `v`'s store satisfies
    `Restated.Vocabulary.Proofs.Bridges.NamedStoreJustificationOnChain`: its justified block is
    recomputed on a body the store retains. -/
theorem Vocabulary.Proofs.Bridges.storeJustificationOnChain_stateBefore (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (i : Nat) (v : V) : ∀ w₁ ∈ Record.stateBeforeOf M S rho i, 
    Restated.Vocabulary.Proofs.Bridges.NamedStoreJustificationOnChain M S (w₁ v).st :=
  Restated.Vocabulary.Proofs.NamedJustificationCarrier.justification_carrier_stateBefore facts S rho i v

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Bridges
open Internal Execution Protocol

/-- In every world before the `i`-th event of `rho`, `v`'s store satisfies
    `Restated.Vocabulary.Proofs.Bridges.NamedProvenance`. -/
theorem Vocabulary.Proofs.Bridges.namedProvenance_stateBefore (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V) : ∀ w₁ ∈ Record.stateBeforeOf M S rho i, 
    Restated.Vocabulary.Proofs.Bridges.NamedProvenance M S (w₁ v).st :=
  fun w₁ hw₁ =>
    ⟨Restated.Vocabulary.Proofs.NamedFinalizationBridge.finalization_carrier_stateBefore facts S rho i v
        w₁ hw₁,
      Restated.Vocabulary.Proofs.Bridges.storeJustificationOnChain_stateBefore facts S rho i v w₁ hw₁⟩

end

end DecoupledConsensusModel.Sts.Restated
