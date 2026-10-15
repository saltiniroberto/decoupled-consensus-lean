import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.FinalityFilterRetention
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Record.Wiring

/-!
# Finality filter retention

The condition that a protected block is in a store's filtered block tree, over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface

/-- In the world `wd`, `P` is in the filtered block tree of `w`'s core store. -/
def Vocabulary.Proofs.HealingSurface.FinalityFilterRetainedAtRead (M : Record.Model V)
    (S : Setup V) (rho : Record.Run V) (w : V) (read : Time) (wd : V → M.N)
    (P : Block V) : Prop :=
  P ∈ M.get_filtered_block_tree (wd w).st.core.toHealing.toFG

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface

/-- `DecoupledConsensusModel.Proofs.HealingSurface.FinalityFilterRetainedAtRead` holds exactly when
    `Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterRetainedAtRead` holds at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.FinalityFilterRetainedAtRead_vocabulary_eq (S : Setup V) (rho : Run V) (w : V) (read : Time) (P : Block V) :
    _root_.DecoupledConsensusModel.Proofs.HealingSurface.FinalityFilterRetainedAtRead (V := V) S rho w read P ↔
      Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterRetainedAtRead (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) w read
        (_root_.DecoupledConsensusModel.Execution.NamedRun.stateBeforeTime S rho read) P :=
  Iff.rfl

end

end DecoupledConsensusModel.Sts.Restated
