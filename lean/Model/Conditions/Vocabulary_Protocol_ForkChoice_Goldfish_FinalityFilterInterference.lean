import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.FinalityFilterInterference
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Record.Wiring

/-!
# Finality filter interference

The conditions under which the finality-gadget root and the filtered tree of a store do or do not
exclude a protected block, over a model `M : Record.Model V`.
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

/-- In the world `wd`, `P` is an ancestor of the finality-gadget root of `w`'s store, or `P` is in
    the filtered block tree of `w`'s store. -/
def Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead (M : Record.Model V)
    (S : Setup V) (rho : Record.Run V) (w : V) (read : Time) (wd : V → M.N)
    (P : Block V) : Prop :=
  Block.Preceq P (M.get_fg_root (wd w).st.toHealing.toFG) ∨
    P ∈ M.get_filtered_block_tree (wd w).st.toHealing.toFG

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution

/-- The finality-gadget root of `st` is not compatible with `P`. -/
def Vocabulary.Proofs.HealingSurface.FGRootInterferenceAt (M : Record.Model V) (st : M.NS) (P : Block V) : Prop :=
  Block.compatible
    (M.get_fg_root st.toHealing.toFG) P = false

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution

/-- The finality-gadget root of `st` is a strict ancestor of `P`, and `P` is not in `st`'s filtered
    block tree. -/
def Vocabulary.Proofs.HealingSurface.HeightFilterInterferenceAt (M : Record.Model V) (st : M.NS) (P : Block V) : Prop :=
  Block.Prec (M.get_fg_root st.toHealing.toFG) P ∧
    P ∉ M.get_filtered_block_tree st.toHealing.toFG

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution

/-- `DecoupledConsensusModel.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead` holds
    exactly when `Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead` holds
    at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead_vocabulary_eq (S : Setup V) (rho : Run V) (w : V) (read : Time) (P : Block V) :
    _root_.DecoupledConsensusModel.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead (V := V) S rho w read P ↔ Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) w read
      (_root_.DecoupledConsensusModel.Execution.NamedRun.stateBeforeTime S rho read) P :=
  Iff.rfl

/-- `DecoupledConsensusModel.Proofs.HealingSurface.FGRootInterferenceAt` holds exactly when
    `Restated.Vocabulary.Proofs.HealingSurface.FGRootInterferenceAt` holds at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.FGRootInterferenceAt_vocabulary_eq (st : Protocol.NamedStore V) (P : Block V) :
    _root_.DecoupledConsensusModel.Proofs.HealingSurface.FGRootInterferenceAt (V := V) st P ↔ Restated.Vocabulary.Proofs.HealingSurface.FGRootInterferenceAt (V := V) Record.Model.vocabulary st P :=
  Iff.rfl

/-- `DecoupledConsensusModel.Proofs.HealingSurface.HeightFilterInterferenceAt` holds exactly when
    `Restated.Vocabulary.Proofs.HealingSurface.HeightFilterInterferenceAt` holds at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.HeightFilterInterferenceAt_vocabulary_eq (st : Protocol.NamedStore V) (P : Block V) :
    _root_.DecoupledConsensusModel.Proofs.HealingSurface.HeightFilterInterferenceAt (V := V) st P ↔ Restated.Vocabulary.Proofs.HealingSurface.HeightFilterInterferenceAt (V := V) Record.Model.vocabulary st P :=
  Iff.rfl

end

end DecoupledConsensusModel.Sts.Restated
