import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeiling
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Record.Wiring

/-!
# A round's last slot and opening confirmation

The last slot of a round and the confirmed blocks a validator can hold at a round's action, over a
model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic
open Protocol (derive_named)

/-- The last slot of round `q`: the slot before the opening slot of round `q + 1`. -/
def Vocabulary.Proofs.HealingSurface.seedRoundLastSlot (M : Record.Model V) (S : Setup V) (q : Round) : Slot :=
  (M.opening_slot S.hc (q + 1)) - 1

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic
open Protocol (derive_named)

/-- The set of the blocks `n.live_confirmed`, for every node state `n` that `v` can hold at round
    `q`'s action. -/
def Vocabulary.Proofs.HealingSurface.roundCeilingOpeningOutput (M : Record.Model V)
    (S : Setup V) (rho : Record.Run V) (q : Round) (v : V) : DC.NDR (Block V) :=
  (fun n : M.N => n.live_confirmed) ''
    Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M S rho v q

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic
open Protocol (derive_named)

/-- `DecoupledConsensusModel.Proofs.HealingSurface.seedRoundLastSlot` equals
    `Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot` at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.seedRoundLastSlot_vocabulary_eq (S : Setup V) (q : Round) :
    _root_.DecoupledConsensusModel.Proofs.HealingSurface.seedRoundLastSlot (V := V) S q = Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot (V := V) Record.Model.vocabulary S q :=
  rfl

/-- At the model `Record.Model.vocabulary`,
    `Restated.Vocabulary.Proofs.HealingSurface.roundCeilingOpeningOutput` is the singleton of
    `DecoupledConsensusModel.Proofs.HealingSurface.roundCeilingOpeningOutput`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.roundCeilingOpeningOutput_vocabulary_eq (S : Setup V) (rho : Run V) (q : Round) (v : V) :
    Restated.Vocabulary.Proofs.HealingSurface.roundCeilingOpeningOutput (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) q v =
      {_root_.DecoupledConsensusModel.Proofs.HealingSurface.roundCeilingOpeningOutput (V := V) S rho q v} := by
  rw [Restated.Vocabulary.Proofs.HealingSurface.roundCeilingOpeningOutput,
    Vocabulary.Proofs.HealingSurface.actionStoreAt_vocabulary_eq]
  exact Set.image_singleton

end

end DecoupledConsensusModel.Sts.Restated
