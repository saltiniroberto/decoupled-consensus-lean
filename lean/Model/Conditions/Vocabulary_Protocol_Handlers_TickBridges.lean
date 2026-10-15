import Proofs.Vocabulary.Protocol.Handlers.TickBridges
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Record.Wiring

/-!
# The store read by the slot confirmation

The set of stores the slot-`s` confirmation reads, stated over a model `M : Record.Model V`, and its
agreement with the definition of the same name at `Record.Model.vocabulary`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Protocol

/-- The set of the stores `tickStore M S st.core (M.confirmation_time S.E s)`, for every store `st`
    that `v` can hold just before slot `s`'s confirmation time in `ρ`. -/
def Vocabulary.Proofs.Optimistic.confStore (M : Record.Model V) (S : Setup V) (ρ : Record.Run V) (v : V) (s : Slot) :
    DC.NDR M.S :=
  (fun ns => Restated.Vocabulary.Proofs.Optimistic.tickStore M S ns.core (M.confirmation_time S.E s)) ''
    Restated.Vocabulary.Execution.Run.storeBeforeTime M S ρ v (M.confirmation_time S.E s)

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Protocol

/-- At `Record.Model.vocabulary`, the set of values of `confStore` over the record is the singleton of
    the value of `DecoupledConsensusModel.Proofs.Optimistic.confStore`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.Optimistic.confStore_vocabulary_eq (S : Setup V) (ρ : Run V) (v : V) (s : Slot) :
    Restated.Vocabulary.Proofs.Optimistic.confStore (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary ρ) v s =
      {_root_.DecoupledConsensusModel.Proofs.Optimistic.confStore (V := V) S ρ v s} := by
  rw [Restated.Vocabulary.Proofs.Optimistic.confStore, Vocabulary.Execution.Run.storeBeforeTime_vocabulary_eq]
  exact Set.image_singleton

end

end DecoupledConsensusModel.Sts.Restated
