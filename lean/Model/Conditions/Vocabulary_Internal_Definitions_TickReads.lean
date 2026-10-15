import Proofs.Vocabulary.Internal.Definitions.TickReads
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Record.Wiring

/-!
# The stores a tick and a vote duty read

The store a tick hands its first duty, the store the Goldfish vote reads, and the set of vote duty
stores of a run, stated over a model `M : Record.Model V`, and their counterparts at
`Record.Model.vocabulary`.
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
open DecoupledConsensusModel.Execution

/-- The store the tick at `t` hands its first duty: `st` with the clock and the slot written. -/
def Vocabulary.Proofs.Optimistic.tickStore (M : Record.Model V) (S : Setup V) (st : M.S) (t : Time) : M.S :=
  M.store_with_t_s st t (S.E.slotOf t)

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Execution

/-- The store the Goldfish vote reads at slot `s`'s vote instant: the tick's store at that instant. -/
def Vocabulary.Proofs.Optimistic.voteStore (M : Record.Model V) (S : Setup V) (st : M.S) (s : Slot) : M.S :=
  Restated.Vocabulary.Proofs.Optimistic.tickStore M S st (M.vote_time S.E s)

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Execution

/-- The set of stores the Goldfish vote reads at slot `s`'s vote instant, one for each store `w` can
    hold just before that instant. -/
def Vocabulary.Proofs.Optimistic.voteDutyStore (M : Record.Model V) (S : Setup V) (ρ : Record.Run V) (w : V) (s : Slot) :
    DC.NDR M.S :=
  (fun ns => Restated.Vocabulary.Proofs.Optimistic.voteStore M S ns.core s) ''
    Restated.Vocabulary.Execution.Run.storeBeforeTime M S ρ w (M.vote_time S.E s)

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Execution

/-- At `Record.Model.vocabulary`, the restated `tickStore` is
    `DecoupledConsensusModel.Proofs.Optimistic.tickStore`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.Optimistic.tickStore_vocabulary_eq (S : Setup V) (st : Protocol.Store V) (t : Time) :
    _root_.DecoupledConsensusModel.Proofs.Optimistic.tickStore (V := V) S st t = Restated.Vocabulary.Proofs.Optimistic.tickStore (V := V) Record.Model.vocabulary S st t :=
  rfl

/-- At `Record.Model.vocabulary`, the restated `voteStore` is
    `DecoupledConsensusModel.Proofs.Optimistic.voteStore`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.Optimistic.voteStore_vocabulary_eq (S : Setup V) (st : Protocol.Store V) (s : Slot) :
    _root_.DecoupledConsensusModel.Proofs.Optimistic.voteStore (V := V) S st s = Restated.Vocabulary.Proofs.Optimistic.voteStore (V := V) Record.Model.vocabulary S st s :=
  rfl

/-- At `Record.Model.vocabulary` and a run embedded by `Record.Run.ofVocabulary`, the restated
    `voteDutyStore` is the singleton of the value of
    `DecoupledConsensusModel.Proofs.Optimistic.voteDutyStore`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.Optimistic.voteDutyStore_vocabulary_eq (S : Setup V) (ρ : Run V) (w : V) (s : Slot) :
    Restated.Vocabulary.Proofs.Optimistic.voteDutyStore (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary ρ) w s =
      {_root_.DecoupledConsensusModel.Proofs.Optimistic.voteDutyStore (V := V) S ρ w s} := by
  rw [Restated.Vocabulary.Proofs.Optimistic.voteDutyStore, Vocabulary.Execution.Run.storeBeforeTime_vocabulary_eq]
  exact Set.image_singleton

end

end DecoupledConsensusModel.Sts.Restated
