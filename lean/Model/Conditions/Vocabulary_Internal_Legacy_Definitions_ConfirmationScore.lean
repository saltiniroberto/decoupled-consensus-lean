import Proofs.Vocabulary.Internal.Legacy.Definitions.ConfirmationScore
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Confirmation score

The vote sets, the score and the eligibility test of a slot's confirmation evaluation, over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Internal
open Execution

/-- The outcomes of the votes of slot `s` in `st`'s pool resolved before the support cutoff of slot
    `s`. -/
def Vocabulary.Internal.confirmationEarly (M : Record.Model V) (E : Env V) (st : M.S) (s : Slot) :
    DC.NDRE (Finset (GoldfishVote V)) := do
  let τ ← st.tau
  pure (beforeCutoff τ (M.support_cutoff E s) ((M.store_pool st s)))

end

section
open DecoupledConsensusModel.Internal
open Execution

/-- The votes of slot `s` in `st`'s pool received before slot `s`'s confirmation time. -/
def Vocabulary.Internal.confirmationLate (M : Record.Model V) (E : Env V) (st : M.S) (s : Slot) :
    Finset (GoldfishVote V) :=
  beforeCutoff st.timestamp_vote (M.confirmation_time E s) ((M.store_pool st s))

end

section
open DecoupledConsensusModel.Internal
open Execution

/-- The outcomes of the votes of `confirmationEarly M E st s` whose validator has no second vote in
    `confirmationLate M E st s`. -/
def Vocabulary.Internal.confirmationVotes (M : Record.Model V) (E : Env V) (st : M.S) (s : Slot) :
    DC.NDRE (Finset (GoldfishVote V)) := do
  let early ← Restated.Vocabulary.Internal.confirmationEarly M E st s
  pure (early.filter
    (fun u => M.no_second_vote_in (Restated.Vocabulary.Internal.confirmationLate M E st s) u = true))

end

section
open DecoupledConsensusModel.Internal
open Execution

/-- The outcomes of the Goldfish score of `B` in `st`'s tree at slot `s`, with an outcome of
    `confirmationVotes M E st s` as both its raw and its support votes. -/
def Vocabulary.Internal.confirmationScore (M : Record.Model V) (E : Env V) (st : M.S) (s : Slot)
    (B : Block V) : DC.NDRE Nat := do
  let X ← Restated.Vocabulary.Internal.confirmationVotes M E st s
  M.goldfish_score E st.T X X s B

end

section
open DecoupledConsensusModel.Internal
open Execution

/-- The outcomes of the test whether the voter count of `confirmationLate M E st s` is less than
    twice an outcome of `confirmationScore M E st s B`. -/
def Vocabulary.Internal.confirmationEligible (M : Record.Model V) (E : Env V) (st : M.S) (s : Slot)
    (B : Block V) : DC.NDRE Bool := do
  let score ← Restated.Vocabulary.Internal.confirmationScore M E st s B
  pure (decide (M.voters_count E (Restated.Vocabulary.Internal.confirmationLate M E st s) s <
    2 * score))

end

section
open DecoupledConsensusModel.Internal
open Execution

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Internal.confirmationEarly` has the
    single outcome `DecoupledConsensusModel.Internal.confirmationEarly`. -/
@[record_vocabulary]
theorem Vocabulary.Internal.confirmationEarly_vocabulary_eq (E : Env V) (st : Protocol.Store V) (s : Slot) :
    Restated.Vocabulary.Internal.confirmationEarly (V := V) Record.Model.vocabulary E st s =
      pure (_root_.DecoupledConsensusModel.Internal.confirmationEarly (V := V) E st s) := by
  simp only [Restated.Vocabulary.Internal.confirmationEarly, Record.Model.S.tau,
    Record.Model.vocabulary, pure_bind]
  rfl

/-- `DecoupledConsensusModel.Internal.confirmationLate` equals
    `Restated.Vocabulary.Internal.confirmationLate` at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Internal.confirmationLate_vocabulary_eq (E : Env V) (st : Protocol.Store V) (s : Slot) :
    _root_.DecoupledConsensusModel.Internal.confirmationLate (V := V) E st s = Restated.Vocabulary.Internal.confirmationLate (V := V) Record.Model.vocabulary E st s :=
  rfl

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Internal.confirmationVotes` has the
    single outcome `DecoupledConsensusModel.Internal.confirmationVotes`. -/
@[record_vocabulary]
theorem Vocabulary.Internal.confirmationVotes_vocabulary_eq (E : Env V) (st : Protocol.Store V) (s : Slot) :
    Restated.Vocabulary.Internal.confirmationVotes (V := V) Record.Model.vocabulary E st s =
      pure (_root_.DecoupledConsensusModel.Internal.confirmationVotes (V := V) E st s) := by
  simp only [Restated.Vocabulary.Internal.confirmationVotes,
    Restated.Vocabulary.Internal.confirmationEarly_vocabulary_eq, pure_bind]
  rfl

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Internal.confirmationScore` has the
    single outcome `DecoupledConsensusModel.Internal.confirmationScore`. -/
@[record_vocabulary]
theorem Vocabulary.Internal.confirmationScore_vocabulary_eq (E : Env V) (st : Protocol.Store V) (s : Slot) (B : Block V) :
    Restated.Vocabulary.Internal.confirmationScore (V := V) Record.Model.vocabulary E st s B =
      pure (_root_.DecoupledConsensusModel.Internal.confirmationScore (V := V) E st s B) := by
  simp only [Restated.Vocabulary.Internal.confirmationScore,
    Restated.Vocabulary.Internal.confirmationVotes_vocabulary_eq, pure_bind]
  rfl

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Internal.confirmationEligible` has the
    single outcome `DecoupledConsensusModel.Internal.confirmationEligible`. -/
@[record_vocabulary]
theorem Vocabulary.Internal.confirmationEligible_vocabulary_eq (E : Env V) (st : Protocol.Store V) (s : Slot) (B : Block V) :
    Restated.Vocabulary.Internal.confirmationEligible (V := V) Record.Model.vocabulary E st s B =
      pure (_root_.DecoupledConsensusModel.Internal.confirmationEligible (V := V) E st s B) := by
  simp only [Restated.Vocabulary.Internal.confirmationEligible,
    Restated.Vocabulary.Internal.confirmationScore_vocabulary_eq, pure_bind]
  rfl

end

end DecoupledConsensusModel.Sts.Restated
