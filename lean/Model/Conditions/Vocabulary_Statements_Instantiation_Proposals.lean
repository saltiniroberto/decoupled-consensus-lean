import Model.Vocabulary.Statements.Instantiation.Proposals
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Record.Wiring

/-!
# The proposal of a slot

The node states a slot's proposer can hold at its proposal time and the blocks it can propose there,
stated over a model `M : Record.Model V`, and their agreement with the definitions of the same name
at `Record.Model.vocabulary`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Statements
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel DecoupledConsensusModel.Execution

/-- The set of node states slot `s`'s proposer can hold when it reads at slot `s`'s proposal time. -/
def Vocabulary.Statements.Instantiation.proposerReadAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (s : Slot) : DC.NDR M.N :=
  Restated.Vocabulary.Execution.NamedActionReads.confirmationReadAt M S rho (S.E.proposer s) (M.proposal_time S.E s)

end

section
open DecoupledConsensusModel.Statements
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel DecoupledConsensusModel.Execution

/-- The set of outcomes of `M.proposal_with` with the attestation source `.poolAndCarried`, for
    every node state in `proposerReadAt M S rho s`. -/
def Vocabulary.Statements.Instantiation.proposedBlockAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (s : Slot) : DC.NDR (Option (NamedBlock V)) :=
  { b | ∃ n ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho s,
      M.proposal_with (M.gradeContract n.cache) .poolAndCarried
        S.E S.hc (S.node (S.E.proposer s)) n.st ⇢ b }

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Statements
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel DecoupledConsensusModel.Execution

/-- At `Record.Model.vocabulary`, the set of values of `proposerReadAt` over the record is the
    singleton of the value of `DecoupledConsensusModel.Statements.Instantiation.proposerReadAt`. -/
@[record_vocabulary]
theorem Vocabulary.Statements.Instantiation.proposerReadAt_vocabulary_eq (S : Setup V) (rho : Run V) (s : Slot) :
    Restated.Vocabulary.Statements.Instantiation.proposerReadAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) s =
      {_root_.DecoupledConsensusModel.Statements.Instantiation.proposerReadAt (V := V) S rho s} :=
  Vocabulary.Execution.NamedActionReads.confirmationReadAt_vocabulary_eq S rho _ _

/-- At `Record.Model.vocabulary`, the set of values of `proposedBlockAt` over the record is the
    singleton of the value of `DecoupledConsensusModel.Statements.Instantiation.proposedBlockAt`. -/
@[record_vocabulary]
theorem Vocabulary.Statements.Instantiation.proposedBlockAt_vocabulary_eq (S : Setup V) (rho : Run V) (s : Slot) :
    Restated.Vocabulary.Statements.Instantiation.proposedBlockAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) s =
      {_root_.DecoupledConsensusModel.Statements.Instantiation.proposedBlockAt (V := V) S rho s} := by
  ext b
  rw [Restated.Vocabulary.Statements.Instantiation.proposedBlockAt,
    Vocabulary.Statements.Instantiation.proposerReadAt_vocabulary_eq]
  constructor
  · rintro ⟨n, hn, hb⟩
    obtain rfl : n = _ := hn
    exact (Record.returns_pure _ _).1 hb
  · intro hb
    obtain rfl : b = _ := hb
    exact ⟨_, rfl, (Record.returns_pure _ _).2 rfl⟩

end

end DecoupledConsensusModel.Sts.Restated
