import Proofs.Vocabulary.Internal.Legacy.Definitions.ProposalSourcesInternal
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Healing_Action
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# Proposal inputs

The proposal input and the parent an honest proposer of a slot can select, as sets over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Execution

/-- The set of proposal inputs `proposal_input_with` can return from some node state in
    `proposerReadAt M S rho s`, with the node of slot `s`'s proposer. -/
def Vocabulary.Proofs.HealingSurface.proposalInputAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (s : Slot) :
    DC.NDR (Protocol.ProposalInput V) :=
  { p | ∃ n ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho s,
    Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract n.cache) S.E S.hc
      (S.node (S.E.proposer s)) (M.toHealing n.st.core) ⇢ p }

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Execution

/-- The set of the parent fields of the inputs in `proposalInputAt M S rho s`. -/
def Vocabulary.Proofs.HealingSurface.proposedParent (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (s : Slot) :
    DC.NDR (Block V) :=
  (fun p : Protocol.ProposalInput V => p.parent) ''
    Restated.Vocabulary.Proofs.HealingSurface.proposalInputAt M S rho s

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Execution

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Proofs.HealingSurface.proposalInputAt`
    is the singleton of `DecoupledConsensusModel.Proofs.HealingSurface.proposalInputAt`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.proposalInputAt_vocabulary_eq (S : Setup V) (rho : Run V) (s : Slot) :
    Restated.Vocabulary.Proofs.HealingSurface.proposalInputAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) s =
      {_root_.DecoupledConsensusModel.Proofs.HealingSurface.proposalInputAt (V := V) S rho s} := by
  rw [Restated.Vocabulary.Proofs.HealingSurface.proposalInputAt, Vocabulary.Statements.Instantiation.proposerReadAt_vocabulary_eq]
  ext p
  constructor
  · rintro ⟨n, hn, h⟩
    have hn' : n = _ := hn
    subst hn'
    rw [Vocabulary.Protocol.proposal_input_with_vocabulary_eq] at h
    exact (Record.returns_pure _ _).1 h
  · intro h
    rw [Set.mem_singleton_iff] at h
    subst h
    refine ⟨_, rfl, ?_⟩
    rw [Vocabulary.Protocol.proposal_input_with_vocabulary_eq]
    exact (Record.returns_pure _ _).2 rfl

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Proofs.HealingSurface.proposedParent`
    is the singleton of `DecoupledConsensusModel.Proofs.HealingSurface.proposedParent`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.HealingSurface.proposedParent_vocabulary_eq (S : Setup V) (rho : Run V) (s : Slot) :
    Restated.Vocabulary.Proofs.HealingSurface.proposedParent (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) s =
      {_root_.DecoupledConsensusModel.Proofs.HealingSurface.proposedParent (V := V) S rho s} := by
  rw [Restated.Vocabulary.Proofs.HealingSurface.proposedParent, Vocabulary.Proofs.HealingSurface.proposalInputAt_vocabulary_eq]
  exact Set.image_singleton

end

end DecoupledConsensusModel.Sts.Restated
