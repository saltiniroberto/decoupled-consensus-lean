import Proofs.Vocabulary.Internal.ModelVocabulary.Healing.Action
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Proposal and attestation inputs

The proposal and attestation duties' reads of a healing store, over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Protocol

/-- The outcomes of the proposal duty's read of the healing store `st` under `contract`, each a
    proposal input or a failure. -/
def Vocabulary.Protocol.proposal_input_with (M : Record.Model V) (contract : M.Contract)
    (E : Env V) (hc : HealConfig) (nd : Protocol.Node V) (st : M.HS) :
    DC.NDRE (ProposalInput V) :=
  M.with_proposal_input contract E hc nd st id

end

section
open DecoupledConsensusModel.Protocol

/-- The outcomes of the attestation duty's read of the healing store `st` under `contract`, each an
    attestation input or a failure. -/
def Vocabulary.Protocol.attestation_input_with (M : Record.Model V) (contract : M.Contract)
    (E : Env V) (hc : HealConfig) (nd : Protocol.Node V) (st : M.HS) :
    DC.NDRE (AttestationInput V) :=
  M.with_attestation_input contract E hc nd st id

end

section
open DecoupledConsensusModel.Protocol

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Protocol.proposal_input_with` has the
    single outcome `DecoupledConsensusModel.Protocol.proposal_input_with`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.proposal_input_with_vocabulary_eq (contract : GradeContract V) (E : Env V) (hc : HealConfig) (nd : Protocol.Node V) (st : HealingStore V) :
    Restated.Vocabulary.Protocol.proposal_input_with (V := V) Record.Model.vocabulary contract E hc nd st =
      pure (_root_.DecoupledConsensusModel.Protocol.proposal_input_with (V := V) contract E hc nd st) :=
  rfl

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Protocol.attestation_input_with` has
    the single outcome `DecoupledConsensusModel.Protocol.attestation_input_with`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.attestation_input_with_vocabulary_eq (contract : GradeContract V) (E : Env V) (hc : HealConfig) (nd : Protocol.Node V) (st : HealingStore V) :
    Restated.Vocabulary.Protocol.attestation_input_with (V := V) Record.Model.vocabulary contract E hc nd st =
      pure (_root_.DecoupledConsensusModel.Protocol.attestation_input_with (V := V) contract E hc nd st) :=
  rfl

end

end DecoupledConsensusModel.Sts.Restated
