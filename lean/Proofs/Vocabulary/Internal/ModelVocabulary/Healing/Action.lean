module
public import Model.Vocabulary.Protocol.Duties.Inputs

@[expose] public section

/-!
# Proposal and attestation inputs

The contract-parameterised inputs of the proposal and of the round action's attestation.
-/

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

def proposal_input_with (contract : GradeContract V)
    (E : Env V) (hc : HealConfig) (nd : Protocol.Node V) (st : HealingStore V) : ProposalInput V :=
  with_proposal_input contract E hc nd st id

def attestation_input_with (contract : GradeContract V)
    (E : Env V) (hc : HealConfig) (nd : Protocol.Node V) (st : HealingStore V) :
    AttestationInput V :=
  with_attestation_input contract E hc nd st id

end Protocol
end DecoupledConsensusModel

end
