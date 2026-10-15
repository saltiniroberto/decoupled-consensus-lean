module
public import Model.Vocabulary.Statements.Instantiation.Proposals
public import Proofs.Vocabulary.Internal.ModelVocabulary.Healing.Action

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

namespace DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The proposal input the proposer's duty computes on its prepared read at slot `s`. -/
def proposalInputAt (S : Setup V) (rho : Run V) (s : Slot) : Protocol.ProposalInput V :=
  let n := proposerReadAt S rho s
  Protocol.proposal_input_with (NamedProfile.gradeContract n.cache) S.E S.hc
    (S.node (S.E.proposer s)) n.st.core.toHealing

/-- The parent the honest proposer selects: the input's parent field. -/
def proposedParent (S : Setup V) (rho : Run V) (s : Slot) : Block V :=
  (proposalInputAt S rho s).parent

end DecoupledConsensusModel.Proofs.HealingSurface

end
