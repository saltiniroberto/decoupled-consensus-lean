module
public import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedDutyReads
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.NamedAdmissible
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Run
public import Model.Vocabulary.Statements.Instantiation.Proposals

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Duty reads

The proposal-duty read `proposalDutyRead` and the vote-duty store `voteDutyStore`.
-/
namespace DecoupledConsensusModel.Internal.NamedRecoveryRead
open Execution Proofs.HealingSurface
variable {V : Type} [DecidableEq V] [Fintype V]

def proposalDutyRead (S : Setup V) (rho : Run V) (s : Slot) : NamedNodeState V :=
  proposerReadAt S rho s

def voteDutyStore (S : Setup V) (rho : Run V) (v : V) (s : Slot) : Protocol.Store V :=
  (voteDutyRead S rho v s).st.core

end DecoupledConsensusModel.Internal.NamedRecoveryRead

end
