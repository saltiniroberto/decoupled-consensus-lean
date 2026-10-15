module
public import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedHeadReads
public import Model.Vocabulary.Statements.Instantiation.Certificates
public import Proofs.Vocabulary.Internal.ModelVocabulary.Protocol.Store
public import Mathlib.Algebra.Order.Floor.Div
public import Proofs.Vocabulary.Internal.Legacy.Definitions.Confirmation
public import Proofs.Vocabulary.Internal.Legacy.Interface
public import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedOutageEntry

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Vote-duty head

`Protocol.voteDutyHead`, the voter's head at its vote-duty read.
-/


namespace DecoupledConsensusModel
open Internal Execution Proofs.HealingSurface
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The voter's head at slot `s`, `voterHeadAt`. -/
def Protocol.voteDutyHead (S : Setup V) (rho : Run V) (v : V) (s : Slot) : Block V :=
  Internal.voterHeadAt S rho v s

end DecoupledConsensusModel

end
