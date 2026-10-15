module
public import Proofs.Vocabulary.Internal.Definitions.NamedOutageEntry
public import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.NamedBlocks

@[expose] public section

/-!
# Round confirmation read

`roundConfirmationRead`, a validator's confirmation read at a round's action time.
-/
namespace DecoupledConsensusModel.Internal.NamedStableChainOutage
open Execution NamedOutageEntry DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]


/-- `v`'s confirmation read at the action time of round `s`. -/
def roundConfirmationRead (S : Setup V) (rho : NamedRun V) (v : V) (s : Round) :
    NamedNodeState V :=
  confirmationReadAt S rho v (S.a s)


end DecoupledConsensusModel.Internal.NamedStableChainOutage

end
