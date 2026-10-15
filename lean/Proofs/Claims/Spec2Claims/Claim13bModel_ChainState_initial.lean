import Model.Vocabulary.Protocol.ChainState
import Proofs.Claims.ModelIrreducible

/-!
# The initial chain state

The initial chain state `Protocol.ChainState.initial` stands at height `1`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type}

section ChainStateBodies

attribute [local semireducible] Protocol.ChainState.initial

/-- The initial chain state, the chain state of genesis, has `h = 1`. -/
theorem chainState_initial_h : (Protocol.ChainState.initial : Protocol.ChainState V).h = 1 :=
  rfl

end ChainStateBodies

end DecoupledConsensusModel.Sts
