module
public import Model.Vocabulary.Protocol.Handlers

@[expose] public section

/-!
# Erased evidence helpers

The chain state `derived_state` of an erased block, used by proof-side comparison lemmas.
-/
namespace DecoupledConsensusModel.Internal
open Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The chain state `σ[B]` derived from the structural chain of an erased block. -/
def derived_state (E : Env V) (cfg : HeightConfig) : Block V → ChainState V
  | .genesis => ChainState.initial
  | B@(.node p _ _ _ _ _ _) =>
      Protocol.state_transition E cfg (derived_state E cfg p) B

end DecoupledConsensusModel.Internal

end
