module
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.named_transition`

The chain-state transition of a named block does not read the environment's GST.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.slot
  DecoupledConsensusModel.Electorate.finalityThreshold
  DecoupledConsensusModel.Electorate.quorumCheck DecoupledConsensusModel.NamedBlock.attestations
  DecoupledConsensusModel.Protocol.ChainState.Q_target
  DecoupledConsensusModel.Protocol.advance_height DecoupledConsensusModel.Protocol.fold_rows

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

section ChainStateBodies

attribute [local semireducible] Protocol.named_transition Protocol.transition_rows
  Protocol.process_height_events Protocol.finalityReady Protocol.targetReady Protocol.progReady
  Protocol.ChainState.finalityQuorum Protocol.ChainState.targetQuorum
  Protocol.ChainState.progQuorum

/-- For every GST `g ≥ 0`, `named_transition` at the environment `E` with its GST replaced by `g` is
    the transition at `E`. -/
theorem named_transition_withGST (E : Env V) (g : Int) (hg : 0 ≤ g) :
    Protocol.named_transition { E with t_GST := g, t_GST_nonneg := hg } =
      Protocol.named_transition E := rfl

end ChainStateBodies

end DecoupledConsensusModel.Sts
