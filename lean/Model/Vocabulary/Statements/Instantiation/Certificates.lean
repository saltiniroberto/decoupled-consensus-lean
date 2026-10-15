module
public import Model.Vocabulary.Protocol.ChainState

@[expose] public section

/-!
# Finalization certificates

The finalization predicate on the derived state of a named block.
-/
namespace DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The derived state of the named block `C` has finalized block `T` at height `h`. -/
def NamedFinalizedAt (E : Env V) (cfg : HeightConfig) (C : NamedBlock V) (T : Block V)
    (h : Height) : Prop :=
  (derive_named E cfg C).F = T ∧ (derive_named E cfg C).h_F = h

end DecoupledConsensusModel.Statements.Instantiation

end
