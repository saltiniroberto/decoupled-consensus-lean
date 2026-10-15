module
public import Proofs.Vocabulary.Protocol.Grades.VoterAnchorSourceInputs
public import Proofs.Vocabulary.Protocol.ChainState.Emission
public import Proofs.Vocabulary.Protocol.Grades.RecoveryDelayedSourceSeed
public import Proofs.Vocabulary.Protocol.Duties.Inputs.FGSourceRawGrade

@[expose] public section

/-!
# Named genesis is an ancestor of every named block

A helper: named genesis is an ancestor of every named block.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem namedGenesis_preceq (B : NamedBlock V) :
    NamedBlock.Preceq .genesis B := by
  induction B with
  | genesis => rfl
  | node parent slot root votes support rows proposer ih =>
      exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer ih

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
