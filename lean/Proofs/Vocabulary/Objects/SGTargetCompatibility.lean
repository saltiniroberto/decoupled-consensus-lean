module
public import Proofs.Vocabulary.Internal.Definitions.NamedLifecycle
public import Proofs.Vocabulary.Internal.Legacy.Assumptions.Weight
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Admissible
import Proofs.Vocabulary.Execution.NamedAncestry
import Proofs.Vocabulary.Execution.Wire
import Proofs.Vocabulary.Protocol.Schedule.Alignment

@[expose] public section
/-!
# Two ancestors of one block are compatible

Two ancestors of a common block, such as one honest Goldfish head, are compatible.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Proofs.Optimistic

variable {V : Type} [DecidableEq V]

/-- Two ancestors `T1` and `T2` of the block `X` are compatible. -/
theorem compatible_of_common_honest_goldfish_head
    {T1 T2 X : Block V}
    (hT1 : Block.Preceq T1 X)
    (hT2 : Block.Preceq T2 X) :
    Block.compatible T1 T2 = true := by
  exact Block.compatible_of_preceq_common hT1 hT2


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
