module
public import Proofs.Vocabulary.Protocol.Grades.HeightProgressClosureBatchAlignedSite
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeiling
import Proofs.Vocabulary.Protocol.Grades.GradeFormsBridge
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# A named parent is an ancestor

A named block's parent is an ancestor of the block.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]


omit [Fintype V] in
/-- A named block's parent is an ancestor of the block. -/
private theorem seedAdoption_namedParent_preceq (P : NamedBlock V) :
    NamedBlock.Preceq P.parent P := by
  cases P with
  | genesis => exact Proofs.NamedAncestry.named_self _
  | node parent slot root votes support rows proposer =>
      exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
        (Proofs.NamedAncestry.named_self parent)


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
