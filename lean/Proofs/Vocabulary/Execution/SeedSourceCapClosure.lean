module
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Seed source-height helpers

Private facts: a named block's parent is its ancestor, and compatibility passes to an ancestor.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Protocol Proofs.HealingLemmas Proofs.Optimistic DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

omit [Fintype V] in
private theorem seedSourceCap_namedParent_preceq (P : NamedBlock V) :
    NamedBlock.Preceq P.parent P := by
  cases P with
  | genesis => exact Proofs.NamedAncestry.named_self _
  | node parent slot root votes support rows proposer =>
      exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
        (Proofs.NamedAncestry.named_self parent)

omit [Fintype V] in
private theorem seedSourceCap_compatible_ancestor_left {A K C : Block V}
    (hAK : Block.Preceq A K) (hKC : Block.compatible K C = true) :
    Block.compatible A C = true := by
  rcases (show Block.Preceq K C ∨ Block.Preceq C K by
    simpa only [Block.compatible, Bool.or_eq_true, Block.Preceq] using hKC) with hKC | hCK
  · simpa only [Block.compatible, Bool.or_eq_true] using
      Or.inl (Block.preceq_trans hAK hKC)
  · exact Block.compatible_of_preceq_common hAK hCK

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
