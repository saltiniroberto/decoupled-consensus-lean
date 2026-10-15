module
public import Proofs.Vocabulary.Protocol.Grades.GradeFormsBridge
public import Proofs.Vocabulary.Protocol.ValidatorClient.RecoveryTimeout
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.FinalityFilterRetention
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedAdoption

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Seed-promotion helpers

Private facts: a named block's parent is its ancestor, and a step of round arithmetic.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem seedPromotionAncestor_namedParent_preceq (P : NamedBlock V) :
    NamedBlock.Preceq P.parent P := by
  cases P with
  | genesis => exact Proofs.NamedAncestry.named_self _
  | node parent slot root votes support rows proposer =>
      exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
        (Proofs.NamedAncestry.named_self parent)

private theorem seedPromotionAncestor_rounds_nat
    {q q' : Nat} (h : q + 2 ≤ q') :
    q + 1 ≤ q' - 1 ∧ 0 < q' - 1 := by
  omega

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
