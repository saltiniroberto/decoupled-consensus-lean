module
public import Proofs.Vocabulary.Objects.ActionRound
public import Proofs.Vocabulary.Protocol.Grades.RecoveryCapturedSlotInterval
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ReaderLocalCone
public import Proofs.Vocabulary.Generic.FixedHeightRootAdmission
public import Proofs.Vocabulary.Protocol.Store.BoundaryRows
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.RawHeightActiveLifecycle
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.RoundZero
import Proofs.Vocabulary.Protocol.Grades.GradeFormsBridge
import Proofs.Vocabulary.Protocol.Handlers.HMaxCore
import Mathlib.Data.Rat.Floor
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Tactic.ENatToNat

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# A named parent is an ancestor

A named block's parent, when it has one, is an ancestor of the block.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}


private theorem namedParent_preceq_of_parent?
    {B P : NamedBlock V} (h : NamedBlock.parent? B = some P) :
    NamedBlock.Preceq P B := by
  cases B with
  | genesis => cases h
  | node parent slot root votes support rows proposer =>
      have hparent : parent = P := Option.some.inj h
      subst P
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
      exact Or.inr (Proofs.NamedAncestry.named_self parent)


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
