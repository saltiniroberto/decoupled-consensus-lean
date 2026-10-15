module
public import Proofs.Vocabulary.Generic.FixedHeightRootAdmission
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep
public import Proofs.Vocabulary.Protocol.Grades.RelativeCarrierWindowGateOff
public import Proofs.Vocabulary.ModelProperties.confirmationReadFrom
public import Proofs.Vocabulary.ModelProperties.get_fg_root
import Proofs.Vocabulary.Objects.SGTargetCompatibility
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ProposalVoteDuty
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.RecoveryFinalityFilterRetainedAdoption
import Proofs.Vocabulary.Protocol.Grades.GSTZeroSelectionSafety
import Proofs.Vocabulary.Protocol.Grades.RecoveryCapturedSlotInterval
import Proofs.Vocabulary.ModelProperties.gradeBool
import Proofs.Vocabulary.Protocol.Grades.Q31_actionSGBlock_tiers
import Proofs.Vocabulary.Protocol.Grades.GradeFormsBridge
import Proofs.Vocabulary.Protocol.Schedule.ConfirmationHistoryProducer
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.WittVector.IsPoly

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Two ancestry helpers

A named block's parent is an ancestor of the block, and an ancestor of a block compatible with `C`
is compatible with `C`.
-/

namespace DecoupledConsensusModel.Proofs.HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Protocol Proofs.HealingLemmas Proofs.Optimistic DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

omit [Fintype V] in
private theorem fixedRootSource_parent_preceq_self (B : NamedBlock V) :
    NamedBlock.Preceq B.parent B := by
  cases B with
  | genesis => exact Proofs.NamedAncestry.named_self _
  | node parent slot root votes support rows proposer =>
      exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
        (Proofs.NamedAncestry.named_self parent)

omit [Fintype V] in
private theorem fixedRootSource_compatible_left
    {A K C : Block V} (hAK : Block.Preceq A K)
    (hKC : Block.compatible K C = true) : Block.compatible A C = true := by
  rcases (show Block.Preceq K C ∨ Block.Preceq C K by
    simpa only [Block.compatible, Bool.or_eq_true, Block.Preceq] using hKC) with hKC | hCK
  · simpa only [Block.compatible, Bool.or_eq_true] using
      Or.inl (Block.preceq_trans hAK hKC)
  · exact Block.compatible_of_preceq_common hAK hCK


end DecoupledConsensusModel.Proofs.HealingSurface

end
