module
public import Proofs.Vocabulary.Protocol.ChainState.RawHeightCoverage
public import Proofs.Vocabulary.Objects.FixedHeightRootCore
import Proofs.Vocabulary.Protocol.Handlers.HMaxCore
import Proofs.Vocabulary.Generic.SuffixHistory
import Proofs.Vocabulary.Objects.Final
import Proofs.Vocabulary.Protocol.ChainState.SlashableBoundBridge
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.RecoveryProposalWindow
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.RoundZero
import Proofs.Vocabulary.Protocol.Grades.CleanReadBridge
import Proofs.Vocabulary.Protocol.Grades.GradeFormsProducers
import Proofs.Vocabulary.Protocol.Schedule.ProposalCanonicality
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat

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
open Internal.PhaseGrades
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem lifecycle_parent_preceq (B : NamedBlock V) :
    NamedBlock.Preceq B.parent B := by
  cases B with
  | genesis => exact Proofs.NamedAncestry.named_self _
  | node parent slot root votes support rows proposer =>
      exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
        (Proofs.NamedAncestry.named_self parent)


namespace DecoupledConsensusModel.Proofs.HealingSurface
end DecoupledConsensusModel.Proofs.HealingSurface

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
