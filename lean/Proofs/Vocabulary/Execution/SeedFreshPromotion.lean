module
public import Proofs.Vocabulary.Protocol.ChainState.RawHeightCoverage
public import Proofs.Vocabulary.ModelProperties.confirmationReadFrom
public import Proofs.Vocabulary.ModelProperties.ProposalRows_inWindow
public import Proofs.Vocabulary.Protocol.Grades.LifecycleActionSource
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.RecoveryProposalWindow
import Mathlib.Data.Rat.Floor

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Seed-branch ancestry helper

A private fact: a named block's parent is its ancestor.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem seedFresh_parent_preceq_self (B : NamedBlock V) :
    NamedBlock.Preceq B.parent B := by
  cases B with
  | genesis => exact Proofs.NamedAncestry.named_self _
  | node parent slot root votes support rows proposer =>
      exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
        (Proofs.NamedAncestry.named_self parent)


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
