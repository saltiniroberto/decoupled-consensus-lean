module
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.HeightProgressSeedRegime
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.RawHeightActiveLifecycle
public import Proofs.Vocabulary.Protocol.Grades.GradeFormsProducers
import Proofs.Vocabulary.Objects.Final
import Proofs.Vocabulary.Protocol.ChainState.SlashableBoundBridge
import Proofs.Vocabulary.Protocol.Grades.GradeFormsBridge
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Rat.Floor
import Mathlib.Logic.Equiv.PartialEquiv

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation


/-!
# Height-progress round lags

The round budgets `seedLag` and `progressLag'`, and the fact that `progressLag'` is positive.
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
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

/-- The seed's round budget: `4 * gap + 12 + 2 * delayExtra` rounds. -/
def seedLag (gap : Round) (delayExtra : Nat := 0) : Round :=
  4 * gap + 12 + 2 * delayExtra

/-- The height-progress round lag: `seedLag gap delayExtra` plus `3 * gap + 10 + 2 * delayExtra`
    rounds. -/
def progressLag' (gap : Round) (delayExtra : Nat := 0) : Round :=
  seedLag gap delayExtra + 3 * gap + 10 + 2 * delayExtra


theorem progressLag'_pos (gap : Round) : 0 < progressLag' gap delayExtra := by
  simp [progressLag', seedLag]


private theorem compose_namedParent_preceq_of_parent?
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


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Protocol
open Proofs.HealingLemmas
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
