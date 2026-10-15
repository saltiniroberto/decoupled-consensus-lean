module
public import Proofs.Vocabulary.Objects.SGTargetCompatibility
public import Proofs.Vocabulary.Protocol.Schedule.ConfirmationHistoryProducer
public import Proofs.Vocabulary.Protocol.Grades.SeedHeightProgress
public import Proofs.Vocabulary.ModelProperties.gradeBool
public import Proofs.Vocabulary.Protocol.Grades.Q31_actionSGBlock_tiers
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ProposalVoteDuty
import Proofs.Vocabulary.Protocol.Grades.GSTZeroSelectionSafety
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The cases of an honest round action's SG block

The SG block of an honest round action is a clear block between the anchor and the live
confirmation, the selected G2 candidate, the FG root, or the anchor.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}


private theorem entry_nat' {base q : Nat} (hq : base + 4 ≤ q) :
    1 ≤ q ∧ 1 ≤ q - 1 ∧ base + 1 ≤ q - 1 ∧ base + 1 ≤ q - 1 - 1 ∧ base ≤ q - 1 ∧
      base ≤ q - 1 - 1 ∧ q - 1 + 1 = q ∧ q - 1 + 2 ≤ q + 2 ∧
      base + 3 ≤ q ∧ base + 3 ≤ q - 1 := by
  omega


/-- The SG block `v` chooses at round `r`'s action is one of: a clear block between the anchor `A`
    and `live_confirmed`; the selected candidate `nodeQ2`; the FG root, when there is no candidate
    but a raw G2 block; or the anchor `A`. -/
theorem actionSGBlockAt_tiers (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    letI n := actionReadAt S rho v r
    letI A := Internal.PhaseGrades.nodeAnchor S n r
    (Block.Preceq A (actionSGBlockAt S rho v r) ∧
      Block.Preceq (actionSGBlockAt S rho v r) n.st.core.live_confirmed ∧
      Internal.PhaseGrades.nodeClear S n r (actionSGBlockAt S rho v r) = true) ∨
    (∃ Q, Internal.PhaseGrades.nodeQ2 S n r = some Q ∧
      actionSGBlockAt S rho v r = Q) ∨
    (Internal.PhaseGrades.nodeQ2 S n r = none ∧ Internal.PhaseGrades.nodeRawG2 S n r ∧
      actionSGBlockAt S rho v r =
        Protocol.get_fg_root n.st.core.toHealing.toFG) ∨
    (Internal.PhaseGrades.nodeQ2 S n r = none ∧
      ¬ Internal.PhaseGrades.nodeRawG2 S n r ∧ actionSGBlockAt S rho v r = A) :=
  Proofs.HealingLemmas.Rows.q31_actionsgblock_tiers S rho v r

#print axioms actionSGBlockAt_tiers


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
