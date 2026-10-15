module
public import Proofs.Vocabulary.Execution.ExcludesRefute
public import Proofs.Vocabulary.Protocol.Handlers.AdoptionConstructor
public import Proofs.Vocabulary.Execution.Wire
public import Proofs.Vocabulary.Internal.Internal.GradeReads
public import Proofs.Vocabulary.Generic.CarrierAdmissionCore
import Proofs.Vocabulary.Execution.Acceptance
import Proofs.Vocabulary.Protocol.Grades.Grades
import Proofs.Vocabulary.Protocol.Schedule.SlotInduction
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Proofs.Vocabulary.ModelProperties.Store_toHealing
import Proofs.Vocabulary.ModelProperties.get_filtered_block_tree

@[expose] public section

/-!
# Two store facts at a read

Every SG vote in a store's round-`k` SG vote set has round `k`, and a block in the filtered tree is
a descendant of the store's finalized block.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace GradeDeliveryRun

open Internal
open Execution
open Internal.PhaseGrades
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]


omit [Fintype V] in
/-! ## Projected vote transport -/


theorem projected_rounds_storeBeforeTime
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    (w : V) (read : Time) :
    ∀ k : Round, ∀ u ∈
      (rho.storeBeforeTime S w read).toHealing.sg_votes k, u.round = k := by
  obtain ⟨N, hN, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S sch read
  have hread : rho.storeBeforeTime S w read = (rho.stateBefore S N w).st :=
    congrArg NodeState.st (congrFun hN w)
  intro k u hu
  rw [hread] at hu
  change u ∈ ((rho.stateBefore S N w).st.sg_pool k).image Protocol.sgVote at hu
  obtain ⟨a, ha, hau⟩ := Finset.mem_image.mp hu
  have haround := Proofs.NamedStoreBridge.sgRounds_stateBefore S rho N w k a
    (List.mem_toFinset.mp ha)
  simpa only [← hau, Protocol.sgVote] using haround


/- A block in the filtered tree of `w`'s store before time `read` is a descendant of that store's
    finalized block. -/
theorem finalized_preceq_of_mem_filtered_at_read
    (S : Setup V) (rho : Run V) {w : V} {read : Time} {B : Block V}
    (hactive : B ∈ Protocol.get_filtered_block_tree
      (rho.storeBeforeTime S w read).toHealing.toFG) :
    Block.Preceq (rho.storeBeforeTime S w read).F B := by
  have h := Proofs.ModelProperties.finalized_preceq_of_mem_get_filtered_block_tree hactive
  rw [Proofs.ModelProperties.toHealing_F] at h
  exact h


end GradeDeliveryRun
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
