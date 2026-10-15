module
public import Proofs.Vocabulary.Generic.PostGSTCarrierAdmissionCore
public import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
public import Proofs.Vocabulary.Protocol.Schedule.PostHealingReuse
public import Proofs.Vocabulary.Protocol.Grades.GradeFormsBridge
public import Proofs.Vocabulary.Protocol.Grades.Interpolation
public import Proofs.Vocabulary.Protocol.Handlers.RetentionNamed
import Proofs.Vocabulary.Objects.BlockVisibilityCore
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ProposalVoteDuty
import Proofs.Vocabulary.Execution.EmissionShape
import Proofs.Vocabulary.Protocol.Grades.CacheProvenance
import Proofs.Vocabulary.Protocol.Schedule.Action
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]


/-- The opening slot names its round. -/
theorem round_of_opening_slot_eq
    (hc : Protocol.HealConfig) (r : Round) :
    hc.round_of (hc.opening_slot r) = r := by
  simp only [Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
  have hR : 0 < hc.R := lt_of_lt_of_le Nat.zero_lt_two hc.R_ge_two
  simpa only [Nat.mul_comm] using Nat.mul_div_cancel_left r hR


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
