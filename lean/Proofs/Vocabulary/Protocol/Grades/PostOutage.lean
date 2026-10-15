module
public import Proofs.Vocabulary.Protocol.Grades.Interpolation
public import Proofs.Vocabulary.Protocol.Handlers.RetentionNamed
public import Proofs.Vocabulary.ModelProperties.Block_Preceq
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
import Proofs.Vocabulary.Execution.EmissionShape
import Proofs.Vocabulary.Protocol.Schedule.Action
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Proofs.Vocabulary.ModelProperties.Store_toHealing
import Proofs.Vocabulary.ModelProperties.get_head_in_tree_with_layer

@[expose] public section

/-!
# Vote heads and their anchors

The head of a vote duty is a descendant of its anchor, so every ancestor of the anchor is an
ancestor of the vote head.
-/
namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.PhaseGrades Internal.NamedRecoveryRead
open Internal.NamedStableChainOutage
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]


/-- The head of `v`'s slot-`s` vote duty is a descendant of its voter anchor. -/
theorem voteDutyHead_preceq_voteDutyAnchor
    (S : Setup V) (rho : Run V) (v : V) (s : Slot) :
    Block.Preceq
      (DecoupledConsensusModel.Proofs.HealingSurface.voterAnchorAt S rho v s)
      (voterHeadAt S rho v s) := by
  let n := voteDutyRead S rho v s
  have h := Proofs.ModelProperties.read_anchor_preceq_get_head_in_tree_with_layer
    (NamedProfile.gradeContract n.cache) S.E S.hc n.st.core.toHealing
    (Protocol.voter_filtered_block_tree S.E n.st.core n.st.core.s)
    (Protocol.voter_view S.E n.st.core.toHealing.toFG.toSG.toGoldfishStore n.st.core.s)
    (Protocol.voter_support_view S.E n.st.core.toHealing.toFG.toSG.toGoldfishStore n.st.core.s)
    (n.st.core.s - 1)
  rw [Proofs.ModelProperties.toHealing_s] at h
  exact h

/-- A block that is an ancestor of `v`'s slot-`s` voter anchor is an ancestor of its vote head. -/
theorem preceq_voteDutyHead_of_preceq_voteDutyAnchor
    (S : Setup V) (rho : Run V) (v : V) (s : Slot) {P : Block V}
    (hP : Block.Preceq P
      (DecoupledConsensusModel.Proofs.HealingSurface.voterAnchorAt S rho v s)) :
    Block.Preceq P (voterHeadAt S rho v s) :=
  Proofs.ModelProperties.Preceq_trans hP (voteDutyHead_preceq_voteDutyAnchor S rho v s)


#print axioms voteDutyHead_preceq_voteDutyAnchor
#print axioms preceq_voteDutyHead_of_preceq_voteDutyAnchor

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
