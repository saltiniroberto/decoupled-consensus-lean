module
public import Proofs.Vocabulary.Protocol.ChainState.ProposalBridge
public import Proofs.Vocabulary.ModelProperties.get_sg_root_with
public import Proofs.Vocabulary.ModelProperties.get_head_in_tree_with_layer
public import Proofs.Vocabulary.ModelProperties.Store_toHealing
public import Proofs.Vocabulary.ModelProperties.Block_Preceq
public import Proofs.Vocabulary.Internal.Definitions.NamedResult23Statements
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Proofs.Vocabulary.ModelProperties.NamedProfile_gradeContract
import Proofs.Vocabulary.ModelProperties.anchor

@[expose] public section

/-!
# The prepared vote-duty read

Equations and order lemmas for the prepared vote-duty read, its frame contract, its anchor and its
candidate tree.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## The prepared head and anchor -/

/-- The prepared vote head is the contract-parametric walk on its own read. -/
theorem voterHeadAt_eq_get_head_with_anchor
    (S : Setup V) (rho : Run V) (v : V) (s : Slot) :
    voterHeadAt S rho v s =
      Protocol.get_head_in_tree_with_layer
        (NamedProfile.gradeContract (voteDutyRead S rho v s).cache)
        S.E S.hc (voteDutyRead S rho v s).st.core.toHealing
        (voterCandidateTreeAt S rho v s)
        (Protocol.voter_view S.E
          (voteDutyRead S rho v s).st.core.toHealing.toFG.toSG.toGoldfishStore
          (voteDutyRead S rho v s).st.core.s)
        (Protocol.voter_support_view S.E
          (voteDutyRead S rho v s).st.core.toHealing.toFG.toSG.toGoldfishStore
          (voteDutyRead S rho v s).st.core.s)
        ((voteDutyRead S rho v s).st.core.s - 1) := by
  rfl

/-- The prepared anchor is either the active prefix of the saved G1 root or
the store's FG root. -/
theorem voterAnchorAt_cases
    (S : Setup V) (rho : Run V) (v : V) (s : Slot) :
    voterAnchorAt S rho v s =
        Protocol.get_fg_root
          (voteDutyRead S rho v s).st.core.toHealing.toFG ∨
      ∃ root A,
        (DecoupledConsensusModel.Protocol.readFrame (voteDutyRead S rho v s).cache
          (voteDutyRead S rho v s).st.core.toHealing
          (S.hc.round_of (voteDutyRead S rho v s).st.core.s)).g1 =
          some (some root) ∧
        DecoupledConsensusModel.Protocol.activePrefix
          (Protocol.get_filtered_block_tree
            (voteDutyRead S rho v s).st.core.toHealing.toFG) root = some A ∧
        voterAnchorAt S rho v s = A := by
  dsimp only [voterAnchorAt, nodeAnchor, nodeRead]
  rw [Proofs.ModelProperties.gradeContract_read_anchor]
  exact Proofs.ModelProperties.anchor_cases _ _ _ _ _

/-! ## Ancestors of the prepared head -/

/-- The prepared SG root is an ancestor of the prepared vote-duty head. -/
theorem sgRootWith_preceq_voterHeadAt
    (S : Setup V) (rho : Run V) (v : V) (s : Slot) :
    Block.Preceq
      (Protocol.get_sg_root_with
        (NamedProfile.gradeContract (voteDutyRead S rho v s).cache)
        S.E S.hc (voteDutyRead S rho v s).st.core.toHealing
        (S.hc.round_of (voteDutyRead S rho v s).st.core.s))
      (voterHeadAt S rho v s) := by
  rw [voterHeadAt_eq_get_head_with_anchor,
    Proofs.ModelProperties.get_sg_root_with_eq_read_anchor]
  have h := Proofs.ModelProperties.read_anchor_preceq_get_head_in_tree_with_layer
    (NamedProfile.gradeContract (voteDutyRead S rho v s).cache) S.E S.hc
    (voteDutyRead S rho v s).st.core.toHealing (voterCandidateTreeAt S rho v s)
    (Protocol.voter_view S.E
      (voteDutyRead S rho v s).st.core.toHealing.toFG.toSG.toGoldfishStore
      (voteDutyRead S rho v s).st.core.s)
    (Protocol.voter_support_view S.E
      (voteDutyRead S rho v s).st.core.toHealing.toFG.toSG.toGoldfishStore
      (voteDutyRead S rho v s).st.core.s)
    ((voteDutyRead S rho v s).st.core.s - 1)
  rw [Proofs.ModelProperties.toHealing_s] at h
  exact h

/-- The prepared anchor is an ancestor of the prepared vote-duty head. -/
theorem voterAnchorAt_preceq_voterHeadAt
    (S : Setup V) (rho : Run V) (v : V) (s : Slot) :
    Block.Preceq (voterAnchorAt S rho v s)
      (voterHeadAt S rho v s) := by
  have h := sgRootWith_preceq_voterHeadAt S rho v s
  rw [Proofs.ModelProperties.get_sg_root_with_eq_read_anchor] at h
  exact h

/-- The explicit prepared walk from the same anchor equals `voterHeadAt`. -/
theorem get_head_in_tree_eq_voterHeadAt_of_anchor
    (S : Setup V) (rho : NamedRun V) (v : V) (s : Slot) :
    Protocol.get_head_in_tree_with_layer
        (NamedProfile.gradeContract (voteDutyRead S rho v s).cache)
        S.E S.hc (voteDutyRead S rho v s).st.core.toHealing
        (voterCandidateTreeAt S rho v s)
        (Protocol.voter_view S.E
          (voteDutyRead S rho v s).st.core.toHealing.toFG.toSG.toGoldfishStore
          (voteDutyRead S rho v s).st.core.s)
        (Protocol.voter_support_view S.E
          (voteDutyRead S rho v s).st.core.toHealing.toFG.toSG.toGoldfishStore
          (voteDutyRead S rho v s).st.core.s)
        ((voteDutyRead S rho v s).st.core.s - 1) =
      voterHeadAt S rho v s := by
  exact (voterHeadAt_eq_get_head_with_anchor S rho v s).symm


/-- The SG root `get_sg_root_with` is an ancestor of the head of the explicit-tree walk. -/
theorem get_sg_root_with_preceq_get_head_in_tree_with
    (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V))
    (k : Slot) :
    Block.Preceq
      (Protocol.get_sg_root_with contract E hc st (hc.round_of st.s))
      (Protocol.get_head_in_tree_with_layer contract E hc st tree votes support k) := by
  exact Protocol.ghost_preceq _ _ _ _

/-- Under the frame contract, any ancestor of the FG root is an ancestor of the head of the
    explicit-tree walk. -/
theorem get_head_in_tree_with_of_preceq_fgRoot
    (cache : DecoupledConsensusModel.Protocol.Cache V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (tree : Finset (Block V)) (F : Block V)
    (votes support : Finset (GoldfishVote V)) (k : Slot)
    (hroot : Block.Preceq F (Protocol.get_fg_root st.toFG)) :
    Block.Preceq F
      (Protocol.get_head_in_tree_with_layer (DecoupledConsensusModel.Protocol.frameContract cache)
        E hc st tree votes support k) := by
  exact Block.preceq_trans hroot
    (Block.preceq_trans
      (fg_root_preceq_get_sg_root_with_frame cache E hc st
        (hc.round_of st.s))
      (get_sg_root_with_preceq_get_head_in_tree_with
        (DecoupledConsensusModel.Protocol.frameContract cache) E hc st tree votes support k))

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
