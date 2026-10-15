import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Records
import Proofs.Claims.ModelIrreducible
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Adoption
import Proofs.Vocabulary.ModelProperties.get_sg_root_with
import Proofs.Vocabulary.ModelProperties.get_head_in_tree_with_layer
import Proofs.Vocabulary.ModelProperties.Block_Preceq
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.FrontierParent

/-!
# Facts about `Protocol.get_head_in_tree_with_layer`

The Goldfish head over a given candidate tree: the fork choice started at the store's SG root.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Execution.NamedProfile.gradeContract
  DecoupledConsensusModel.Execution.RootInjectiveBelow
  DecoupledConsensusModel.Protocol.Store.toHealing
  DecoupledConsensusModel.Protocol.get_head_in_tree_with_layer
  DecoupledConsensusModel.Protocol.get_sg_root_with DecoupledConsensusModel.Protocol.ghost
  DecoupledConsensusModel.Protocol.goldfish_fork_choice
  DecoupledConsensusModel.Protocol.raw_supporters

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If a set of blocks `T` holds the SG root the contract reads at the store's round and every block
    of `tree`, then the head over `tree` is in `T`. -/
theorem get_head_in_tree_with_layer_mem (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.HealingStore V) (tree : Finset (Block V))
    (votes support : Finset (GoldfishVote V)) (k : Slot) {T : Finset (Block V)}
    (hA : Protocol.get_sg_root_with contract E hc st (hc.round_of st.s) ∈ T)
    (htree : tree ⊆ T) :
    Protocol.get_head_in_tree_with_layer contract E hc st tree votes support k ∈ T := by
  unfold Protocol.get_head_in_tree_with_layer Protocol.goldfish_fork_choice
  exact Proofs.Records.ghost_mem_of _ _ hA htree

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Under the grade contract of the cache `c`, the healing store's `get_fg_root` is an ancestor of
    the head over any candidate tree. -/
theorem fgRoot_Preceq_get_head_in_tree_with_layer_gradeContract (c : Protocol.Cache V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (k : Slot) :
    Block.Preceq (Protocol.get_fg_root st.toFG)
      (Protocol.get_head_in_tree_with_layer (Execution.NamedProfile.gradeContract c) E hc st tree votes
        support k) :=
  Proofs.ModelProperties.Preceq_trans
    (Proofs.ModelProperties.fg_root_Preceq_get_sg_root_with_gradeContract c E hc st
      (hc.round_of st.s))
    (Proofs.ModelProperties.read_anchor_preceq_get_head_in_tree_with_layer
      (Execution.NamedProfile.gradeContract c) E hc st tree votes support k)

/-- The head over `tree` at the healing view of `st` is either the anchor of the contract's grade
    read at `st`'s round, or a block of `tree`. -/
theorem get_head_in_tree_with_layer_anchor_or_mem (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V) (tree : Finset (Block V))
    (votes support : Finset (GoldfishVote V)) (k : Slot) :
    Protocol.get_head_in_tree_with_layer contract E hc st.toHealing tree votes support k =
        (contract.read E hc st.toHealing (hc.round_of st.s)).anchor ∨
      Protocol.get_head_in_tree_with_layer contract E hc st.toHealing tree votes support k ∈
        tree := by
  unfold Protocol.get_head_in_tree_with_layer Protocol.goldfish_fork_choice
    Protocol.get_sg_root_with
  exact Proofs.Records.ghost_mem _ _ _ _

/-- If no two blocks of `tree` have the same root, `C ∈ tree`, and the parent of `C` is the head
    over `tree` at the healing view of `st`, then `C` is not Goldfish-eligible at `st` with the same
    votes and slot. -/
theorem goldfish_eligible_false_of_parent_head (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V) (tree : Finset (Block V))
    (votes support : Finset (GoldfishVote V)) (k : Slot) {C : Block V}
    (hroot : Execution.RootInjectiveBelow tree) (hC : C ∈ tree)
    (hparent : C.parent? = some
      (Protocol.get_head_in_tree_with_layer contract E hc st.toHealing tree votes support k)) :
    Protocol.goldfish_eligible E st.σ st.h_max st.T st.s votes support k C = false := by
  unfold Protocol.get_head_in_tree_with_layer Protocol.goldfish_fork_choice at hparent
  exact Proofs.HealingSurface.eligible_child_false_at_ghost_result hroot hC hparent

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Sts
