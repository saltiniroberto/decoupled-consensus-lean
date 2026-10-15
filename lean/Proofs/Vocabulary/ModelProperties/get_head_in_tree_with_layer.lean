module
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Walk
public import Model.Vocabulary.Protocol.ForkChoice.Head
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Records

@[expose] public section

/-!
# Facts about `Protocol.get_head_in_tree_with_layer`

The head over a candidate tree, started at the contract's anchor.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The anchor the contract reads at the store's round is an ancestor of the head over any candidate
    tree. -/
theorem read_anchor_preceq_get_head_in_tree_with_layer (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (k : Slot) :
    Block.Preceq (contract.read E hc st (hc.round_of st.s)).anchor
      (Protocol.get_head_in_tree_with_layer contract E hc st tree votes support k) := by
  unfold Protocol.get_head_in_tree_with_layer Protocol.goldfish_fork_choice
    Protocol.get_sg_root_with
  exact Protocol.ghost_preceq _ _ _ _

/-- If the contract's anchor is in `T` and the candidate tree is a subset of `T`, the head over that
    tree is in `T`. -/
theorem get_head_in_tree_with_layer_mem (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (k : Slot)
    {T : Finset (Block V)} (hanchor : (contract.read E hc st (hc.round_of st.s)).anchor ∈ T)
    (htree : tree ⊆ T) :
    Protocol.get_head_in_tree_with_layer contract E hc st tree votes support k ∈ T := by
  unfold Protocol.get_head_in_tree_with_layer Protocol.goldfish_fork_choice
    Protocol.get_sg_root_with
  exact Proofs.Records.ghost_mem_of _ _ hanchor htree

end DecoupledConsensusModel.Proofs.ModelProperties

end
