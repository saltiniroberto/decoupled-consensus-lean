import Model.Vocabulary.Protocol.Handlers
import Proofs.Claims.ModelIrreducible
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Adoption

/-!
# Facts about `Protocol.get_head_in_tree_with`

The explicit-tree head at a store, and the head `Protocol.get_head_in_tree_with_layer` it is
computed by.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Block.preceq DecoupledConsensusModel.Protocol.HealConfig.round_of
  DecoupledConsensusModel.Protocol.Store.toHealing
  DecoupledConsensusModel.Protocol.get_head_in_tree_with
  DecoupledConsensusModel.Protocol.get_head_in_tree_with_layer
  DecoupledConsensusModel.Protocol.get_sg_root_with DecoupledConsensusModel.Protocol.ghost
  DecoupledConsensusModel.Protocol.ghost_walk DecoupledConsensusModel.Protocol.goldfish_fork_choice
  DecoupledConsensusModel.Protocol.goldfish_score

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The head `Protocol.get_head_in_tree_with` computes at the store `st` is the head
    `Protocol.get_head_in_tree_with_layer` computes with the same arguments at the healing view of
    `st`. -/
theorem get_head_in_tree_with_eq_layer (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V)
    (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (k : Slot) :
    Protocol.get_head_in_tree_with contract E hc st tree votes support k =
      Protocol.get_head_in_tree_with_layer contract E hc st.toHealing tree votes support k := rfl

/-- The head `Protocol.get_head_in_tree_with` computes at `st` over `tree` is the Goldfish fork
    choice with `st`'s chain-state map, `h_max`, tree and slot, started from the SG root the grade
    contract reads for the round of `st`'s slot, through `tree`. -/
theorem get_head_in_tree_with_eq_fork_choice (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V)
    (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (s : Slot) :
    Protocol.get_head_in_tree_with contract E hc st tree votes support s =
      Protocol.goldfish_fork_choice E st.toHealing.σ st.toHealing.h_max st.T st.s
        (Protocol.get_sg_root_with contract E hc st.toHealing (hc.round_of st.s)) tree
        votes support s := rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The SG root the grade contract reads for the round of `st`'s slot is an ancestor of the head
    `Protocol.get_head_in_tree_with` computes at `st` over any candidate tree and vote sets. -/
theorem get_sg_root_with_preceq_get_head_in_tree_with_store (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V)
    (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (s : Slot) :
    Block.Preceq (Protocol.get_sg_root_with contract E hc st.toHealing (hc.round_of st.s))
      (Protocol.get_head_in_tree_with contract E hc st tree votes support s) := by
  unfold Protocol.get_head_in_tree_with Protocol.get_head_in_tree_with_layer
    Protocol.goldfish_fork_choice
  exact Protocol.ghost_preceq _ _ _ _

end DecoupledConsensusModel.Sts
