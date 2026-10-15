import Model.Vocabulary.Protocol.ForkChoice.Head
import Proofs.Claims.ModelIrreducible
import Proofs.Vocabulary.Protocol.Grades.ProposalParent
import Model.Vocabulary.Execution.Node
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Agreement

/-!
# Facts about `Protocol.get_head_with`

The full-tree head, which the proposal duty reads.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Execution.NamedProfile.gradeContract
  DecoupledConsensusModel.Protocol.frameContract
  DecoupledConsensusModel.Protocol.get_head_in_tree_with_layer
  DecoupledConsensusModel.Protocol.get_head_with
  DecoupledConsensusModel.Protocol.goldfish_fork_choice

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The head `Protocol.get_head_with` computes at the healing store `st` is the Goldfish fork choice
    with `st`'s chain-state map, `h_max`, tree and slot, started from the SG root the grade contract
    reads for the round of `st`'s slot, through `Protocol.get_filtered_block_tree` of `st`. -/
theorem get_head_with_eq_fork_choice (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (votes support : Finset (GoldfishVote V)) (s : Slot) :
    Protocol.get_head_with contract E hc st votes support s =
      Protocol.goldfish_fork_choice E st.σ st.h_max st.T st.s
        (Protocol.get_sg_root_with contract E hc st (hc.round_of st.s))
        (Protocol.get_filtered_block_tree st.toFG) votes support s := rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the healing store's `get_fg_root` is in its tree, then the head `Protocol.get_head_with`
    computes under the grade contract of the cache `c` is in the store's tree. -/
theorem get_head_with_gradeContract_mem (c : Protocol.Cache V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (votes support : Finset (GoldfishVote V)) (k : Slot)
    (hroot : Protocol.get_fg_root st.toFG ∈ st.T) :
    Protocol.get_head_with (Execution.NamedProfile.gradeContract c) E hc st votes support k
      ∈ st.T :=
  Proofs.NamedProposalParent.runtime_get_head_mem c E hc st votes support k hroot

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Sts
