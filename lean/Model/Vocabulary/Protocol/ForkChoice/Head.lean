module
public import Model.Vocabulary.Protocol.Grades

@[expose] public section

/-!
# SG root and head

The SG root a grade contract supplies, and the head: the Goldfish walk from that root through the
filtered block tree.
-/

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The SG root: the anchor the grade contract reads for round `r`. -/
def get_sg_root_with (contract : GradeContract V)
    (E : Env V) (hc : HealConfig) (st : HealingStore V) (r : Round) : Block V :=
  (contract.read E hc st r).anchor

/-- The head in `tree`: the Goldfish fork choice from the SG root of the current round. -/
def get_head_in_tree_with_layer (contract : GradeContract V)
    (E : Env V) (hc : HealConfig) (st : HealingStore V)
    (tree : Finset (Block V)) (votes support_votes : Finset (GoldfishVote V))
    (k : Slot) : Block V :=
  let A := get_sg_root_with contract E hc st (hc.round_of st.s)
  Protocol.goldfish_fork_choice E st.σ st.h_max st.T st.s A tree votes
    support_votes k

/-- The head: `get_head_in_tree_with_layer` over the filtered block tree. -/
def get_head_with (contract : GradeContract V)
    (E : Env V) (hc : HealConfig) (st : HealingStore V)
    (votes support_votes : Finset (GoldfishVote V)) (k : Slot) : Block V :=
  get_head_in_tree_with_layer contract E hc st
    (Protocol.get_filtered_block_tree st.toFG) votes support_votes k

end Protocol
end DecoupledConsensusModel

end
