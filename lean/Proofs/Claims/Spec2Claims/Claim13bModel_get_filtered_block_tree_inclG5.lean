import Model.Vocabulary.Protocol.Grades
import Proofs.Claims.ModelIrreducible

/-!
# Membership in `Protocol.get_filtered_block_tree`

Membership in a healing store's candidate tree, from its four parts.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Protocol.finalized_descendants
  DecoupledConsensusModel.Protocol.get_filtered_block_tree
  DecoupledConsensusModel.Protocol.get_filtered_block_tree_from
  DecoupledConsensusModel.Protocol.viable DecoupledConsensusModel.Protocol.viable_tree

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If `C` is in the healing store's tree, `st.F ⪯ C`, some block `W` of the store's tree has
    `C ⪯ W` and chain-state height at least `st.h_max − 1`, and the store's `get_fg_root` is an
    ancestor of `C`, then `C` is in `Protocol.get_filtered_block_tree` of the store. -/
theorem mem_get_filtered_block_tree_of_parts (st : Protocol.HealingStore V) {C W : Block V}
    (hC : C ∈ st.T) (hF : Block.Preceq st.F C)
    (hW : W ∈ st.T) (hCW : Block.Preceq C W) (hh : st.h_max - 1 ≤ (st.σ W).h)
    (hroot : Block.Preceq (Protocol.get_fg_root st.toFG) C) :
    C ∈ Protocol.get_filtered_block_tree st.toFG := by
  simp only [Protocol.get_filtered_block_tree, Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants, Finset.mem_filter, Protocol.viable,
    decide_eq_true_eq]
  exact ⟨⟨⟨hC, hF⟩, W, hW, hCW, hh⟩, hroot⟩

end DecoupledConsensusModel.Sts
