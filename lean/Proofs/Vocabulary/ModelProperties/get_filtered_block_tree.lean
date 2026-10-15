module
public import Model.Vocabulary.Protocol.ForkChoice.Goldfish
public import Model.Vocabulary.Protocol.Store

@[expose] public section

/-!
# Facts about `Protocol.get_filtered_block_tree`

The filtered candidate tree of a store.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V]

/-- Every block of the filtered tree is a descendant of the store's finalized block, or that block
    itself. -/
theorem finalized_preceq_of_mem_get_filtered_block_tree {st : Protocol.FGStore V} {B : Block V}
    (hB : B ∈ Protocol.get_filtered_block_tree st) : Block.Preceq st.F B := by
  simp only [Protocol.get_filtered_block_tree, Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants, Finset.mem_filter] at hB
  exact hB.1.1.2

/-- The filtered tree does not read the clock or the slot. -/
theorem get_filtered_block_tree_toHealing_clock (st : Protocol.Store V) (t : Time) (s : Slot) :
    Protocol.get_filtered_block_tree
        ({ st with t := t, s := s } : Protocol.Store V).toHealing.toFG =
      Protocol.get_filtered_block_tree st.toHealing.toFG := rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
