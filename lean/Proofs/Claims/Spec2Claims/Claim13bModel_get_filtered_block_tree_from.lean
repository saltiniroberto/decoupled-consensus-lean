import Model.Vocabulary.Protocol.ForkChoice.Goldfish
import Proofs.Claims.ModelIrreducible
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq

/-!
# Facts about `Protocol.get_filtered_block_tree_from`

The filtered tree drawn from a set of blocks: the blocks of the set that are descendants of the
store's finalized block, have a descendant in the set with chain-state height at least `h_max − 1`,
and are descendants of the store's `get_fg_root`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Protocol.finalized_descendants
  DecoupledConsensusModel.Protocol.get_filtered_block_tree_from
  DecoupledConsensusModel.Protocol.viable DecoupledConsensusModel.Protocol.viable_tree

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If `B` is in the filtered tree of `st` drawn from `blocks`, then `B ∈ blocks`, `st.F ⪯ B`, some
    `W ∈ blocks` has `B ⪯ W` and chain-state height at least `st.h_max − 1`, and `st`'s
    `get_fg_root` is an ancestor of `B`. -/
theorem mem_get_filtered_block_tree_from_parts {st : Protocol.FGStore V}
    {blocks : Finset (Block V)} {B : Block V}
    (hB : B ∈ Protocol.get_filtered_block_tree_from st blocks) :
    B ∈ blocks ∧ Block.Preceq st.F B ∧
      (∃ W ∈ blocks, Block.Preceq B W ∧ st.h_max - 1 ≤ (st.σ W).h) ∧
      Block.Preceq (Protocol.get_fg_root st) B := by
  simp only [Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
    Protocol.finalized_descendants, Protocol.viable, Finset.mem_filter,
    decide_eq_true_eq] at hB
  exact ⟨hB.1.1.1, preceq_eq_true_iff_Preceq.1 hB.1.1.2, hB.1.2,
    preceq_eq_true_iff_Preceq.1 hB.2⟩


end DecoupledConsensusModel.Sts

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If `C` is in the filtered tree of `st` over `blocks`, then `C ∈ blocks`, `st.F ⪯ C`, some
    `W ∈ blocks` has `C ⪯ W` and chain-state height at least `st.h_max − 1`, and `st`'s
    `get_fg_root` is an ancestor of `C`. -/
theorem parts_of_mem_get_filtered_block_tree_from {st : Protocol.FGStore V}
    {blocks : Finset (Block V)} {C : Block V}
    (h : C ∈ Protocol.get_filtered_block_tree_from st blocks) :
    ((C ∈ blocks ∧ Block.Preceq st.F C) ∧
      ∃ W, W ∈ blocks ∧ Block.Preceq C W ∧ st.h_max - 1 ≤ (st.σ W).h) ∧
      Block.Preceq (Protocol.get_fg_root st) C := by
  simp only [Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
    Protocol.finalized_descendants, Protocol.viable, Finset.mem_filter,
    decide_eq_true_eq] at h
  exact h

/-- If `C ∈ blocks`, `st.F ⪯ C`, some `W ∈ blocks` has `C ⪯ W` and chain-state height at least
    `st.h_max − 1`, and `st`'s `get_fg_root` is an ancestor of `C`, then `C` is in the filtered tree
    of `st` over `blocks`. -/
theorem mem_get_filtered_block_tree_from_of_parts_explicit (st : Protocol.FGStore V)
    {blocks : Finset (Block V)} {C W : Block V}
    (hC : C ∈ blocks) (hF : Block.Preceq st.F C)
    (hW : W ∈ blocks) (hCW : Block.Preceq C W) (hh : st.h_max - 1 ≤ (st.σ W).h)
    (hroot : Block.Preceq (Protocol.get_fg_root st) C) :
    C ∈ Protocol.get_filtered_block_tree_from st blocks := by
  simp only [Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
    Protocol.finalized_descendants, Protocol.viable, Finset.mem_filter,
    decide_eq_true_eq]
  exact ⟨⟨⟨hC, hF⟩, W, hW, hCW, hh⟩, hroot⟩

end DecoupledConsensusModel.Sts
