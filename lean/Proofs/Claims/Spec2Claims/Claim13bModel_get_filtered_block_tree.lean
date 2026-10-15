import Proofs.Vocabulary.Protocol.Grades.Main
import Proofs.Claims.ModelIrreducible
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock

/-!
# Facts about `Protocol.get_filtered_block_tree`

The candidate tree a confirmation walk descends, and what membership in it gives.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Block.preceq DecoupledConsensusModel.Protocol.Store.toHealing
  DecoupledConsensusModel.Protocol.finalized_descendants
  DecoupledConsensusModel.Protocol.get_fg_root
  DecoupledConsensusModel.Protocol.get_filtered_block_tree
  DecoupledConsensusModel.Protocol.get_filtered_block_tree_from
  DecoupledConsensusModel.Protocol.viable DecoupledConsensusModel.Protocol.viable_tree

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- Setting a store's clock and slot leaves its filtered block tree unchanged. -/
theorem get_filtered_block_tree_set_clock_slot (st : Protocol.Store V) (t : Int) (s : Slot) :
    Protocol.get_filtered_block_tree ({ st with t := t, s := s } : Protocol.Store V).toHealing.toFG
      = Protocol.get_filtered_block_tree st.toHealing.toFG := rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]


omit [Fintype V] in
/-- If `B` is in the filtered tree of `st`, then some block `W` of `st`'s tree has `B ⪯ W` and
    chain-state height at least `st.h_max − 1`. -/
theorem viable_witness_of_mem_get_filtered_block_tree {st : Protocol.FGStore V} {B : Block V}
    (hB : B ∈ Protocol.get_filtered_block_tree st) :
    ∃ W ∈ st.T, Block.Preceq B W ∧ st.h_max - 1 ≤ (st.σ W).h := by
  simp only [Protocol.get_filtered_block_tree, Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants, Protocol.viable, Finset.mem_filter,
    decide_eq_true_eq] at hB
  obtain ⟨⟨-, W, hWT, hBW, hh⟩, -⟩ := hB
  exact ⟨W, hWT, hBW, hh⟩

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]


/-- If `C` is in the filtered tree of `st`, then `C` is in `st`'s tree, `st.F ⪯ C`, some block `W`
    of `st`'s tree has `C ⪯ W` and chain-state height at least `st.h_max − 1`, and `st`'s
    `get_fg_root` is an ancestor of `C`. -/
theorem parts_of_mem_get_filtered_block_tree {st : Protocol.FGStore V} {C : Block V}
    (h : C ∈ Protocol.get_filtered_block_tree st) :
    ((C ∈ st.T ∧ Block.Preceq st.F C) ∧
      ∃ W, W ∈ st.T ∧ Block.Preceq C W ∧ st.h_max - 1 ≤ (st.σ W).h) ∧
      Block.Preceq (Protocol.get_fg_root st) C := by
  simp only [Protocol.get_filtered_block_tree, Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants, Protocol.viable, Finset.mem_filter,
    decide_eq_true_eq] at h
  exact h

end DecoupledConsensusModel.Sts
