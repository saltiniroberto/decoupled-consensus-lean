import Proofs.Claims.Spec2Claims.Claim13bStepCone
import Proofs.Vocabulary.ModelProperties.viable_tree

/-!
# Facts on `Protocol.voter_filtered_block_tree`

The candidate tree the Goldfish vote duty descends, against the voter's processed tree it filters:
its members are exactly the blocks of the processed tree with the four properties the filter asks
for.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Env.slotOf DecoupledConsensusModel.Protocol.Store.toHealing
  DecoupledConsensusModel.Protocol.finalized_descendants
  DecoupledConsensusModel.Protocol.get_filtered_block_tree_from
  DecoupledConsensusModel.Protocol.viable DecoupledConsensusModel.Protocol.viable_tree
  DecoupledConsensusModel.Protocol.voter_filtered_block_tree
  DecoupledConsensusModel.Protocol.voter_processed_block_tree DecoupledConsensusModel.stampedBefore

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every block of the voter's filtered tree of the store `st` at slot `s` is in `st.T`. -/
theorem voter_filtered_block_tree_subset (E : Env V) (st : Protocol.Store V) (s : Slot) :
    Protocol.voter_filtered_block_tree E st s ⊆ st.T := by
  intro B hB
  unfold Protocol.voter_filtered_block_tree at hB
  have hp := Proofs.Records.get_filtered_block_tree_from_subset _ _ hB
  unfold Protocol.voter_processed_block_tree at hp
  exact (Finset.mem_filter.mp hp).1

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If `C` is in the voter's processed tree of `st` at slot `s`, `st.F` is an ancestor of `C`, `C`
    is an ancestor of a block `Y` of that processed tree whose chain-state height is at least
    `st.h_max − 1`, and `st`'s fgroot is an ancestor of `C`, then `C` is in the voter's filtered
    tree of `st` at slot `s`. -/
theorem mem_voter_filtered_block_tree_of_parts (E : Env V) (st : Protocol.Store V) (s : Slot)
    {C Y : Block V}
    (hC : C ∈ Protocol.voter_processed_block_tree E st.toHealing.toFG.toSG.toGoldfishStore s)
    (hF : Block.Preceq st.F C)
    (hY : Y ∈ Protocol.voter_processed_block_tree E st.toHealing.toFG.toSG.toGoldfishStore s)
    (hCY : Block.Preceq C Y) (hh : st.h_max - 1 ≤ (st.σ Y).h)
    (hroot : Block.Preceq (Protocol.get_fg_root st.toHealing.toFG) C) :
    C ∈ Protocol.voter_filtered_block_tree E st s := by
  simp only [Protocol.voter_filtered_block_tree, Protocol.get_filtered_block_tree_from]
  exact Finset.mem_filter.mpr
    ⟨(Proofs.ModelProperties.mem_viable_tree_iff _ _ _ _ _).mpr ⟨⟨hC, hF⟩, Y, hY, hCY, hh⟩,
      hroot⟩


/-- A block `C` of the voter's filtered tree of `st` at slot `s` is in the voter's processed tree,
    has `st.F` as an ancestor, is an ancestor of a block of that processed tree whose chain-state
    height is at least `st.h_max − 1`, and has `st`'s fgroot as an ancestor; the converse of
    `mem_voter_filtered_block_tree_of_parts`. -/
theorem voter_filtered_block_tree_cases (E : Env V) (st : Protocol.Store V) (s : Slot)
    {C : Block V} (hC : C ∈ Protocol.voter_filtered_block_tree E st s) :
    C ∈ Protocol.voter_processed_block_tree E st.toHealing.toFG.toSG.toGoldfishStore s ∧
      Block.Preceq st.F C ∧
      (∃ Y ∈ Protocol.voter_processed_block_tree E st.toHealing.toFG.toSG.toGoldfishStore s,
        Block.Preceq C Y ∧ st.h_max - 1 ≤ (st.σ Y).h) ∧
      Block.Preceq (Protocol.get_fg_root st.toHealing.toFG) C := by
  simp only [Protocol.voter_filtered_block_tree, Protocol.get_filtered_block_tree_from] at hC
  obtain ⟨hv, hroot⟩ := Finset.mem_filter.mp hC
  obtain ⟨⟨hCp, hF⟩, Y, hY, hCY, hh⟩ :=
    (Proofs.ModelProperties.mem_viable_tree_iff _ _ _ _ _).mp hv
  exact ⟨hCp, hF, ⟨Y, hY, hCY, hh⟩, hroot⟩

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]


end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Sts
