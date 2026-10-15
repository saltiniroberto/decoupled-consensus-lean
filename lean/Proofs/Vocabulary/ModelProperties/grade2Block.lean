module
public import Proofs.Vocabulary.Protocol.ValidatorClient.Engine

@[expose] public section

/-!
# Facts about `Protocol.grade2Block`

The grade-2 block of a frame.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V]

/-- A grade-2 block the frame gives the store is in the store's filtered tree. -/
theorem mem_filtered_of_grade2Block {st : Protocol.HealingStore V}
    {frame : DecoupledConsensusModel.Protocol.Frame V} {Q : Block V}
    (h : DecoupledConsensusModel.Protocol.grade2Block st frame = some Q) :
    Q ∈ Protocol.get_filtered_block_tree st.toFG := by
  unfold DecoupledConsensusModel.Protocol.grade2Block at h
  by_cases hcl : DecoupledConsensusModel.Protocol.allClosed frame = true
  · rw [if_pos hcl] at h
    obtain ⟨root, -, hact⟩ := Option.bind_eq_some_iff.mp h
    unfold DecoupledConsensusModel.Protocol.activePrefix at hact
    exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hact)).1
  · rw [if_neg hcl] at h
    exact absurd h (by simp)

/-- If the frame gives `st` the grade-2 block `Q`, the frame's grade-2 result is a completed root
    `clipped` and `Q` is an ancestor of `clipped`. -/
theorem grade2Block_some {st : Protocol.HealingStore V}
    {frame : DecoupledConsensusModel.Protocol.Frame V} {Q : Block V}
    (h : DecoupledConsensusModel.Protocol.grade2Block st frame = some Q) :
    ∃ clipped : Block V, frame.g2 = some (some clipped) ∧ Block.Preceq Q clipped := by
  unfold DecoupledConsensusModel.Protocol.grade2Block at h
  by_cases hcl : DecoupledConsensusModel.Protocol.allClosed frame = true
  · rw [if_pos hcl] at h
    obtain ⟨clipped, hclipped, hact⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨inner, hfield, hinner⟩ := Option.bind_eq_some_iff.mp hclipped
    change inner = some clipped at hinner
    subst hinner
    refine ⟨clipped, hfield, ?_⟩
    unfold DecoupledConsensusModel.Protocol.activePrefix at hact
    exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hact)).2
  · rw [if_neg hcl] at h
    exact absurd h (by simp)

end DecoupledConsensusModel.Proofs.ModelProperties

end
