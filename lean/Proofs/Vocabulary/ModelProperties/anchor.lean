module
public import Model.Vocabulary.Protocol.Grades

@[expose] public section

/-!
# Facts about `Protocol.anchor`

The round's anchor read from a grade-1 result.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The anchor read from `g1` is the store's FG root, or the active prefix, in the store's filtered
    tree, of a root `g1` holds. -/
theorem anchor_cases (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (r : Round) (g1 : Option (Option (Block V))) :
    DecoupledConsensusModel.Protocol.anchor E hc st r g1 = Protocol.get_fg_root st.toFG ∨
      ∃ root A, g1 = some (some root) ∧
        DecoupledConsensusModel.Protocol.activePrefix
          (Protocol.get_filtered_block_tree st.toFG) root = some A ∧
        DecoupledConsensusModel.Protocol.anchor E hc st r g1 = A := by
  rcases g1 with _ | _ | root
  · exact Or.inl rfl
  · exact Or.inl rfl
  · cases hactive : DecoupledConsensusModel.Protocol.activePrefix
        (Protocol.get_filtered_block_tree st.toFG) root with
    | none =>
      exact Or.inl (by simp only [DecoupledConsensusModel.Protocol.anchor, hactive,
        Option.getD_none])
    | some A =>
      exact Or.inr ⟨root, A, rfl, hactive, by
        simp only [DecoupledConsensusModel.Protocol.anchor, hactive, Option.getD_some]⟩

/-- Two stores with the same filtered tree and the same FG root give the same anchor from the same
    grade-1 result. -/
theorem anchor_eq_of_filtered_fg_root (E : Env V) (hc : Protocol.HealConfig)
    {st st' : Protocol.HealingStore V} (r : Round) (g1 : Option (Option (Block V)))
    (htree : Protocol.get_filtered_block_tree st.toFG =
      Protocol.get_filtered_block_tree st'.toFG)
    (hroot : Protocol.get_fg_root st.toFG = Protocol.get_fg_root st'.toFG) :
    DecoupledConsensusModel.Protocol.anchor E hc st r g1 =
      DecoupledConsensusModel.Protocol.anchor E hc st' r g1 := by
  unfold DecoupledConsensusModel.Protocol.anchor
  rw [htree, hroot]

end DecoupledConsensusModel.Proofs.ModelProperties

end
