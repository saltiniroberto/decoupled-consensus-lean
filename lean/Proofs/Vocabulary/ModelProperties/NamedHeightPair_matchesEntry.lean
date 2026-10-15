module
public import Model.Vocabulary.Objects.NamedBlocks

@[expose] public section

/-!
# Facts about `NamedHeightPair.matchesEntry`

Whether a height pair matches a height and an entry root.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

/-- The vote pair at height `h'` for `entry'`, with any timeout flag, matches `h` and `entry`
    exactly when `h' = h` and `entry' = entry`. -/
theorem matchesEntry_vote_iff {h' h : Height} {entry' entry : BlockId} {tmo : Bool} :
    (NamedHeightPair.vote h' entry' tmo).matchesEntry h entry = true ↔
      h' = h ∧ entry' = entry := by
  simp only [NamedHeightPair.matchesEntry, decide_eq_true_eq]

end DecoupledConsensusModel.Proofs.ModelProperties

end
