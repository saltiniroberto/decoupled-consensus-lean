import Model.Vocabulary.Objects.NamedBlocks
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `NamedHeightPair.matchesEntry`

Lemmas that unfold the test that a height pair is a vote bound to a given height and entry block.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.NamedHeightPair.matchesEntry

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

/-- If the height pair `p` matches the height `h` and the entry root `entry`, then `p` is a vote for
    height `h` bound to `entry`, with some timeout flag. -/
theorem vote_of_matchesEntry {p : NamedHeightPair} {h : Height} {entry : BlockId}
    (hm : p.matchesEntry h entry = true) :
    ∃ tmo : Bool, p = NamedHeightPair.vote h entry tmo := by
  cases p with
  | empty => simp [NamedHeightPair.matchesEntry] at hm
  | vote h' entry' tmo =>
      simp only [NamedHeightPair.matchesEntry, decide_eq_true_eq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact ⟨tmo, rfl⟩

/-- The vote pair at height `h'` for the entry `entry'`, with any timeout flag, matches the height
    `h` and the entry `entry` exactly when `h' = h` and `entry' = entry`. -/
theorem matchesEntry_vote_iff {h' h : Height} {entry' entry : BlockId} {tmo : Bool} :
    (NamedHeightPair.vote h' entry' tmo).matchesEntry h entry = true ↔ h' = h ∧ entry' = entry := by
  simp only [NamedHeightPair.matchesEntry, decide_eq_true_eq]

end DecoupledConsensusModel.Sts
