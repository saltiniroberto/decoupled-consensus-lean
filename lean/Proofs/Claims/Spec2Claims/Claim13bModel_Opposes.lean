module

public import Model.Vocabulary.Protocol.Grades
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.Opposes`

The proposition that a sender's tokens oppose a block: a late token of a round at least every early
token's does not cover the block, or two raw tokens of such a round carry different keys.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.Opposes

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {Key Blk : Type*}

/-- If the late token `x` has a round at least every early token's and its key does not cover `B`,
    then the tokens oppose `B`. -/
theorem opposes_of_late {covers : Key → Blk → Prop} {early late raw : Finset (Protocol.Token Key)}
    {B : Blk} (x : Protocol.Token Key) (hx : x ∈ late) (hmax : ∀ u ∈ early, u.round ≤ x.round)
    (hnot : ¬ covers x.key B) :
    Protocol.Opposes covers early late raw B := by
  unfold Protocol.Opposes
  exact Or.inl ⟨x, hx, hmax, hnot⟩

/-- If the raw tokens `x` and `y` have the same round, at least every early token's, and different
    keys, then the tokens oppose `B`. -/
theorem opposes_of_raw {covers : Key → Blk → Prop} {early late raw : Finset (Protocol.Token Key)}
    {B : Blk} (x : Protocol.Token Key) (hx : x ∈ raw) (y : Protocol.Token Key) (hy : y ∈ raw)
    (hmax : ∀ u ∈ early, u.round ≤ x.round) (hxy : x.round = y.round) (hne : x.key ≠ y.key) :
    Protocol.Opposes covers early late raw B := by
  unfold Protocol.Opposes
  exact Or.inr ⟨x, hx, y, hy, hmax, hxy, hne⟩

/-- If the tokens oppose `B`, then either some late token of a round at least every early token's
    does not cover `B`, or two raw tokens of one such round carry different keys. -/
theorem opposes_cases {covers : Key → Blk → Prop} {early late raw : Finset (Protocol.Token Key)}
    {B : Blk} (h : Protocol.Opposes covers early late raw B) :
    (∃ x ∈ late, (∀ u ∈ early, u.round ≤ x.round) ∧ ¬ covers x.key B) ∨
      ∃ x ∈ raw, ∃ y ∈ raw, (∀ u ∈ early, u.round ≤ x.round) ∧
        x.round = y.round ∧ x.key ≠ y.key := by
  unfold Protocol.Opposes at h
  exact h

end DecoupledConsensusModel.Sts
