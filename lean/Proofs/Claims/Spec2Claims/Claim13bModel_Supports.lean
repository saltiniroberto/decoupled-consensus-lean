module

public import Model.Vocabulary.Protocol.Grades
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.Supports`

The proposition that a sender's tokens support a block: a latest early token covers the block, the
raw tokens are clean from its round on, and every later late token covers the block.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.Supports

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {Key Blk : Type*}

/-- If the early token `u` has the largest round among the early tokens and covers `B`, the raw
    tokens are clean from `u`'s round on, and every late token of a larger round covers `B`, then
    the tokens support `B`. -/
theorem supports_intro {covers : Key → Blk → Prop} {early late raw : Finset (Protocol.Token Key)}
    {B : Blk} (u : Protocol.Token Key) (hu : u ∈ early) (hmax : ∀ x ∈ early, x.round ≤ u.round)
    (hcov : covers u.key B) (hclean : Protocol.CleanFrom raw u.round)
    (hlater : ∀ x ∈ late, u.round < x.round → covers x.key B) :
    Protocol.Supports covers early late raw B := by
  unfold Protocol.Supports
  exact ⟨u, hu, hmax, hcov, hclean, hlater⟩

/-- If the tokens support `B`, then some early token `u` has the largest round among the early
    tokens and covers `B`, the raw tokens are clean from `u`'s round on, and every late token of a
    larger round covers `B`. -/
theorem supports_elim {covers : Key → Blk → Prop} {early late raw : Finset (Protocol.Token Key)}
    {B : Blk} (h : Protocol.Supports covers early late raw B) :
    ∃ u ∈ early, (∀ x ∈ early, x.round ≤ u.round) ∧ covers u.key B ∧
      Protocol.CleanFrom raw u.round ∧ ∀ x ∈ late, u.round < x.round → covers x.key B := by
  unfold Protocol.Supports at h
  exact h

end DecoupledConsensusModel.Sts
