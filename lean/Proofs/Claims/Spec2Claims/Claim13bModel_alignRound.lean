import Model.Vocabulary.Protocol.Grades
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.alignRound`

What aligning a grade cache to a round does to the frame it holds for each round.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.alignRound
  DecoupledConsensusModel.Protocol.cacheAtRound

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
/-- After `Protocol.alignRound`, the frame the cache holds for a round is the one it held before or
    the pending frame. -/
theorem cacheAtRound_alignRound (c : Protocol.Cache V) (r₀ r₁ : Round) :
    Protocol.cacheAtRound (Protocol.alignRound c r₀) r₁ = Protocol.cacheAtRound c r₁ ∨
      Protocol.cacheAtRound (Protocol.alignRound c r₀) r₁ = Protocol.pendingFrame := by
  unfold Protocol.alignRound
  by_cases h1 : r₀ = c.round
  · rw [if_pos h1]; exact Or.inl rfl
  · rw [if_neg h1]
    by_cases h2 : r₀ = c.round + 1
    · rw [if_pos h2]
      by_cases h3 : r₁ = r₀
      · left
        have hne : r₁ ≠ c.round := by rw [h3, h2]; exact Nat.succ_ne_self _
        simp only [Protocol.cacheAtRound, if_pos h3, if_neg hne, if_pos (h3.trans h2)]
      · right
        simp only [Protocol.cacheAtRound, if_neg h3]
        split_ifs <;> rfl
    · rw [if_neg h2]
      right
      simp only [Protocol.cacheAtRound]
      split_ifs <;> rfl

end DecoupledConsensusModel.Sts
