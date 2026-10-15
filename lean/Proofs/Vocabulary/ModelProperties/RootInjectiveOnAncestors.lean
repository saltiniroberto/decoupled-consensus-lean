module
public import Model.Vocabulary.Execution.Setup

@[expose] public section

/-!
# Facts about `Execution.RootInjectiveOnAncestors`

Roots identifying blocks on the ancestors of two tips.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V]

/-- Under `RootInjectiveOnAncestors tip₁ tip₂`, a block `A ⪯ tip₁` and a block `C ⪯ tip₂` with equal
    roots are equal. -/
theorem RootInjectiveOnAncestors.eq_of_root_eq {tip₁ tip₂ A C : Block V}
    (h : RootInjectiveOnAncestors tip₁ tip₂) (hA : Block.Preceq A tip₁)
    (hC : Block.Preceq C tip₂) (hAC : A.root = C.root) : A = C :=
  h A C ⟨tip₁, by simp, hA⟩ ⟨tip₂, by simp, hC⟩ hAC

/-- `RootInjectiveOnAncestors tip₁ tip₂` follows from root injectivity among the ancestors of each
    tip and between the ancestors of the two, in both directions. -/
theorem RootInjectiveOnAncestors.of_four {tip₁ tip₂ : Block V}
    (h₁₁ : ∀ A C : Block V, Block.Preceq A tip₁ → Block.Preceq C tip₁ → A.root = C.root → A = C)
    (h₁₂ : ∀ A C : Block V, Block.Preceq A tip₁ → Block.Preceq C tip₂ → A.root = C.root → A = C)
    (h₂₁ : ∀ A C : Block V, Block.Preceq A tip₂ → Block.Preceq C tip₁ → A.root = C.root → A = C)
    (h₂₂ : ∀ A C : Block V, Block.Preceq A tip₂ → Block.Preceq C tip₂ → A.root = C.root → A = C) :
    RootInjectiveOnAncestors tip₁ tip₂ := by
  intro A C ⟨Z, hZ, hAZ⟩ ⟨W, hW, hCW⟩ hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hZ hW
  rcases hZ with rfl | rfl <;> rcases hW with rfl | rfl
  · exact h₁₁ A C hAZ hCW hr
  · exact h₁₂ A C hAZ hCW hr
  · exact h₂₁ A C hAZ hCW hr
  · exact h₂₂ A C hAZ hCW hr

end DecoupledConsensusModel.Proofs.ModelProperties

end
