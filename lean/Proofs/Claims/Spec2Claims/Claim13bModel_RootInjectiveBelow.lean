module
public import Model.Vocabulary.Execution.Setup
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `RootInjectiveBelow` and `RootInjectiveOnAncestors`

How to establish and how to use the two root-injectivity predicates.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Execution.RootInjectiveBelow
  DecoupledConsensusModel.Execution.RootInjectiveOnAncestors

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V]

/-- `RootInjectiveBelow Tr` holds when any two blocks with equal roots, each an ancestor of some
    block of `Tr`, are equal. -/
theorem rootInjectiveBelow_intro {Tr : Finset (Block V)}
    (h : ∀ (A C B₁ B₂ : Block V), B₁ ∈ Tr → Block.Preceq A B₁ → B₂ ∈ Tr → Block.Preceq C B₂ →
      A.root = C.root → A = C) :
    RootInjectiveBelow Tr := by
  rintro A C ⟨B₁, hB₁, hAB₁⟩ ⟨B₂, hB₂, hCB₂⟩ hAC
  exact h A C B₁ B₂ hB₁ hAB₁ hB₂ hCB₂ hAC

/-- Under `RootInjectiveOnAncestors tip₁ tip₂`, blocks `A ⪯ tip₁` and `C ⪯ tip₂` with equal roots
    are equal. -/
theorem RootInjectiveOnAncestors.eq_of_root_eq {tip₁ tip₂ A C : Block V}
    (h : RootInjectiveOnAncestors tip₁ tip₂) (hA : Block.Preceq A tip₁)
    (hC : Block.Preceq C tip₂) (hAC : A.root = C.root) : A = C :=
  h A C ⟨tip₁, by simp, hA⟩ ⟨tip₂, by simp, hC⟩ hAC

/-- Under `RootInjectiveBelow Tr`, two blocks with equal roots, each an ancestor of some block of
    `Tr`, are equal. -/
theorem RootInjectiveBelow.eq_of_root_eq {Tr : Finset (Block V)} (h : RootInjectiveBelow Tr)
    {A C B₁ B₂ : Block V} (hB₁ : B₁ ∈ Tr) (hA : Block.Preceq A B₁) (hB₂ : B₂ ∈ Tr)
    (hC : Block.Preceq C B₂) (hAC : A.root = C.root) : A = C :=
  h A C ⟨B₁, hB₁, hA⟩ ⟨B₂, hB₂, hC⟩ hAC

/-- `RootInjectiveOnAncestors tip₁ tip₂` holds when any two blocks with equal roots, each an
    ancestor of `tip₁` or `tip₂`, are equal. -/
theorem rootInjectiveOnAncestors_intro {tip₁ tip₂ : Block V}
    (h : ∀ (A C B₁ B₂ : Block V), B₁ ∈ ({tip₁, tip₂} : Finset (Block V)) →
      Block.Preceq A B₁ → B₂ ∈ ({tip₁, tip₂} : Finset (Block V)) → Block.Preceq C B₂ →
      A.root = C.root → A = C) :
    RootInjectiveOnAncestors tip₁ tip₂ := by
  unfold RootInjectiveOnAncestors
  exact rootInjectiveBelow_intro h

end DecoupledConsensusModel.Sts
