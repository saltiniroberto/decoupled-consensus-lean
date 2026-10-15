import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.NamedBlocks
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `NamedBlock.compatible`

The lemmas that unfold `NamedBlock.compatible`: two named blocks are compatible when one is an
ancestor of the other.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.NamedBlock.Preceq

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If one of the named blocks `A` and `B` is an ancestor of the other, then
    `NamedBlock.compatible A B` is `true`. -/
theorem namedBlock_compatible_of_cases {A B : NamedBlock V}
    (h : NamedBlock.Preceq A B ∨ NamedBlock.Preceq B A) : NamedBlock.compatible A B = true := by
  simp only [NamedBlock.compatible, Bool.or_eq_true]
  exact h

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If the named blocks `A` and `B` are compatible, then one of them is an ancestor of the other. -/
theorem namedBlock_compatible_cases {A B : NamedBlock V}
    (h : NamedBlock.compatible A B = true) :
    NamedBlock.Preceq A B ∨ NamedBlock.Preceq B A := by
  simp only [NamedBlock.compatible, Bool.or_eq_true] at h
  exact h

end DecoupledConsensusModel.Sts
