import Proofs.Vocabulary.Protocol.ChainState.W4NamedJustificationMonotone
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Record.Wiring

/-!
# Named justification is monotone along ancestry

A theorem over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: the justified
height derived for a named block is at most the one derived for each of its descendants.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol Internal Execution

/-- If `A` is an ancestor of `B`, the justified height derived for `A` is at most the one derived
    for `B`. -/
theorem Vocabulary.Proofs.HealingSurface.namedJustification_le_of_preceq (facts : Record.Facts M)
    (E : Env V) (cfg : HeightConfig) {A B : NamedBlock V}
    (hAB : NamedBlock.Preceq A B) :
    (M.derive_named E cfg A).h_j ≤ (M.derive_named E cfg B).h_j := by
  rcases facts.csAdded.namedJustification_strict_or_eq_of_preceq E cfg hAB with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

end

end DecoupledConsensusModel.Sts.Restated
