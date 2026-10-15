import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_HjMono

/-!
# Monotonicity of the justified height

The justified height along a chain, stated over a model `M : Record.Model V` and its facts
`facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (HeightConfig derive_named)

/-- If the named block `A` is an ancestor of the named block `B`, then `h_j(A) ≤ h_j(B)`, both read
    on `derive_named S.E S.cfg`. -/
theorem h_j_mono_chain (facts : Record.Facts M) (S : Setup V) {A B : NamedBlock V} (hAB : NamedBlock.Preceq A B) :
    (M.derive_named S.E S.cfg A).h_j ≤ (M.derive_named S.E S.cfg B).h_j :=
  facts.csAdded.derive_named_h_j_mono S.E S.cfg hAB

end

end DecoupledConsensusModel.Sts.Restated
