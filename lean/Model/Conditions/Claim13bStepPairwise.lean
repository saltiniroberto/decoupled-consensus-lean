import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bStepPairwise

/-!
# Pairwise compatibility of the SG walks' candidates

The condition `SGCandidate` on the blocks an SG walk could return, and the condition `GradePairwise`
on two stores, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `B` is an ancestor of the store's confirmed block, or a graded block of the grade read `grades`. -/
def SGCandidate (M : Record.Model V) (stH : M.HS) (grades : Protocol.GradeRead V) (B : Block V) :
    Prop :=
  Block.Preceq B stH.live_confirmed ∨ SGGraded grades B

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Any two blocks that satisfy `SGCandidate` at the two stores, at least one of them a graded block
    of its own store's grade read, lie on one chain. -/
def GradePairwise (M : Record.Model V) (stH₁ stH₂ : M.HS)
    (grades₁ grades₂ : Protocol.GradeRead V) : Prop :=
  ∀ B₁ B₂ : Block V, Restated.SGCandidate M stH₁ grades₁ B₁ → Restated.SGCandidate M stH₂ grades₂ B₂ →
    (SGGraded grades₁ B₁ ∨ SGGraded grades₂ B₂) → Block.compatible B₁ B₂ = true

end

end DecoupledConsensusModel.Sts.Restated
