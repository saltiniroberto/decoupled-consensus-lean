import Proofs.Vocabulary.Protocol.Grades.CacheProvenance
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_NamedNode
import Model.Conditions.Vocabulary_Protocol_Grades_CacheProvenance
import Model.Record.Wiring

/-!
# The origin of a completed grade-cache result

A completed result in a validator's grade cache has a recorded origin in the run, stated over a
model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedCacheProvenance
open Execution DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol

/-- For every world `w₁` before event `i` of `rho`, if the cache of `v`'s node state in `w₁` has the
    completed result `root` for round `r` and phase `p`, then `root` has the origin
    `Origin M S rho i w₁ v r p root` names, clipped to the finalized block of `v`'s store in `w₁`. -/
theorem Vocabulary.Proofs.NamedCacheProvenance.completed_phase_origin (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V)
    (r : Round) (p : Phase) (root : Option (Block V)) :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    M.phaseResult (M.cacheAtRound (w₁ v).cache r) p = some root →
    Restated.Vocabulary.Proofs.NamedCacheProvenance.Origin M S rho i w₁ v r p root (w₁ v).st.core.F :=
  facts.grRun.completed_phase_origin S rho i v r p root

end

end DecoupledConsensusModel.Sts.Restated
