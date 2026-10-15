import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Vocabulary.Protocol.Handlers.Invariants2
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Event
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Record.Wiring

/-!
# The justified height never decreases

The justified height `h_j` of a validator's store never decreases along a run, stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface (ReleasedThrough HonestStoresCrossedAt
  PermanentlyCrossedFrom UnreleasedCertificateStaleFrom)

/-- For `m ≤ n`, every world `w₁` before the `m`-th event of `rho` and every world `w₂` the events
    `m` to `n - 1` lead to from `w₁`, the justified height of `v`'s store in `w₁` is at most that of
    `v`'s store in `w₂`. -/
theorem Vocabulary.Proofs.HealingSurface.stateBefore_h_j_mono (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) {m n : Nat} (hmn : m ≤ n) :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho m,
    ∀ w₂ ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) w₁,
      (w₁ v).st.core.h_j ≤ (w₂ v).st.core.h_j :=
  facts.hdRun.stateBefore_h_j_mono S rho v hmn

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface (ReleasedThrough HonestStoresCrossedAt
  PermanentlyCrossedFrom UnreleasedCertificateStaleFrom)

end

end DecoupledConsensusModel.Sts.Restated
