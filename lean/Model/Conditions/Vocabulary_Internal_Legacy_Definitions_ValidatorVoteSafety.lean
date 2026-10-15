import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Record.Wiring

/-!
# Authenticity of included attestations

The condition that an attestation of an honest validator included in a processed block was sent by
that validator, over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Internal
open Execution

/-- Along the path `W` of `rho`, an attestation of an honest validator included in a block some
    validator processes at `t` was sent by that validator's tick at some `t' ≤ t`. -/
structure Vocabulary.Internal.AttestationAuthenticity (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) : Prop where
  carriedAttest : ∀ v B t, Restated.Vocabulary.Execution.NamedRun.processes M S rho W v (.block B) t →
    ∀ a ∈ B.attestations, a.val_index ∈ rho.honest →
      ∃ t', t' ≤ t ∧
        Restated.Vocabulary.Execution.NamedRun.emitsAlong M S rho W a.val_index (.attest a) t'

end

end DecoupledConsensusModel.Sts.Restated
