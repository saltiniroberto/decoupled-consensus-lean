import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Record.Wiring

/-!
# The attestation of the action duty

The attestations `actionAttestationFrom` a validator's action duty can compute from a node state,
stated over a model `M : Record.Model V`.
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

/-- The attestations `a` such that, for some node state `n` of the round-`r` action read from
    `before`, the attestation duty on `n` can return `a`. -/
def actionAttestationFrom (M : Record.Model V) (S : Setup V) (before : M.N) (v : V) (r : Round) :
    DC.NDR (NamedAttestation V) :=
  { a | ∃ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
    ∃ (ns : M.NS) (rec : M.NR), M.duties_attest_with (M.gradeContract n.cache)
      S.E S.hc (S.node v) n.st n.record ⇢ (ns, rec, a) }

end

end DecoupledConsensusModel.Sts.Restated
