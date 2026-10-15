import Proofs.Vocabulary.Execution.EmissionShape
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_OutageInputs
import Model.Conditions.Vocabulary_Internal_Definitions_NamedOutageEntry
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The shape of an emitted attestation

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`, along a path `W`
of a run: an attestation a validator emits is its own, emitted at the action time of its round, by a
tick at which the validator passes the grade-2 awake test.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open Internal Execution Internal.NamedOutageEntry

/-- For every path `W` of `rho`, if `v` emits the attestation `a` at `t` along `W`, then `a` is
    `v`'s and `t` is the action time of `a`'s round. -/
theorem Vocabulary.Proofs.Optimistic.emits_attest_shape (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} {v : V}
    {a : NamedAttestation V} {t : Time}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (h : Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (NamedObject.attest a) t) :
    a.val_index = v ∧ t = (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
  obtain ⟨_, _, _, _, _, _, _, hval, ht, _⟩ :=
    Restated.Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_stages facts S rho W hW h
  exact ⟨hval, ht⟩

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open Internal Execution Internal.NamedOutageEntry

/-- For every path `W` of `rho`, if `v` emits the attestation `a` at `t` along `W`, then some event
    `i` of `rho` is `v`'s tick at `t`, and `v`'s node state in `W i` passes the grade-2 awake test
    `M.awake_for_grade2` of `a`'s round. -/
theorem Vocabulary.Proofs.Optimistic.emits_attest_awake (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} {v : V}
    {a : NamedAttestation V} {t : Time}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (h : Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (NamedObject.attest a) t) :
    ∃ i : Nat, rho.events[i]? = some (.tick v t) ∧ M.awake_for_grade2 S v (W i v) a.round := by
  obtain ⟨i, hi, _, _, _, _, _, _, _, hawake⟩ :=
    Restated.Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_stages facts S rho W hW h
  exact ⟨i, hi, hawake⟩

end

end DecoupledConsensusModel.Sts.Restated
