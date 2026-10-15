import Proofs.Vocabulary.Protocol.ChainState.AlignedRoundLemmas
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Record.Wiring

/-!
# Honest emission of included attestations, and no self-slashing

Two conditions on a run read along a path, over a model `M : Record.Model V`: the attestations of a
pool attributed to honest validators were emitted by them, and no validator's own emissions are
slashable.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Execution

/-- Every attestation of `A` whose validator is in `H` is the erasure of a named attestation that
    validator emits at some time, read along the path `W` of `ρ`. -/
def Vocabulary.Proofs.AlignedRoundLemmas.CarriedByHonest (M : Record.Model V) (S : Setup V) (ρ : Record.Run V)
    (W : Nat → V → M.N) (H : Finset V)
    (A : Finset (CombinedAttestation V)) : Prop :=
  ∀ a ∈ A, a.val_index ∈ H →
    ∃ (row : NamedAttestation V) (t : Time),
      row.erase = a ∧ (Restated.Vocabulary.Execution.Run.emits M S ρ W a.val_index (Object.attest row) t)

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Execution

/-- For every validator `i` and named attestations `a`, `b` that `i` emits, read along the path `W`
    of `ρ`, the erasures of `a` and `b` are not slashable. -/
def Vocabulary.Proofs.AlignedRoundLemmas.NoSelfSlashing (M : Record.Model V) (S : Setup V) (ρ : Record.Run V)
    (W : Nat → V → M.N) : Prop :=
  ∀ (i : V) (a b : NamedAttestation V),
    (∃ t : Time, (Restated.Vocabulary.Execution.Run.emits M S ρ W i (Object.attest a) t)) →
    (∃ t : Time, (Restated.Vocabulary.Execution.Run.emits M S ρ W i (Object.attest b) t)) →
    M.slashable a.erase b.erase = false

end

end DecoupledConsensusModel.Sts.Restated
