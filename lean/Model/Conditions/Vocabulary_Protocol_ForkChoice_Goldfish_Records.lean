import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Records
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Lock compatibility

The condition that a signing record's locks are compatible with its timeouts and targets, over a
model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Records
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Internal

/-- For every height `h`, a lock of `Λ` on `T` at `h` comes with no timeout at `h` and a target at
    `h` that is empty or `T`. -/
def Vocabulary.Proofs.Records.LockCompatible (M : Record.Model V) (Λ : M.R) : Prop :=
  ∀ (h : Height) (T : BlockId), Λ.lock h = some T →
    Λ.timeout h = false ∧ (Λ.target h = none ∨ Λ.target h = some T)

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Records
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Internal

/-- `DecoupledConsensusModel.Proofs.Records.LockCompatible` holds exactly when
    `Restated.Vocabulary.Proofs.Records.LockCompatible` holds at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.Records.LockCompatible_vocabulary_eq (Λ : Record) :
    _root_.DecoupledConsensusModel.Proofs.Records.LockCompatible Λ ↔ Restated.Vocabulary.Proofs.Records.LockCompatible (V := V) Record.Model.vocabulary Λ :=
  Iff.rfl

end

end DecoupledConsensusModel.Sts.Restated
