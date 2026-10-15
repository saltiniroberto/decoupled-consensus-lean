import Proofs.Vocabulary.Protocol.ChainState.NjGap
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# The `nj` invariant

The condition on a chain state's nonjustifiability flag, over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NjGap
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Internal
open Execution

/-- The chain state's flag `σ.nj` is the nonjustifiability formula at its height `σ.h`, evaluated at
    some finalized height `h_F' ≤ σ.h_F`. -/
def Vocabulary.Proofs.NjGap.NjEntry (M : Record.Model V) (cfg : HeightConfig) (σ : M.CS) : Prop :=
  ∃ h_F' : Height, h_F' ≤ σ.h_F ∧ σ.nj = M.nonjustifiable cfg σ.h h_F'

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NjGap
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Internal
open Execution

/-- `DecoupledConsensusModel.Proofs.NjGap.NjEntry` holds exactly when
    `Restated.Vocabulary.Proofs.NjGap.NjEntry` holds at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Proofs.NjGap.NjEntry_vocabulary_eq (cfg : HeightConfig) (σ : ChainState V) :
    _root_.DecoupledConsensusModel.Proofs.NjGap.NjEntry (V := V) cfg σ ↔ Restated.Vocabulary.Proofs.NjGap.NjEntry (V := V) Record.Model.vocabulary cfg σ :=
  Iff.rfl

end

end DecoupledConsensusModel.Sts.Restated
