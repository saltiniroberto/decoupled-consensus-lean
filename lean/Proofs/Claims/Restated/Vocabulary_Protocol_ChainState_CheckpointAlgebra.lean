import Proofs.Vocabulary.Protocol.ChainState.CheckpointAlgebra
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Vocabulary.Protocol.ChainState.Chain
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Vocabulary.Protocol.ChainState.DerivationGeometry
import Model.Record.Wiring

/-!
# Named justifications

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: a positive
justified height of a named block's chain state is the height of a named ancestor that erases to the
justified block and is its own height entry.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedCheckpointAlgebra
open Protocol
open Internal
open Execution
open Internal.HealingSurface

/-- If the chain state derived from `B` has a positive justified height `h_j`, some named ancestor
    `J` of `B` erases to that state's justified block, has height `h_j`, has its own erasure as its
    height entry `T_h`, and has `nj = false`. -/
theorem Vocabulary.Proofs.NamedCheckpointAlgebra.namedJustification_ancestor_data (facts : Record.Facts M)
    (E : Env V) (cfg : HeightConfig) (B : NamedBlock V)
    (hpos : 0 < (M.derive_named E cfg B).h_j) :
    ∃ J : NamedBlock V, NamedBlock.Preceq J B ∧
      J.erase = (M.derive_named E cfg B).J ∧
      (M.derive_named E cfg J).h = (M.derive_named E cfg B).h_j ∧
      (M.derive_named E cfg J).T_h = J.erase ∧
      (M.derive_named E cfg J).nj = false := by
  exact facts.csAdded.namedJustification_ancestor_data E cfg B hpos

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedCheckpointAlgebra
open Protocol
open Internal
open Execution
open Internal.HealingSurface

/-- If the chain state derived from `B` has a positive justified height `h_j`, some named ancestor
    `J` of `B` erases to that state's justified block, has height `h_j`, and has its own erasure as
    its height entry `T_h`. -/
theorem Vocabulary.Proofs.NamedCheckpointAlgebra.namedJustification_selfTarget (facts : Record.Facts M)
    (E : Env V) (cfg : HeightConfig) (B : NamedBlock V)
    (hpos : 0 < (M.derive_named E cfg B).h_j) :
    ∃ J : NamedBlock V, NamedBlock.Preceq J B ∧
      J.erase = (M.derive_named E cfg B).J ∧
      (M.derive_named E cfg J).h = (M.derive_named E cfg B).h_j ∧
      (M.derive_named E cfg J).T_h = J.erase := by
  obtain ⟨J, hJ, hErase, hHeight, hTarget, _⟩ :=
    Restated.Vocabulary.Proofs.NamedCheckpointAlgebra.namedJustification_ancestor_data facts E cfg B hpos
  exact ⟨J, hJ, hErase, hHeight, hTarget⟩

end

end DecoupledConsensusModel.Sts.Restated
