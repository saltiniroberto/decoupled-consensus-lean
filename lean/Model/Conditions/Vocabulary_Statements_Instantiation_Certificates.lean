import Model.Vocabulary.Statements.Instantiation.Certificates
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Finalization recorded by a named block

The condition that a named block's derived chain state finalizes a given block at a given height,
stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Statements
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel DecoupledConsensusModel.Protocol

/-- The derived chain state of the named block `C` has finalized block `T` and finalized height `h`. -/
def Vocabulary.Statements.Instantiation.NamedFinalizedAt (M : Record.Model V) (E : Env V) (cfg : HeightConfig) (C : NamedBlock V) (T : Block V)
    (h : Height) : Prop :=
  (M.derive_named E cfg C).F = T ∧ (M.derive_named E cfg C).h_F = h

end

end DecoupledConsensusModel.Sts.Restated
