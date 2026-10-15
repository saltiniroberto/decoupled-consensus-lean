import Proofs.Vocabulary.Internal.Definitions.Evidence
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# The derived state of a block

The chain state derived from a block's chain, stated over a model `M : Record.Model V`, and its
counterpart at `Record.Model.vocabulary`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Internal
open Protocol

/-- The chain state `σ[B]` derived from the block chain of `B`. -/
def Vocabulary.Internal.derived_state (M : Record.Model V) (E : Env V) (cfg : HeightConfig) : Block V → M.CS
  | .genesis => M.cs_initial
  | B@(.node p _ _ _ _ _ _) =>
      M.state_transition E cfg (derived_state M E cfg p) B

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Internal
open Protocol

/-- At `Record.Model.vocabulary`, the restated `derived_state` is
    `DecoupledConsensusModel.Internal.derived_state`. -/
@[record_vocabulary]
theorem Vocabulary.Internal.derived_state_vocabulary_eq (E : Env V) (cfg : HeightConfig) :
    _root_.DecoupledConsensusModel.Internal.derived_state (V := V) E cfg = Restated.Vocabulary.Internal.derived_state (V := V) Record.Model.vocabulary E cfg := by
  funext B
  induction B with
  | genesis => rfl
  | node p _ _ _ _ _ _ ih =>
    rw [_root_.DecoupledConsensusModel.Internal.derived_state,
      Restated.Vocabulary.Internal.derived_state, ih]
    rfl

end

end DecoupledConsensusModel.Sts.Restated
