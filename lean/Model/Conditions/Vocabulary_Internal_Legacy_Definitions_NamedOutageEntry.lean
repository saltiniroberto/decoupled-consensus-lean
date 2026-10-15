import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedOutageEntry
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Legacy_Assumptions_Weight
import Model.Record.Wiring

/-!
# Slashable weight bound of a run

The bound on slashable weight of a run read along a path, over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.NamedOutageEntry
open Execution DecoupledConsensusModel.Protocol

/-- The run `rho`, read along the path `W`, satisfies `Restated.Vocabulary.Execution.SlashableBound`. -/
abbrev Vocabulary.Internal.NamedOutageEntry.SlashableBound (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) : Prop :=
  Restated.Vocabulary.Execution.SlashableBound M S rho W

end

end DecoupledConsensusModel.Sts.Restated
