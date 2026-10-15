import Proofs.Vocabulary.Protocol.Handlers.CommitteePools
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedExecutionQueries
import Model.Record.Wiring

/-!
# Committee pools of a world

The committee-pool condition on a world of node states, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.CommitteePools

/-- The committee-pool condition `NamedWorldCommitteePools` on the world `w`. -/
abbrev Vocabulary.Protocol.CommitteePools.WorldCommitteePools (M : Record.Model V) (S : Execution.Setup V)
    (w : (V → M.N)) : Prop :=
  Restated.Vocabulary.Execution.NamedWorldCommitteePools M S w

end

end DecoupledConsensusModel.Sts.Restated
