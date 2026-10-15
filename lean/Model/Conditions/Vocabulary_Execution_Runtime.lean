import Proofs.Vocabulary.Execution.Runtime
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# The node invariant

The invariant of a node state, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedRuntime
open Execution

/-- The store of `n` satisfies the confirmation-membership invariant, its signing record satisfies
    the tick record invariant, and clipping its grade cache at its store's finalized block leaves
    the cache unchanged. -/
def Vocabulary.Proofs.NamedRuntime.NodeInvariant (M : Record.Model V) (S : Setup V) (n : M.N) : Prop :=
  Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg n.st ∧
  Restated.Vocabulary.Proofs.NamedTickRecord.Invariant M n.record ∧ M.clipCache n.st.core.F n.cache = n.cache

end

end DecoupledConsensusModel.Sts.Restated
