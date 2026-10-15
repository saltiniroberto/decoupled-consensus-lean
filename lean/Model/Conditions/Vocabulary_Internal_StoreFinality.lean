import Proofs.Vocabulary.Internal.StoreFinality
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Justification height less than the maximum

The condition that a store's justification height is less than its maximum chain-state height, over
a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Internal
open Protocol (HeightConfig)

/-- The store's justification height `st.h_j` is less than its maximum chain-state height
    `st.h_max`. -/
def Vocabulary.Internal.JustificationBelowMax (M : Record.Model V) (st : M.S) : Prop :=
  st.h_j < st.h_max

end

end DecoupledConsensusModel.Sts.Restated
