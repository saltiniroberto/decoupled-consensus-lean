import Proofs.Vocabulary.Protocol.Handlers.NumericStore
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Bounded heights of a named store

The condition that every body of a named store derives a chain-state height at most the store's
`h_max`, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedNumericStore
open Execution Protocol

/-- Every body `B` of the named store `st` has a derived chain-state height at most `st.core.h_max`. -/
def Vocabulary.Proofs.NamedNumericStore.HeightsBounded (M : Record.Model V) (S : Setup V) (st : M.NS) : Prop :=
  ∀ B ∈ st.bodies, (M.derive_named S.E S.cfg B).h ≤ st.core.h_max

end

end DecoupledConsensusModel.Sts.Restated
