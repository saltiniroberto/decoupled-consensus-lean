import Proofs.Vocabulary.Protocol.Handlers.StoreBridge
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Rounds of SG rows

The condition that every SG row a named store holds in bucket `r` names round `r`, stated over a
model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedStoreBridge
open Internal
open Execution

/-- Every SG row the store holds in bucket `r` names round `r`. -/
def Vocabulary.Proofs.NamedStoreBridge.SgRowRounds (M : Record.Model V) (st : M.NS) : Prop :=
  ∀ r : Round, ∀ row ∈ st.sg_rows r, row.round = r

end

end DecoupledConsensusModel.Sts.Restated
