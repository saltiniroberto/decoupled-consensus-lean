import Proofs.Vocabulary.Protocol.Handlers.HMaxCore
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Tree heights and the maximum height

The condition that every block of a store's tree has a chain-state height at most `st.h_max`, stated
over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

/-- Every block `B` of `st.T` has `(st.σ B).h ≤ st.h_max`. -/
def Vocabulary.Proofs.HealingSurface.TreeHeightsLeHMax (M : Record.Model V) (st : M.S) : Prop :=
  ∀ B ∈ st.T, (st.σ B).h ≤ st.h_max

end

end DecoupledConsensusModel.Sts.Restated
