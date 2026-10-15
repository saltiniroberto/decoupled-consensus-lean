import Proofs.Vocabulary.Internal.Invariants
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Goldfish_Store
import Model.Record.Wiring

/-!
# Parent-closed processed tree

The condition that the processed block tree of a store is parent closed, over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Internal
open Protocol (HeightConfig)

/-- The processed block tree of the store `st` is parent closed. -/
def Vocabulary.Internal.ParentClosed (M : Record.Model V) (st : M.S) : Prop :=
  Record.Model.GS.parent_closed (M.toHealing st).toFG.toSG.toGoldfishStore

end

end DecoupledConsensusModel.Sts.Restated
