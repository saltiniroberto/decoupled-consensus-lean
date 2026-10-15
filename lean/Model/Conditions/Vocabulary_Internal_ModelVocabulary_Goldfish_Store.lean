import Proofs.Vocabulary.Internal.ModelVocabulary.Goldfish.Store
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Parent-closed Goldfish tree

The parent-closure condition for the processed tree of a Goldfish store, over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.GoldfishStore

/-- The tree of `st` contains genesis, and every block in it that has a parent has its parent in it. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.GS.parent_closed {M : Record.Model V} (st : M.GS) : Prop :=
  Block.genesis ∈ st.T ∧ ∀ B ∈ st.T, B.parent? = none ∨ B.parent ∈ st.T

end

end DecoupledConsensusModel.Sts.Restated
