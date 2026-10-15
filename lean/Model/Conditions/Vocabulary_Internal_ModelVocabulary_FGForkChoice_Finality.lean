import Proofs.Vocabulary.Internal.ModelVocabulary.FGForkChoice.Finality
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Viable tree

The viable tree of a store, over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Protocol
open Protocol (ChainState)

/-- The viable tree of the store `st`, read off its `σ`, `F`, `h_max` and `T`. Named `V_tree`
    because `V` is the validator type. -/
def Vocabulary.Protocol.V_tree (M : Record.Model V) (st : M.FGS) : Finset (Block V) :=
  M.viable_tree st.σ st.F st.h_max st.T

end

section
open DecoupledConsensusModel.Protocol
open Protocol (ChainState)

/-- `DecoupledConsensusModel.Protocol.V_tree` equals `Restated.Vocabulary.Protocol.V_tree` at the
    model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.V_tree_vocabulary_eq (st : FGStore V) :
    _root_.DecoupledConsensusModel.Protocol.V_tree (V := V) st = Restated.Vocabulary.Protocol.V_tree (V := V) Record.Model.vocabulary st :=
  rfl

end

end DecoupledConsensusModel.Sts.Restated
