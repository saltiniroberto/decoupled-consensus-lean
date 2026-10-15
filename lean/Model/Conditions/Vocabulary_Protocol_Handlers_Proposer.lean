import Proofs.Vocabulary.Protocol.Handlers.Proposer
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Proposer check on stored blocks

The condition that every non-genesis block a store holds was proposed by its slot's proposer, stated
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
open Protocol (Record)
open Internal
open Execution

/-- Every block of `st.T` is the genesis block or has the proposer of its slot as its proposer. -/
def Vocabulary.Proofs.HealingSurface.ProposerOk (M : Record.Model V) (E : Env V) (st : M.S) : Prop :=
  ∀ B ∈ st.T, B = Block.genesis ∨ B.proposer? = some (E.proposer B.slot)

end

end DecoupledConsensusModel.Sts.Restated
