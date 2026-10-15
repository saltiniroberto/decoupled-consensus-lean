import Proofs.Vocabulary.Protocol.ValidatorClient.HeightPairCases
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# The source selected by a round action

The set of FG sources a round action can select under a grade contract, stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (ChainState HeightConfig)
open Protocol (Record height_pair own_lock)

/-- The sources a round action can select under `contract`: the outcomes of `M.fg_source_with` for
    `st`'s round, taken with an outcome of `M.grade2_block_with` as its candidate. -/
def Vocabulary.Proofs.HealingSurface.actionSource (M : Record.Model V) (contract : M.Contract) (E : Env V)
    (hc : Protocol.HealConfig) (st : M.HS) : DC.NDRE (Option (Block V)) := do
  let g ← M.grade2_block_with contract E hc st ((M.round_of hc st.s))
  M.fg_source_with contract E hc st ((M.round_of hc st.s)) g

end

end DecoupledConsensusModel.Sts.Restated
